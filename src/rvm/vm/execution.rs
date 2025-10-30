// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use crate::rvm::instructions::Instruction;
use crate::rvm::program::Program;
use crate::value::Value;
use alloc::string::String;
use alloc::vec::Vec;

use super::dispatch::InstructionOutcome;
use super::errors::{Result, VmError};
use super::execution_model::{
    ExecutionFrame, ExecutionMode, ExecutionState, FrameKind, RuleFrameData, RuleFramePhase,
    SuspendReason,
};
use super::machine::RegoVM;

impl RegoVM {
    pub fn execute(&mut self) -> Result<Value> {
        match self.execution_mode {
            ExecutionMode::RunToCompletion => self.execute_run_to_completion(),
            ExecutionMode::Suspendable => self.execute_suspendable(),
        }
    }

    pub fn execute_entry_point_by_index(&mut self, index: usize) -> Result<Value> {
        let entry_points: Vec<(String, usize)> = self
            .program
            .entry_points
            .iter()
            .map(|(name, pc)| (name.clone(), *pc))
            .collect();

        if index >= entry_points.len() {
            return Err(VmError::InvalidEntryPointIndex {
                index,
                max_index: entry_points.len().saturating_sub(1),
            });
        }

        let (_entry_point_name, entry_point_pc) = &entry_points[index];

        if *entry_point_pc >= self.program.instructions.len() {
            return Err(VmError::Internal(alloc::format!(
                "Entry point PC {} >= instruction count {} for index {} | {}",
                entry_point_pc,
                self.program.instructions.len(),
                index,
                self.get_debug_state()
            )));
        }

        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.reset_execution_state();

                if let Err(e) = self.validate_vm_state() {
                    return Err(VmError::Internal(alloc::format!(
                        "VM state validation failed before entry point execution: {} | {}",
                        e,
                        self.get_debug_state()
                    )));
                }

                self.jump_to(*entry_point_pc)
            }
            ExecutionMode::Suspendable => {
                self.reset_execution_state();

                if let Err(e) = self.validate_vm_state() {
                    return Err(VmError::Internal(alloc::format!(
                        "VM state validation failed before entry point execution: {} | {}",
                        e,
                        self.get_debug_state()
                    )));
                }

                self.execute_suspendable_entry(*entry_point_pc)
            }
        }
    }

    pub fn execute_entry_point_by_name(&mut self, name: &str) -> Result<Value> {
        let entry_point_pc =
            self.program
                .get_entry_point(name)
                .ok_or_else(|| VmError::EntryPointNotFound {
                    name: String::from(name),
                    available: self.program.entry_points.keys().cloned().collect(),
                })?;

        if entry_point_pc >= self.program.instructions.len() {
            return Err(VmError::Internal(alloc::format!(
                "Entry point PC {} >= instruction count {} for '{}' | {}",
                entry_point_pc,
                self.program.instructions.len(),
                name,
                self.get_debug_state()
            )));
        }

        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.reset_execution_state();

                if let Err(e) = self.validate_vm_state() {
                    return Err(VmError::Internal(alloc::format!(
                        "VM state validation failed before entry point execution: {} | {}",
                        e,
                        self.get_debug_state()
                    )));
                }

                self.jump_to(entry_point_pc)
            }
            ExecutionMode::Suspendable => {
                self.reset_execution_state();

                if let Err(e) = self.validate_vm_state() {
                    return Err(VmError::Internal(alloc::format!(
                        "VM state validation failed before entry point execution: {} | {}",
                        e,
                        self.get_debug_state()
                    )));
                }

                self.execute_suspendable_entry(entry_point_pc)
            }
        }
    }

    pub(super) fn jump_to(&mut self, target: usize) -> Result<Value> {
        let program = self.program.clone();
        self.pc = target;
        while self.pc < program.instructions.len() {
            if self.executed_instructions >= self.max_instructions {
                return Err(VmError::InstructionLimitExceeded {
                    limit: self.max_instructions,
                });
            }

            self.executed_instructions += 1;
            let instruction = program.instructions[self.pc].clone();

            match self.execute_instruction(&program, instruction)? {
                InstructionOutcome::Continue => {
                    self.pc += 1;
                }
                InstructionOutcome::Return(value) => {
                    return Ok(value);
                }
                InstructionOutcome::Break => {
                    return Ok(self.registers[0].clone());
                }
                InstructionOutcome::Suspend { reason } => {
                    return Err(VmError::Internal(alloc::format!(
                        "Suspend instruction {:?} is not supported in run-to-completion execution",
                        reason
                    )));
                }
            }
        }

        Ok(self.registers[0].clone())
    }

    fn execute_run_to_completion(&mut self) -> Result<Value> {
        self.reset_execution_state();
        self.execution_state = ExecutionState::Running;
        match self.jump_to(0) {
            Ok(value) => {
                self.execution_state = ExecutionState::Completed {
                    result: value.clone(),
                };
                Ok(value)
            }
            Err(err) => {
                self.execution_state = ExecutionState::Error { error: err.clone() };
                Err(err)
            }
        }
    }

    fn execute_suspendable(&mut self) -> Result<Value> {
        self.reset_execution_state();
        self.execution_state = ExecutionState::Running;
        match self.run_stackless_from(0) {
            Ok(result) => Ok(result),
            Err(err) => {
                self.execution_state = ExecutionState::Error { error: err.clone() };
                Err(err)
            }
        }
    }

    fn execute_suspendable_entry(&mut self, entry_point_pc: usize) -> Result<Value> {
        self.execution_state = ExecutionState::Running;
        match self.run_stackless_from(entry_point_pc) {
            Ok(result) => Ok(result),
            Err(err) => {
                self.execution_state = ExecutionState::Error { error: err.clone() };
                Err(err)
            }
        }
    }

    pub fn resume(&mut self, resume_value: Option<Value>) -> Result<Value> {
        let (reason, mut last_result) = match self.execution_state.clone() {
            ExecutionState::Suspended {
                reason,
                last_result,
                ..
            } => (reason, last_result),
            current_state => {
                return Err(VmError::Internal(alloc::format!(
                    "Cannot resume VM when execution state is {:?}",
                    current_state
                )));
            }
        };

        match reason.clone() {
            SuspendReason::HostAwait { dest, .. } => {
                let value = resume_value.ok_or_else(|| {
                    VmError::Internal("HostAwait suspension requires a resume value".into())
                })?;

                if self.registers.len() <= dest as usize {
                    self.registers.resize(dest as usize + 1, Value::Undefined);
                }
                self.registers[dest as usize] = value;
            }
            other_reason => {
                if resume_value.is_some() {
                    return Err(VmError::Internal(alloc::format!(
                        "Unexpected resume value supplied for {:?}",
                        other_reason
                    )));
                }
            }
        }

        self.execution_state = ExecutionState::Running;

        let program = self.program.clone();
        self.run_stackless_loop(&program, &mut last_result)?;

        if matches!(self.execution_state, ExecutionState::Suspended { .. }) {
            Ok(last_result)
        } else {
            self.execution_stack.clear();
            self.execution_state = ExecutionState::Completed {
                result: last_result.clone(),
            };
            Ok(last_result)
        }
    }

    fn run_stackless_from(&mut self, start_pc: usize) -> Result<Value> {
        let program = self.program.clone();

        self.execution_stack.clear();
        self.execution_stack.push(ExecutionFrame::main(start_pc, 0));

        let mut last_result = self.registers.first().cloned().unwrap_or(Value::Undefined);

        self.run_stackless_loop(&program, &mut last_result)?;

        if matches!(self.execution_state, ExecutionState::Suspended { .. }) {
            Ok(last_result)
        } else {
            self.execution_stack.clear();
            self.execution_state = ExecutionState::Completed {
                result: last_result.clone(),
            };
            Ok(last_result)
        }
    }

    fn run_stackless_loop(&mut self, program: &Program, last_result: &mut Value) -> Result<()> {
        while !self.execution_stack.is_empty() {
            self.frame_pc_overridden = false;
            let should_finalize_rule = if let Some(frame) = self.execution_stack.last() {
                matches!(
                    frame.kind,
                    FrameKind::Rule(RuleFrameData {
                        phase: RuleFramePhase::Finalizing,
                        ..
                    })
                )
            } else {
                false
            };

            if should_finalize_rule {
                let frame = self.execution_stack.pop().expect("frame available");
                self.finalize_rule_execution_frame(frame, last_result)?;
                if self.execution_stack.is_empty() {
                    break;
                }
                continue;
            }

            let frame_pc = {
                let frame = self
                    .execution_stack
                    .last()
                    .expect("stack checked to be non-empty");
                frame.pc
            };

            if self.execution_mode == ExecutionMode::Suspendable
                && self.breakpoints.contains(&frame_pc)
            {
                self.pc = frame_pc;
                let snapshot = (*last_result).clone();
                self.execution_state = ExecutionState::Suspended {
                    reason: SuspendReason::Breakpoint { pc: frame_pc },
                    pc: frame_pc,
                    last_result: snapshot,
                };
                return Ok(());
            }

            if frame_pc >= program.instructions.len() {
                let frame = self.execution_stack.pop().expect("frame exists");
                self.finalize_rule_execution_frame(frame, last_result)?;
                if self.execution_stack.is_empty() {
                    break;
                }
                continue;
            }

            if self.executed_instructions >= self.max_instructions {
                self.execution_state = ExecutionState::Error {
                    error: VmError::InstructionLimitExceeded {
                        limit: self.max_instructions,
                    },
                };
                return Err(VmError::InstructionLimitExceeded {
                    limit: self.max_instructions,
                });
            }

            self.pc = frame_pc;
            let instruction = program.instructions[self.pc].clone();
            if let Some(frame_info) = self.execution_stack.last() {
                if let FrameKind::Comprehension { context, .. } = &frame_info.kind {
                    if context.iteration_state.is_none()
                        && frame_pc == context.comprehension_end as usize
                        && !matches!(instruction, Instruction::ComprehensionEnd { .. })
                    {
                        let resume_pc = frame_pc;
                        let _completed = self.execution_stack.pop().expect("frame exists");
                        if let Some(parent) = self.execution_stack.last_mut() {
                            parent.pc = resume_pc;
                            self.frame_pc_overridden = true;
                        }
                        continue;
                    }
                }
            }
            self.executed_instructions += 1;

            let stack_depth_before = self.execution_stack.len();

            match self.execute_instruction(program, instruction) {
                Ok(InstructionOutcome::Continue) => {
                    let stack_depth_after = self.execution_stack.len();
                    if stack_depth_after == stack_depth_before && !self.frame_pc_overridden {
                        if let Some(frame) = self.execution_stack.last_mut() {
                            frame.pc = self.pc + 1;
                        }
                    }
                    if self.step_mode {
                        self.handle_instruction_suspend(SuspendReason::Step, &*last_result);
                        return Ok(());
                    }
                }
                Ok(InstructionOutcome::Return(value)) => {
                    self.handle_instruction_return(value, last_result)?;
                    if self.execution_stack.is_empty() {
                        break;
                    }
                }
                Ok(InstructionOutcome::Break) => {
                    self.handle_instruction_break(last_result)?;
                    if self.execution_stack.is_empty() {
                        break;
                    }
                }
                Ok(InstructionOutcome::Suspend { reason }) => {
                    self.handle_instruction_suspend(reason, last_result);
                    return Ok(());
                }
                Err(err) => {
                    if self.handle_instruction_error(err.clone(), last_result)? {
                        if self.execution_stack.is_empty() {
                            break;
                        }
                        continue;
                    } else {
                        self.execution_stack.clear();
                        return Err(err);
                    }
                }
            }
        }

        Ok(())
    }

    fn handle_instruction_suspend(&mut self, reason: SuspendReason, last_result: &Value) {
        if let Some(frame) = self.execution_stack.last_mut() {
            if !self.frame_pc_overridden && frame.pc <= self.pc {
                frame.pc = self.pc + 1;
            }
        }

        self.execution_state = ExecutionState::Suspended {
            reason,
            pc: self.pc,
            last_result: last_result.clone(),
        };
    }

    fn handle_completed_frame_kind(&mut self, kind: FrameKind, last_result: &mut Value) {
        match kind {
            FrameKind::Main {
                return_value_register,
            } => {
                *last_result = self
                    .registers
                    .get(return_value_register as usize)
                    .cloned()
                    .unwrap_or(Value::Undefined);
            }
            FrameKind::Loop { .. } | FrameKind::Comprehension { .. } => {
                *last_result = self.registers.first().cloned().unwrap_or(Value::Undefined);
            }
            FrameKind::Rule(_) => {
                *last_result = Value::Undefined;
            }
        }
    }

    fn handle_instruction_return(&mut self, value: Value, last_result: &mut Value) -> Result<()> {
        loop {
            let frame = match self.execution_stack.pop() {
                Some(frame) => frame,
                None => {
                    *last_result = value;
                    return Ok(());
                }
            };

            match frame.kind {
                FrameKind::Rule(mut data) => {
                    if self.registers.len() <= data.result_reg as usize {
                        self.registers
                            .resize(data.result_reg as usize + 1, Value::Undefined);
                    }
                    self.registers[data.result_reg as usize] = value.clone();
                    data.accumulated_result = Some(value.clone());
                    data.any_body_succeeded = true;

                    let result = self.finalize_rule_frame_data(data)?;
                    *last_result = result.clone();

                    if let Some(parent_frame) = self.execution_stack.last_mut() {
                        parent_frame.pc = self.pc + 1;
                    }
                    return Ok(());
                }
                FrameKind::Main {
                    return_value_register,
                } => {
                    if self.registers.len() <= return_value_register as usize {
                        self.registers
                            .resize(return_value_register as usize + 1, Value::Undefined);
                    }
                    self.registers[return_value_register as usize] = value.clone();
                    *last_result = value;
                    return Ok(());
                }
                FrameKind::Loop { return_pc, .. } | FrameKind::Comprehension { return_pc, .. } => {
                    if let Some(parent_frame) = self.execution_stack.last_mut() {
                        parent_frame.pc = return_pc;
                    }
                    // Propagate the return value outward until we reach the owning frame
                    continue;
                }
            }
        }
    }

    fn handle_instruction_break(&mut self, last_result: &mut Value) -> Result<()> {
        if let Some(frame) = self.execution_stack.pop() {
            match frame.kind {
                FrameKind::Rule(mut data) => {
                    let current_pc = frame.pc;
                    let next_pc = self.handle_rule_break_event(&mut data)?;
                    if let Some(pc) = next_pc {
                        self.execution_stack
                            .push(ExecutionFrame::new(pc, FrameKind::Rule(data)));
                    } else {
                        self.finalize_rule_execution_frame(
                            ExecutionFrame::new(current_pc, FrameKind::Rule(data)),
                            last_result,
                        )?;
                    }
                }
                other_kind => {
                    self.handle_break_non_rule(
                        ExecutionFrame::new(frame.pc, other_kind),
                        last_result,
                    );
                }
            }
        }

        Ok(())
    }

    fn handle_instruction_error(&mut self, _err: VmError, last_result: &mut Value) -> Result<bool> {
        if let Some(frame) = self.execution_stack.pop() {
            match frame.kind {
                FrameKind::Rule(mut data) => {
                    let current_pc = frame.pc;
                    let next_pc = self.handle_rule_error_event(&mut data)?;
                    if let Some(pc) = next_pc {
                        self.execution_stack
                            .push(ExecutionFrame::new(pc, FrameKind::Rule(data)));
                    } else {
                        self.finalize_rule_execution_frame(
                            ExecutionFrame::new(current_pc, FrameKind::Rule(data)),
                            last_result,
                        )?;
                    }
                    return Ok(true);
                }
                other_kind => {
                    self.execution_stack
                        .push(ExecutionFrame::new(frame.pc, other_kind));
                }
            }
        }

        Ok(false)
    }

    fn handle_break_non_rule(&mut self, frame: ExecutionFrame, last_result: &mut Value) {
        match frame.kind {
            FrameKind::Main {
                return_value_register,
            } => {
                *last_result = self
                    .registers
                    .get(return_value_register as usize)
                    .cloned()
                    .unwrap_or(Value::Undefined);
            }
            FrameKind::Loop { return_pc, .. } | FrameKind::Comprehension { return_pc, .. } => {
                if let Some(parent_frame) = self.execution_stack.last_mut() {
                    parent_frame.pc = return_pc;
                }
                *last_result = self.registers.first().cloned().unwrap_or(Value::Undefined);
            }
            FrameKind::Rule(_) => {}
        }
    }

    fn finalize_rule_execution_frame(
        &mut self,
        frame: ExecutionFrame,
        last_result: &mut Value,
    ) -> Result<()> {
        match frame.kind {
            FrameKind::Rule(data) => {
                let result = self.finalize_rule_frame_data(data)?;
                *last_result = result.clone();
                if let Some(parent_frame) = self.execution_stack.last_mut() {
                    parent_frame.pc = self.pc + 1;
                }
            }
            other_kind => {
                self.handle_completed_frame_kind(other_kind, last_result);
            }
        }
        Ok(())
    }
}
