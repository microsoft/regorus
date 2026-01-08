// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use crate::rvm::instructions::Instruction;
use crate::rvm::program::Program;
use crate::value::Value;
use alloc::string::String;
use alloc::vec::Vec;
use core::convert::TryFrom as _;

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
                pc: self.pc,
            });
        }

        let &(ref entry_point_name, entry_point_pc) =
            entry_points
                .get(index)
                .ok_or(VmError::InvalidEntryPointIndex {
                    index,
                    max_index: entry_points.len().saturating_sub(1),
                    pc: self.pc,
                })?;

        if entry_point_pc >= self.program.instructions.len() {
            return Err(VmError::EntryPointPcOutOfBounds {
                pc: entry_point_pc,
                instruction_count: self.program.instructions.len(),
                entry_point: entry_point_name.clone(),
            });
        }

        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.reset_execution_state();
                self.reset_execution_timer_state();

                self.validate_vm_state()?;
                let entry_point_pc_u32 = u32::try_from(entry_point_pc).map_err(|_| {
                    VmError::EntryPointPcOutOfBounds {
                        pc: entry_point_pc,
                        instruction_count: self.program.instructions.len(),
                        entry_point: entry_point_name.clone(),
                    }
                })?;

                self.jump_to(entry_point_pc_u32)
            }
            ExecutionMode::Suspendable => {
                self.reset_execution_state();
                self.reset_execution_timer_state();

                self.validate_vm_state()?;
                self.execute_suspendable_entry(entry_point_pc)
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
                    pc: self.pc,
                })?;

        if entry_point_pc >= self.program.instructions.len() {
            return Err(VmError::EntryPointPcOutOfBounds {
                pc: entry_point_pc,
                instruction_count: self.program.instructions.len(),
                entry_point: String::from(name),
            });
        }

        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.reset_execution_state();
                self.reset_execution_timer_state();

                self.validate_vm_state()?;
                let entry_point_pc_u32 = u32::try_from(entry_point_pc).map_err(|_| {
                    VmError::EntryPointPcOutOfBounds {
                        pc: entry_point_pc,
                        instruction_count: self.program.instructions.len(),
                        entry_point: String::from(name),
                    }
                })?;

                self.jump_to(entry_point_pc_u32)
            }
            ExecutionMode::Suspendable => {
                self.reset_execution_state();
                self.reset_execution_timer_state();

                self.validate_vm_state()?;
                self.execute_suspendable_entry(entry_point_pc)
            }
        }
    }

    pub(super) fn jump_to(&mut self, target: u32) -> Result<Value> {
        let program = self.program.clone();
        let target = self.convert_pc(target, "jump target")?;
        self.pc = target;
        while self.pc < program.instructions.len() {
            self.memory_check()?;
            if self.executed_instructions >= self.max_instructions {
                return Err(VmError::InstructionLimitExceeded {
                    limit: self.max_instructions,
                    executed: self.executed_instructions,
                    pc: self.pc,
                });
            }

            self.execution_timer_tick(1)?;
            self.executed_instructions = self.executed_instructions.saturating_add(1);
            let instruction = program.instructions.get(self.pc).cloned().ok_or(
                VmError::ProgramCounterOutOfBounds {
                    pc: self.pc,
                    instruction_count: program.instructions.len(),
                },
            )?;

            match self.execute_instruction(&program, instruction)? {
                InstructionOutcome::Continue => {
                    self.pc = self.pc.saturating_add(1);
                }
                InstructionOutcome::Return(value) => {
                    return Ok(value);
                }
                InstructionOutcome::Break => {
                    return Ok(self.registers.first().cloned().unwrap_or(Value::Undefined));
                }
                InstructionOutcome::Suspend { reason } => {
                    return Err(VmError::UnsupportedSuspendInRunToCompletion {
                        reason,
                        pc: self.pc,
                    });
                }
            }
        }

        Ok(self.registers.first().cloned().unwrap_or(Value::Undefined))
    }

    fn execute_run_to_completion(&mut self) -> Result<Value> {
        self.reset_execution_state();
        self.reset_execution_timer_state();
        self.execution_state = ExecutionState::Running;
        match self.jump_to(0_u32) {
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
        self.reset_execution_timer_state();
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
        self.reset_execution_timer_state();
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
                return Err(VmError::InvalidResumeState {
                    state: alloc::format!("{:?}", current_state),
                    pc: self.pc,
                });
            }
        };

        match reason {
            SuspendReason::HostAwait {
                dest,
                argument,
                identifier,
            } => {
                let value = resume_value.ok_or_else(|| VmError::MissingResumeValue {
                    reason: SuspendReason::HostAwait {
                        dest,
                        argument: argument.clone(),
                        identifier: identifier.clone(),
                    },
                    pc: self.pc,
                })?;

                let dest_index = usize::from(dest);
                if self.registers.len() <= dest_index {
                    let new_len = dest_index.saturating_add(1);
                    self.registers.resize(new_len, Value::Undefined);
                }
                if let Some(slot) = self.registers.get_mut(dest_index) {
                    *slot = value;
                }
            }
            other_reason => {
                if resume_value.is_some() {
                    return Err(VmError::UnexpectedResumeValue {
                        reason: other_reason.clone(),
                        pc: self.pc,
                    });
                }
            }
        }

        self.execution_state = ExecutionState::Running;
        self.restore_execution_timer_after_resume();

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
            self.memory_check()?;
            self.frame_pc_overridden = false;
            let should_finalize_rule = self.execution_stack.last().is_some_and(|frame| {
                matches!(
                    frame.kind,
                    FrameKind::Rule(RuleFrameData {
                        phase: RuleFramePhase::Finalizing,
                        ..
                    })
                )
            });

            if should_finalize_rule {
                let frame = self
                    .execution_stack
                    .pop()
                    .ok_or(VmError::MissingExecutionFrame {
                        context: "finalizing rule",
                        pc: self.pc,
                    })?;
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
                    .ok_or(VmError::MissingExecutionFrame {
                        context: "determining pc",
                        pc: self.pc,
                    })?;
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
                let frame = self
                    .execution_stack
                    .pop()
                    .ok_or(VmError::MissingExecutionFrame {
                        context: "finalizing out-of-range pc",
                        pc: self.pc,
                    })?;
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
                        executed: self.executed_instructions,
                        pc: frame_pc,
                    },
                };
                return Err(VmError::InstructionLimitExceeded {
                    limit: self.max_instructions,
                    executed: self.executed_instructions,
                    pc: frame_pc,
                });
            }

            self.pc = frame_pc;
            if let Err(err) = self.execution_timer_tick(1) {
                self.execution_state = ExecutionState::Error { error: err.clone() };
                return Err(err);
            }
            let instruction = program.instructions.get(self.pc).cloned().ok_or(
                VmError::ProgramCounterOutOfBounds {
                    pc: self.pc,
                    instruction_count: program.instructions.len(),
                },
            )?;
            if let Some(frame_info) = self.execution_stack.last() {
                if let FrameKind::Comprehension { ref context, .. } = frame_info.kind {
                    if context.iteration_state.is_none()
                        && frame_pc == usize::from(context.comprehension_end)
                        && !matches!(instruction, Instruction::ComprehensionEnd { .. })
                    {
                        let resume_pc = frame_pc;
                        let _completed =
                            self.execution_stack
                                .pop()
                                .ok_or(VmError::MissingExecutionFrame {
                                    context: "unwinding comprehension",
                                    pc: self.pc,
                                })?;
                        if let Some(parent) = self.execution_stack.last_mut() {
                            parent.pc = resume_pc;
                            self.frame_pc_overridden = true;
                        }
                        continue;
                    }
                }
            }
            self.executed_instructions = self.executed_instructions.saturating_add(1);

            let stack_depth_before = self.execution_stack.len();

            match self.execute_instruction(program, instruction) {
                Ok(InstructionOutcome::Continue) => {
                    let stack_depth_after = self.execution_stack.len();
                    if stack_depth_after == stack_depth_before && !self.frame_pc_overridden {
                        if let Some(frame) = self.execution_stack.last_mut() {
                            frame.pc = self.pc.saturating_add(1);
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
                frame.pc = self.pc.saturating_add(1);
            }
        }

        self.snapshot_execution_timer_on_suspend();
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
                    .get(usize::from(return_value_register))
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
                    let result_index = usize::from(data.result_reg);
                    if self.registers.len() <= result_index {
                        let new_len = result_index.saturating_add(1);
                        self.registers.resize(new_len, Value::Undefined);
                    }
                    if let Some(slot) = self.registers.get_mut(result_index) {
                        *slot = value.clone();
                    }
                    data.accumulated_result = Some(value.clone());
                    data.any_body_succeeded = true;

                    let result = self.finalize_rule_frame_data(data)?;
                    *last_result = result.clone();

                    if let Some(parent_frame) = self.execution_stack.last_mut() {
                        parent_frame.pc = self.pc.saturating_add(1);
                    }
                    return Ok(());
                }
                FrameKind::Main {
                    return_value_register,
                } => {
                    let ret_index = usize::from(return_value_register);
                    if self.registers.len() <= ret_index {
                        let new_len = ret_index.saturating_add(1);
                        self.registers.resize(new_len, Value::Undefined);
                    }
                    if let Some(slot) = self.registers.get_mut(ret_index) {
                        *slot = value.clone();
                    }
                    *last_result = value;
                    return Ok(());
                }
                FrameKind::Loop { return_pc, .. } | FrameKind::Comprehension { return_pc, .. } => {
                    if let Some(parent_frame) = self.execution_stack.last_mut() {
                        parent_frame.pc = return_pc;
                    }
                    // Propagate the return value outward until we reach the owning frame
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
                    .get(usize::from(return_value_register))
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
                    parent_frame.pc = self.pc.saturating_add(1);
                }
            }
            other_kind => {
                self.handle_completed_frame_kind(other_kind, last_result);
            }
        }
        Ok(())
    }
}
