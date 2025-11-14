// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::FunctionCallParams;
use crate::rvm::program::{RuleInfo, RuleType};
use crate::value::Value;
use alloc::vec::Vec;
use core::mem;

use super::context::CallRuleContext;
use super::errors::{Result, VmError};
use super::execution_model::{
    ExecutionFrame, ExecutionMode, FrameKind, RuleFrameData, RuleFramePhase,
};
use super::machine::RegoVM;

impl RegoVM {
    pub(super) fn execute_rule_definitions_common(
        &mut self,
        rule_definitions: &[Vec<u32>],
        rule_info: &RuleInfo,
        function_call_params: Option<&FunctionCallParams>,
    ) -> Result<(Value, bool)> {
        let mut first_successful_result: Option<Value> = None;
        let mut rule_failed_due_to_inconsistency = false;
        let is_function_call = rule_info.function_info.is_some();
        let result_reg = rule_info.result_reg as usize;

        let num_registers = rule_info.num_registers as usize;
        let mut register_window = self.new_register_window();
        register_window.clear();
        register_window.reserve(num_registers);

        register_window.push(Value::Undefined);

        let num_retained_registers = match function_call_params {
            Some(params) => {
                for arg in params.args[0..params.num_args as usize].iter() {
                    register_window.push(self.registers[*arg as usize].clone());
                }
                params.num_args as usize + 1
            }
            _ => match rule_info.rule_type {
                RuleType::PartialSet | RuleType::PartialObject => 1,
                RuleType::Complete => 0,
            },
        };

        let mut old_registers = Vec::default();
        mem::swap(&mut old_registers, &mut self.registers);

        let mut old_loop_stack = Vec::default();
        mem::swap(&mut old_loop_stack, &mut self.loop_stack);

        let mut old_comprehension_stack = Vec::default();
        mem::swap(&mut old_comprehension_stack, &mut self.comprehension_stack);

        self.register_stack.push(old_registers);
        self.registers = register_window;

        'outer: for (def_idx, definition_bodies) in rule_definitions.iter().enumerate() {
            for (body_entry_point_idx, body_entry_point) in definition_bodies.iter().enumerate() {
                if let Some(ctx) = self.call_rule_stack.last_mut() {
                    ctx.current_body_index = body_entry_point_idx;
                    ctx.current_definition_index = def_idx;
                }

                self.registers
                    .resize(num_retained_registers, Value::Undefined);
                self.registers.resize(num_registers, Value::Undefined);

                if let Some(destructuring_entry_point) =
                    rule_info.destructuring_blocks.get(def_idx).and_then(|x| *x)
                {
                    match self.jump_to(destructuring_entry_point as usize) {
                        Ok(_result) => {}
                        Err(_e) => {
                            continue 'outer;
                        }
                    }
                }

                match self.jump_to(*body_entry_point as usize) {
                    Ok(_) => {
                        if matches!(rule_info.rule_type, RuleType::Complete) || is_function_call {
                            let current_result = self.registers[result_reg].clone();
                            if current_result != Value::Undefined {
                                if let Some(ref expected) = first_successful_result {
                                    if *expected != current_result {
                                        rule_failed_due_to_inconsistency = true;
                                        self.registers[result_reg] = Value::Undefined;
                                        break;
                                    }
                                } else {
                                    first_successful_result = Some(current_result.clone());
                                }
                            }
                        }
                    }
                    Err(_e) => {
                        continue;
                    }
                }
            }

            if rule_failed_due_to_inconsistency {
                break;
            }
        }

        let final_result = if rule_failed_due_to_inconsistency {
            Value::Undefined
        } else if let Some(successful_result) = first_successful_result {
            successful_result
        } else {
            self.registers[result_reg].clone()
        };

        if let Some(old_registers) = self.register_stack.pop() {
            let mut current_register_window = Vec::default();
            mem::swap(&mut current_register_window, &mut self.registers);
            self.return_register_window(current_register_window);

            self.registers = old_registers;
        }

        self.loop_stack = old_loop_stack;
        self.comprehension_stack = old_comprehension_stack;

        Ok((final_result, rule_failed_due_to_inconsistency))
    }

    pub(super) fn execute_call_rule_common(
        &mut self,
        dest: u8,
        rule_index: u16,
        function_call_params: Option<&FunctionCallParams>,
    ) -> Result<()> {
        let rule_idx = rule_index as usize;

        if rule_idx >= self.rule_cache.len() {
            return Err(VmError::RuleIndexOutOfBounds { index: rule_index });
        }

        let rule_info = self
            .program
            .rule_infos
            .get(rule_idx)
            .ok_or(VmError::RuleInfoMissing { index: rule_index })?
            .clone();

        let is_function_rule = rule_info.function_info.is_some();

        if !is_function_rule {
            let (computed, cached_result) = &self.rule_cache[rule_idx];
            if *computed {
                self.registers[dest as usize] = cached_result.clone();
                return Ok(());
            }
        }

        let rule_type = rule_info.rule_type.clone();
        let rule_definitions = rule_info.definitions.clone();

        if rule_definitions.is_empty() {
            let result = Value::Undefined;
            if !is_function_rule {
                self.rule_cache[rule_idx] = (true, result.clone());
            }
            self.registers[dest as usize] = result;
            return Ok(());
        }

        self.call_rule_stack.push(CallRuleContext {
            return_pc: self.pc,
            dest_reg: dest,
            result_reg: rule_info.result_reg,
            rule_index,
            rule_type: rule_type.clone(),
            current_definition_index: 0,
            current_body_index: 0,
        });

        let (final_result, rule_failed_due_to_inconsistency) = self
            .execute_rule_definitions_common(&rule_definitions, &rule_info, function_call_params)?;

        self.registers[dest as usize] = Value::Undefined;

        let call_context = self.call_rule_stack.pop().expect("Call stack underflow");
        self.pc = call_context.return_pc;

        let result_from_rule = if !rule_failed_due_to_inconsistency {
            final_result
        } else {
            Value::Undefined
        };

        self.registers[dest as usize] = result_from_rule.clone();

        if self.registers[dest as usize] == Value::Undefined && !rule_failed_due_to_inconsistency {
            match call_context.rule_type {
                RuleType::PartialSet => {
                    self.registers[dest as usize] = Value::new_set();
                }
                RuleType::PartialObject => {
                    self.registers[dest as usize] = Value::new_object();
                }
                RuleType::Complete => {
                    if let Some(rule_info) = self
                        .program
                        .rule_infos
                        .get(call_context.rule_index as usize)
                    {
                        if let Some(default_literal_index) = rule_info.default_literal_index {
                            if let Some(default_value) =
                                self.program.literals.get(default_literal_index as usize)
                            {
                                self.registers[dest as usize] = default_value.clone();
                            }
                        }
                    }
                }
            }
        }

        let final_result = self.registers[dest as usize].clone();
        if !is_function_rule {
            self.rule_cache[rule_idx] = (true, final_result);
        }
        Ok(())
    }

    pub(super) fn execute_call_rule(&mut self, dest: u8, rule_index: u16) -> Result<()> {
        match self.execution_mode {
            ExecutionMode::RunToCompletion => self.execute_call_rule_common(dest, rule_index, None),
            ExecutionMode::Suspendable => {
                self.execute_call_rule_suspendable(dest, rule_index, None)
            }
        }
    }

    pub(super) fn execute_call_rule_suspendable(
        &mut self,
        dest: u8,
        rule_index: u16,
        function_call_params: Option<&FunctionCallParams>,
    ) -> Result<()> {
        let rule_idx = rule_index as usize;

        if rule_idx >= self.rule_cache.len() {
            return Err(VmError::RuleIndexOutOfBounds { index: rule_index });
        }

        let rule_info = self
            .program
            .rule_infos
            .get(rule_idx)
            .ok_or(VmError::RuleInfoMissing { index: rule_index })?
            .clone();

        let is_function_rule = rule_info.function_info.is_some();

        if !is_function_rule {
            let (computed, cached_result) = &self.rule_cache[rule_idx];
            if *computed {
                self.registers[dest as usize] = cached_result.clone();
                return Ok(());
            }
        }

        if rule_info.definitions.is_empty() {
            let result = Value::Undefined;
            if !is_function_rule {
                self.rule_cache[rule_idx] = (true, result.clone());
            }
            if self.registers.len() <= dest as usize {
                self.registers.resize(dest as usize + 1, Value::Undefined);
            }
            self.registers[dest as usize] = result;
            return Ok(());
        }

        let num_registers = rule_info.num_registers as usize;

        let num_retained_registers = match function_call_params {
            Some(params) => params.arg_count() + 1,
            None => match rule_info.rule_type {
                RuleType::PartialSet | RuleType::PartialObject => 1,
                RuleType::Complete => 0,
            },
        };

        let mut register_window = self.new_register_window();
        register_window.clear();
        register_window.reserve(num_registers);
        register_window.push(Value::Undefined);

        if let Some(params) = function_call_params {
            for &arg in params.arg_registers() {
                register_window.push(self.registers[arg as usize].clone());
            }
        }

        let mut saved_registers = Vec::default();
        mem::swap(&mut saved_registers, &mut self.registers);
        self.registers = register_window;

        let mut saved_loop_stack = Vec::default();
        mem::swap(&mut saved_loop_stack, &mut self.loop_stack);

        let mut saved_comprehension_stack = Vec::default();
        mem::swap(
            &mut saved_comprehension_stack,
            &mut self.comprehension_stack,
        );

        self.loop_stack.clear();
        self.comprehension_stack.clear();

        self.call_rule_stack.push(CallRuleContext {
            return_pc: self.pc,
            dest_reg: dest,
            result_reg: rule_info.result_reg,
            rule_index,
            rule_type: rule_info.rule_type.clone(),
            current_definition_index: 0,
            current_body_index: 0,
        });

        let mut frame_data = RuleFrameData {
            return_pc: self.pc,
            dest_reg: dest,
            rule_index,
            current_definition_index: 0,
            current_body_index: 0,
            total_definitions: rule_info.definitions.len(),
            phase: RuleFramePhase::Initializing,
            accumulated_result: None,
            any_body_succeeded: false,
            rule_failed_due_to_inconsistency: false,
            rule_type: rule_info.rule_type.clone(),
            result_reg: rule_info.result_reg,
            is_function_rule,
            num_registers,
            num_retained_registers,
            saved_registers,
            saved_loop_stack,
            saved_comprehension_stack,
        };

        let initial_pc = self
            .prepare_rule_frame_initial_pc(&mut frame_data, &rule_info)?
            .ok_or_else(|| VmError::Internal("Rule frame has no initial PC".into()))?;

        let frame = ExecutionFrame::new(initial_pc, FrameKind::Rule(frame_data));
        self.execution_stack.push(frame);

        Ok(())
    }

    pub(super) fn execute_rule_init(&mut self, result_reg: u8, _rule_index: u16) -> Result<()> {
        let current_ctx = self
            .call_rule_stack
            .last_mut()
            .expect("Call stack underflow");
        current_ctx.result_reg = result_reg;
        match current_ctx.rule_type {
            RuleType::Complete => {
                self.registers[result_reg as usize] = Value::Undefined;
            }
            RuleType::PartialSet => {
                if current_ctx.current_definition_index == 0 && current_ctx.current_body_index == 0
                {
                    self.registers[result_reg as usize] = Value::new_set();
                }
            }
            RuleType::PartialObject => {
                if current_ctx.current_definition_index == 0 && current_ctx.current_body_index == 0
                {
                    self.registers[result_reg as usize] = Value::new_object();
                }
            }
        }
        Ok(())
    }

    pub(super) fn execute_rule_return(&mut self) -> Result<()> {
        Ok(())
    }

    fn prepare_rule_frame_initial_pc(
        &mut self,
        frame_data: &mut RuleFrameData,
        rule_info: &RuleInfo,
    ) -> Result<Option<usize>> {
        frame_data.current_definition_index = 0;
        frame_data.current_body_index = 0;
        frame_data.phase = RuleFramePhase::Initializing;
        self.rule_frame_schedule_segment(frame_data, rule_info)
    }

    fn rule_frame_schedule_segment(
        &mut self,
        frame_data: &mut RuleFrameData,
        rule_info: &RuleInfo,
    ) -> Result<Option<usize>> {
        if frame_data.rule_failed_due_to_inconsistency {
            frame_data.phase = RuleFramePhase::Finalizing;
            return Ok(None);
        }

        while frame_data.current_definition_index < frame_data.total_definitions {
            let definition_bodies = &rule_info.definitions[frame_data.current_definition_index];

            if frame_data.current_body_index < definition_bodies.len() {
                if let Some(ctx) = self.call_rule_stack.last_mut() {
                    ctx.current_definition_index = frame_data.current_definition_index;
                    ctx.current_body_index = frame_data.current_body_index;
                }

                self.registers
                    .resize(frame_data.num_retained_registers, Value::Undefined);
                self.registers
                    .resize(frame_data.num_registers, Value::Undefined);

                if let Some(destructuring_entry_point) = rule_info
                    .destructuring_blocks
                    .get(frame_data.current_definition_index)
                    .and_then(|opt| *opt)
                {
                    frame_data.phase = RuleFramePhase::ExecutingDestructuring;
                    return Ok(Some(destructuring_entry_point as usize));
                } else {
                    frame_data.phase = RuleFramePhase::ExecutingBody;
                    return Ok(Some(
                        definition_bodies[frame_data.current_body_index] as usize,
                    ));
                }
            } else {
                frame_data.current_definition_index += 1;
                frame_data.current_body_index = 0;
            }
        }

        frame_data.phase = RuleFramePhase::Finalizing;
        Ok(None)
    }

    fn rule_frame_after_destructuring_success(
        &mut self,
        frame_data: &mut RuleFrameData,
        rule_info: &RuleInfo,
    ) -> Result<Option<usize>> {
        frame_data.phase = RuleFramePhase::ExecutingBody;
        let definition_bodies = &rule_info.definitions[frame_data.current_definition_index];
        if frame_data.current_body_index >= definition_bodies.len() {
            frame_data.current_body_index += 1;
            return self.rule_frame_schedule_segment(frame_data, rule_info);
        }

        Ok(Some(
            definition_bodies[frame_data.current_body_index] as usize,
        ))
    }

    fn rule_frame_after_failure(
        &mut self,
        frame_data: &mut RuleFrameData,
        rule_info: &RuleInfo,
    ) -> Result<Option<usize>> {
        frame_data.current_body_index += 1;
        self.rule_frame_schedule_segment(frame_data, rule_info)
    }

    fn rule_frame_after_success(
        &mut self,
        frame_data: &mut RuleFrameData,
        rule_info: &RuleInfo,
    ) -> Result<Option<usize>> {
        frame_data.any_body_succeeded = true;

        if matches!(frame_data.rule_type, RuleType::Complete) || frame_data.is_function_rule {
            let current_result = self
                .registers
                .get(frame_data.result_reg as usize)
                .cloned()
                .unwrap_or(Value::Undefined);

            if current_result != Value::Undefined {
                if let Some(expected) = &frame_data.accumulated_result {
                    if *expected != current_result {
                        frame_data.rule_failed_due_to_inconsistency = true;
                        if let Some(result_slot) =
                            self.registers.get_mut(frame_data.result_reg as usize)
                        {
                            *result_slot = Value::Undefined;
                        }
                    }
                } else {
                    frame_data.accumulated_result = Some(current_result);
                }
            }
        }

        frame_data.current_body_index += 1;
        self.rule_frame_schedule_segment(frame_data, rule_info)
    }

    pub(super) fn finalize_rule_frame_data(&mut self, frame_data: RuleFrameData) -> Result<Value> {
        let RuleFrameData {
            return_pc,
            dest_reg,
            rule_index,
            accumulated_result,
            rule_failed_due_to_inconsistency,
            rule_type,
            result_reg,
            is_function_rule,
            saved_registers,
            saved_loop_stack,
            saved_comprehension_stack,
            ..
        } = frame_data;

        let rule_idx = rule_index as usize;
        let rule_info = self
            .program
            .rule_infos
            .get(rule_idx)
            .ok_or(VmError::RuleInfoMissing { index: rule_index })?
            .clone();

        let result_from_rule = if rule_failed_due_to_inconsistency {
            Value::Undefined
        } else if let Some(value) = accumulated_result {
            value
        } else {
            self.registers
                .get(result_reg as usize)
                .cloned()
                .unwrap_or(Value::Undefined)
        };

        let mut current_window = Vec::default();
        mem::swap(&mut current_window, &mut self.registers);
        self.return_register_window(current_window);

        self.loop_stack = saved_loop_stack;
        self.comprehension_stack = saved_comprehension_stack;

        let mut parent_registers = saved_registers;
        if parent_registers.len() <= dest_reg as usize {
            parent_registers.resize(dest_reg as usize + 1, Value::Undefined);
        }
        parent_registers[dest_reg as usize] = result_from_rule.clone();

        if parent_registers[dest_reg as usize] == Value::Undefined
            && !rule_failed_due_to_inconsistency
        {
            match rule_type {
                RuleType::PartialSet => parent_registers[dest_reg as usize] = Value::new_set(),
                RuleType::PartialObject => {
                    parent_registers[dest_reg as usize] = Value::new_object()
                }
                RuleType::Complete => {
                    if let Some(default_literal_index) = rule_info.default_literal_index {
                        if let Some(default_value) =
                            self.program.literals.get(default_literal_index as usize)
                        {
                            parent_registers[dest_reg as usize] = default_value.clone();
                        }
                    }
                }
            }
        }

        let final_value = parent_registers[dest_reg as usize].clone();

        if !is_function_rule {
            self.rule_cache[rule_idx] = (true, final_value.clone());
        }

        self.registers = parent_registers;

        if self.call_rule_stack.pop().is_none() {
            return Err(VmError::Internal(alloc::format!(
                "Call rule stack underflow during rule finalization | {}",
                self.get_debug_state()
            )));
        }

        self.pc = return_pc;

        Ok(final_value)
    }

    pub(super) fn handle_rule_break_event(
        &mut self,
        frame_data: &mut RuleFrameData,
    ) -> Result<Option<usize>> {
        let rule_info = self.get_rule_info(frame_data.rule_index)?;
        match frame_data.phase {
            RuleFramePhase::ExecutingDestructuring => {
                self.rule_frame_after_destructuring_success(frame_data, &rule_info)
            }
            RuleFramePhase::ExecutingBody => self.rule_frame_after_success(frame_data, &rule_info),
            RuleFramePhase::Initializing | RuleFramePhase::Finalizing => Ok(None),
        }
    }

    pub(super) fn handle_rule_error_event(
        &mut self,
        frame_data: &mut RuleFrameData,
    ) -> Result<Option<usize>> {
        let rule_info = self.get_rule_info(frame_data.rule_index)?;
        self.rule_frame_after_failure(frame_data, &rule_info)
    }

    fn get_rule_info(&self, rule_index: u16) -> Result<RuleInfo> {
        let idx = rule_index as usize;
        self.program
            .rule_infos
            .get(idx)
            .cloned()
            .ok_or(VmError::RuleInfoMissing { index: rule_index })
    }
}
