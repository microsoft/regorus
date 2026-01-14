// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::FunctionCallParams;
use crate::rvm::program::{RuleInfo, RuleType};
use crate::value::Value;
use alloc::format;
use alloc::vec::Vec;
use core::convert::TryFrom as _;
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
        let result_reg = rule_info.result_reg;

        let num_registers = usize::from(rule_info.num_registers);
        let mut register_window = self.new_register_window();
        register_window.clear();
        register_window.reserve(num_registers);

        register_window.push(Value::Undefined);

        let num_retained_registers = match function_call_params {
            Some(params) => {
                for &arg in params.arg_registers() {
                    register_window.push(self.get_register(arg)?.clone());
                }
                self.checked_add_one(params.arg_count(), "retained function registers")?
            }
            _ => match rule_info.rule_type {
                RuleType::PartialSet | RuleType::PartialObject => 1,
                RuleType::Complete => 0,
            },
        };

        let mut previous_registers = Vec::default();
        mem::swap(&mut previous_registers, &mut self.registers);

        let mut previous_loop_stack = Vec::default();
        mem::swap(&mut previous_loop_stack, &mut self.loop_stack);

        let mut previous_comprehension_stack = Vec::default();
        mem::swap(
            &mut previous_comprehension_stack,
            &mut self.comprehension_stack,
        );

        self.register_stack.push(previous_registers);
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
                    match self.jump_to(destructuring_entry_point) {
                        Ok(_result) => {}
                        Err(_e) => {
                            continue 'outer;
                        }
                    }
                }

                match self.jump_to(*body_entry_point) {
                    Ok(_) => {
                        if matches!(rule_info.rule_type, RuleType::Complete) || is_function_call {
                            let current_result = self.get_register(result_reg)?.clone();
                            if current_result != Value::Undefined {
                                if let Some(ref expected) = first_successful_result {
                                    if *expected != current_result {
                                        rule_failed_due_to_inconsistency = true;
                                        self.set_register(result_reg, Value::Undefined)?;
                                        break;
                                    }
                                } else {
                                    first_successful_result = Some(current_result.clone());
                                }
                            }
                        }

                        // Once a body in this definition succeeds, remaining bodies
                        // are treated as else-branches and must not be evaluated.
                        break;
                    }
                    Err(_e) => {}
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
            self.get_register(result_reg)?.clone()
        };

        if let Some(restored_registers) = self.register_stack.pop() {
            let mut current_register_window = Vec::default();
            mem::swap(&mut current_register_window, &mut self.registers);
            self.return_register_window(current_register_window);

            self.registers = restored_registers;
        }

        self.loop_stack = previous_loop_stack;
        self.comprehension_stack = previous_comprehension_stack;

        Ok((final_result, rule_failed_due_to_inconsistency))
    }

    pub(super) fn execute_call_rule_common(
        &mut self,
        dest: u8,
        rule_index: u16,
        function_call_params: Option<&FunctionCallParams>,
    ) -> Result<()> {
        let rule_idx = usize::from(rule_index);

        if rule_idx >= self.rule_cache.len() {
            return Err(VmError::RuleIndexOutOfBounds {
                index: rule_index,
                pc: self.pc,
                available: self.rule_cache.len(),
            });
        }

        let rule_info = self
            .program
            .rule_infos
            .get(rule_idx)
            .ok_or(VmError::RuleInfoMissing {
                index: rule_index,
                pc: self.pc,
                available: self.program.rule_infos.len(),
            })?
            .clone();

        let is_function_rule = rule_info.function_info.is_some();

        if !is_function_rule {
            let (ref computed, ref cached_result) =
                *self
                    .rule_cache
                    .get(rule_idx)
                    .ok_or(VmError::RuleIndexOutOfBounds {
                        index: rule_index,
                        pc: self.pc,
                        available: self.rule_cache.len(),
                    })?;
            if *computed {
                self.set_register(dest, cached_result.clone())?;
                return Ok(());
            }
        }

        let rule_type = rule_info.rule_type.clone();
        let rule_definitions = rule_info.definitions.clone();

        if rule_definitions.is_empty() {
            let result = Value::Undefined;
            if !is_function_rule {
                let available = self.rule_cache.len();
                let entry =
                    self.rule_cache
                        .get_mut(rule_idx)
                        .ok_or(VmError::RuleIndexOutOfBounds {
                            index: rule_index,
                            pc: self.pc,
                            available,
                        })?;
                *entry = (true, result.clone());
            }
            self.set_register(dest, result)?;
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

        self.set_register(dest, Value::Undefined)?;

        let call_context = self
            .call_rule_stack
            .pop()
            .ok_or(VmError::CallRuleStackUnderflow { pc: self.pc })?;
        self.pc = call_context.return_pc;

        let result_from_rule = if !rule_failed_due_to_inconsistency {
            final_result
        } else {
            Value::Undefined
        };

        self.set_register(dest, result_from_rule.clone())?;

        if self.get_register(dest)? == &Value::Undefined && !rule_failed_due_to_inconsistency {
            match call_context.rule_type {
                RuleType::PartialSet => {
                    self.set_register(dest, Value::new_set())?;
                }
                RuleType::PartialObject => {
                    self.set_register(dest, Value::new_object())?;
                }
                RuleType::Complete => {
                    if let Some(rule_metadata) = self
                        .program
                        .rule_infos
                        .get(usize::from(call_context.rule_index))
                    {
                        if let Some(default_literal_index) = rule_metadata.default_literal_index {
                            if let Some(default_value) = self
                                .program
                                .literals
                                .get(usize::from(default_literal_index))
                                .cloned()
                            {
                                self.set_register(dest, default_value)?;
                            }
                        }
                    }
                }
            }
        }

        let final_value = self.get_register(dest)?.clone();
        if !is_function_rule {
            let available = self.rule_cache.len();
            let entry = self
                .rule_cache
                .get_mut(rule_idx)
                .ok_or(VmError::RuleIndexOutOfBounds {
                    index: rule_index,
                    pc: self.pc,
                    available,
                })?;
            *entry = (true, final_value.clone());
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
        let rule_idx = usize::from(rule_index);

        if rule_idx >= self.rule_cache.len() {
            return Err(VmError::RuleIndexOutOfBounds {
                index: rule_index,
                pc: self.pc,
                available: self.rule_cache.len(),
            });
        }

        let rule_info = self
            .program
            .rule_infos
            .get(rule_idx)
            .ok_or(VmError::RuleInfoMissing {
                index: rule_index,
                pc: self.pc,
                available: self.program.rule_infos.len(),
            })?
            .clone();

        let is_function_rule = rule_info.function_info.is_some();

        if !is_function_rule {
            let (ref computed, ref cached_result) =
                *self
                    .rule_cache
                    .get(rule_idx)
                    .ok_or(VmError::RuleIndexOutOfBounds {
                        index: rule_index,
                        pc: self.pc,
                        available: self.rule_cache.len(),
                    })?;
            if *computed {
                self.set_register(dest, cached_result.clone())?;
                return Ok(());
            }
        }

        if rule_info.definitions.is_empty() {
            let result = Value::Undefined;
            if !is_function_rule {
                let available = self.rule_cache.len();
                let entry =
                    self.rule_cache
                        .get_mut(rule_idx)
                        .ok_or(VmError::RuleIndexOutOfBounds {
                            index: rule_index,
                            pc: self.pc,
                            available,
                        })?;
                *entry = (true, result.clone());
            }
            let dest_index = usize::from(dest);
            if self.registers.len() <= dest_index {
                let new_len =
                    self.checked_add_one(dest_index, "register capacity for destination")?;
                self.registers.resize(new_len, Value::Undefined);
            }
            self.set_register(dest, result)?;
            return Ok(());
        }

        let num_registers = usize::from(rule_info.num_registers);

        let num_retained_registers = match function_call_params {
            Some(params) => {
                self.checked_add_one(params.arg_count(), "retained function registers")?
            }
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
                register_window.push(self.get_register(arg)?.clone());
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
            .ok_or(VmError::RuleFrameMissingInitialPc { pc: self.pc })?;

        let frame = ExecutionFrame::new(initial_pc, FrameKind::Rule(frame_data));
        self.execution_stack.push(frame);

        Ok(())
    }

    pub(super) fn execute_rule_init(&mut self, result_reg: u8, _rule_index: u16) -> Result<()> {
        let current_ctx = self
            .call_rule_stack
            .last_mut()
            .ok_or(VmError::CallRuleStackUnderflow { pc: self.pc })?;
        current_ctx.result_reg = result_reg;
        match current_ctx.rule_type {
            RuleType::Complete => {
                self.set_register(result_reg, Value::Undefined)?;
            }
            RuleType::PartialSet => {
                if current_ctx.current_definition_index == 0 && current_ctx.current_body_index == 0
                {
                    self.set_register(result_reg, Value::new_set())?;
                }
            }
            RuleType::PartialObject => {
                if current_ctx.current_definition_index == 0 && current_ctx.current_body_index == 0
                {
                    self.set_register(result_reg, Value::new_object())?;
                }
            }
        }
        Ok(())
    }

    pub(super) const fn execute_rule_return(&mut self) -> Result<()> {
        let _ = self;
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
            let definition_bodies = match rule_info
                .definitions
                .get(frame_data.current_definition_index)
            {
                Some(bodies) => bodies,
                None => {
                    frame_data.current_definition_index = frame_data.total_definitions;
                    break;
                }
            };

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
                    let next_pc =
                        self.convert_pc(destructuring_entry_point, "destructuring entry point")?;
                    return Ok(Some(next_pc));
                }

                if let Some(&body_entry_point) =
                    definition_bodies.get(frame_data.current_body_index)
                {
                    frame_data.phase = RuleFramePhase::ExecutingBody;
                    let next_pc = self.convert_pc(body_entry_point, "rule body entry point")?;
                    return Ok(Some(next_pc));
                }

                self.increment_counter(
                    &mut frame_data.current_definition_index,
                    "rule definition index",
                )?;
                frame_data.current_body_index = 0;
            } else {
                self.increment_counter(
                    &mut frame_data.current_definition_index,
                    "rule definition index",
                )?;
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
        let definition_bodies = match rule_info
            .definitions
            .get(frame_data.current_definition_index)
        {
            Some(bodies) => bodies,
            None => {
                frame_data.current_definition_index = frame_data.total_definitions;
                return Ok(None);
            }
        };

        if let Some(&entry_point) = definition_bodies.get(frame_data.current_body_index) {
            let next_pc = self.convert_pc(entry_point, "rule body entry point")?;
            Ok(Some(next_pc))
        } else {
            self.increment_counter(&mut frame_data.current_body_index, "rule body index")?;
            self.rule_frame_schedule_segment(frame_data, rule_info)
        }
    }

    fn rule_frame_after_failure(
        &mut self,
        frame_data: &mut RuleFrameData,
        rule_info: &RuleInfo,
    ) -> Result<Option<usize>> {
        self.increment_counter(&mut frame_data.current_body_index, "rule body index")?;
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
                .get(usize::from(frame_data.result_reg))
                .cloned()
                .unwrap_or(Value::Undefined);

            if current_result != Value::Undefined {
                if let Some(ref expected) = frame_data.accumulated_result {
                    if *expected != current_result {
                        frame_data.rule_failed_due_to_inconsistency = true;
                        if let Some(result_slot) =
                            self.registers.get_mut(usize::from(frame_data.result_reg))
                        {
                            *result_slot = Value::Undefined;
                        }
                    }
                } else {
                    frame_data.accumulated_result = Some(current_result);
                }
            }
        }

        if let Some(definition_bodies) = rule_info
            .definitions
            .get(frame_data.current_definition_index)
        {
            frame_data.current_body_index = definition_bodies.len();
        } else {
            self.increment_counter(&mut frame_data.current_body_index, "rule body index")?;
        }
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

        let rule_idx = usize::from(rule_index);
        let rule_info = self
            .program
            .rule_infos
            .get(rule_idx)
            .ok_or(VmError::RuleInfoMissing {
                index: rule_index,
                pc: self.pc,
                available: self.program.rule_infos.len(),
            })?
            .clone();

        let result_from_rule = if rule_failed_due_to_inconsistency {
            Value::Undefined
        } else if let Some(value) = accumulated_result {
            value
        } else {
            self.registers
                .get(usize::from(result_reg))
                .cloned()
                .unwrap_or(Value::Undefined)
        };

        let mut current_window = Vec::default();
        mem::swap(&mut current_window, &mut self.registers);
        self.return_register_window(current_window);

        self.loop_stack = saved_loop_stack;
        self.comprehension_stack = saved_comprehension_stack;

        let mut parent_registers = saved_registers;
        let dest_idx = usize::from(dest_reg);
        if parent_registers.len() <= dest_idx {
            let new_len = self.checked_add_one(dest_idx, "parent register capacity")?;
            parent_registers.resize(new_len, Value::Undefined);
        }

        {
            let register_count = parent_registers.len();
            let slot =
                parent_registers
                    .get_mut(dest_idx)
                    .ok_or(VmError::RegisterIndexOutOfBounds {
                        index: dest_reg,
                        pc: self.pc,
                        register_count,
                    })?;
            *slot = result_from_rule.clone();
        }

        let needs_default = parent_registers
            .get(dest_idx)
            .is_some_and(|value| *value == Value::Undefined);

        if needs_default && !rule_failed_due_to_inconsistency {
            match rule_type {
                RuleType::PartialSet => {
                    let register_count = parent_registers.len();
                    let slot = parent_registers.get_mut(dest_idx).ok_or(
                        VmError::RegisterIndexOutOfBounds {
                            index: dest_reg,
                            pc: self.pc,
                            register_count,
                        },
                    )?;
                    *slot = Value::new_set();
                }
                RuleType::PartialObject => {
                    let register_count = parent_registers.len();
                    let slot = parent_registers.get_mut(dest_idx).ok_or(
                        VmError::RegisterIndexOutOfBounds {
                            index: dest_reg,
                            pc: self.pc,
                            register_count,
                        },
                    )?;
                    *slot = Value::new_object();
                }
                RuleType::Complete => {
                    if let Some(default_literal_index) = rule_info.default_literal_index {
                        if let Some(default_value) = self
                            .program
                            .literals
                            .get(usize::from(default_literal_index))
                            .cloned()
                        {
                            let register_count = parent_registers.len();
                            let slot = parent_registers.get_mut(dest_idx).ok_or(
                                VmError::RegisterIndexOutOfBounds {
                                    index: dest_reg,
                                    pc: self.pc,
                                    register_count,
                                },
                            )?;
                            *slot = default_value;
                        }
                    }
                }
            }
        }

        let register_count = parent_registers.len();
        let final_value =
            parent_registers
                .get(dest_idx)
                .cloned()
                .ok_or(VmError::RegisterIndexOutOfBounds {
                    index: dest_reg,
                    pc: self.pc,
                    register_count,
                })?;

        if !is_function_rule {
            let available = self.rule_cache.len();
            let entry = self
                .rule_cache
                .get_mut(rule_idx)
                .ok_or(VmError::RuleIndexOutOfBounds {
                    index: rule_index,
                    pc: self.pc,
                    available,
                })?;
            *entry = (true, final_value.clone());
        }

        self.registers = parent_registers;

        if self.call_rule_stack.pop().is_none() {
            return Err(VmError::CallRuleStackUnderflow { pc: self.pc });
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
        let idx = usize::from(rule_index);
        self.program
            .rule_infos
            .get(idx)
            .cloned()
            .ok_or(VmError::RuleInfoMissing {
                index: rule_index,
                pc: self.pc,
                available: self.program.rule_infos.len(),
            })
    }

    pub(super) fn checked_add_one(&self, value: usize, context: &'static str) -> Result<usize> {
        value
            .checked_add(1)
            .ok_or_else(|| VmError::ArithmeticError {
                message: format!("{context} overflow"),
                pc: self.pc,
            })
    }

    pub(super) fn increment_counter(
        &self,
        counter: &mut usize,
        context: &'static str,
    ) -> Result<()> {
        *counter = self.checked_add_one(*counter, context)?;
        Ok(())
    }

    pub(super) fn convert_pc(&self, value: u32, context: &'static str) -> Result<usize> {
        usize::try_from(value).map_err(|_| VmError::ArithmeticError {
            message: format!("{context} exceeds addressable range"),
            pc: self.pc,
        })
    }
}
