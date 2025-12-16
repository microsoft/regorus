// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::LoopMode;
use crate::value::Value;

use super::context::{IterationState, LoopContext};
use super::errors::{Result, VmError};
use super::execution_model::{ExecutionFrame, ExecutionMode, FrameKind};
use super::machine::RegoVM;

fn compute_body_resume_pc(loop_start_pc: usize, body_start: u16) -> usize {
    if body_start == 0 {
        return 0;
    }

    let candidate = body_start.saturating_sub(1) as usize;
    if candidate == loop_start_pc {
        body_start as usize
    } else {
        candidate
    }
}

#[derive(Clone, Copy)]
pub(super) struct LoopParams {
    pub(super) collection: u8,
    pub(super) key_reg: u8,
    pub(super) value_reg: u8,
    pub(super) result_reg: u8,
    pub(super) body_start: u16,
    pub(super) loop_end: u16,
}

#[derive(Debug)]
enum LoopAction {
    ExitWithSuccess,
    ExitWithFailure,
    Continue,
}

impl RegoVM {
    pub(super) fn execute_loop_start(&mut self, mode: &LoopMode, params: LoopParams) -> Result<()> {
        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.execute_loop_start_run_to_completion(mode, params)
            }
            ExecutionMode::Suspendable => self.execute_loop_start_suspendable(mode, params),
        }
    }

    pub(super) fn execute_loop_next(&mut self, body_start: u16, loop_end: u16) -> Result<()> {
        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.execute_loop_next_run_to_completion(body_start, loop_end)
            }
            ExecutionMode::Suspendable => self.execute_loop_next_suspendable(body_start, loop_end),
        }
    }

    pub(super) fn handle_condition(&mut self, condition_passed: bool) -> Result<()> {
        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.handle_condition_run_to_completion(condition_passed)
            }
            ExecutionMode::Suspendable => self.handle_condition_suspendable(condition_passed),
        }
    }

    fn execute_loop_start_run_to_completion(
        &mut self,
        mode: &LoopMode,
        params: LoopParams,
    ) -> Result<()> {
        let initial_result = match mode {
            LoopMode::Any | LoopMode::Every | LoopMode::ForEach => Value::Bool(false),
        };
        self.registers[params.result_reg as usize] = initial_result.clone();

        let collection_value = self.registers[params.collection as usize].clone();

        let iteration_state = match &collection_value {
            Value::Array(items) => {
                if items.is_empty() {
                    self.handle_empty_collection(mode, params.result_reg, params.loop_end)?;
                    return Ok(());
                }
                IterationState::Array {
                    items: items.clone(),
                    index: 0,
                }
            }
            Value::Object(obj) => {
                if obj.is_empty() {
                    self.handle_empty_collection(mode, params.result_reg, params.loop_end)?;
                    return Ok(());
                }
                IterationState::Object {
                    obj: obj.clone(),
                    current_key: None,
                    first_iteration: true,
                }
            }
            Value::Set(set) => {
                if set.is_empty() {
                    self.handle_empty_collection(mode, params.result_reg, params.loop_end)?;
                    return Ok(());
                }
                IterationState::Set {
                    items: set.clone(),
                    current_item: None,
                    first_iteration: true,
                }
            }
            _ => {
                self.handle_empty_collection(mode, params.result_reg, params.loop_end)?;
                return Ok(());
            }
        };

        let has_next =
            self.setup_next_iteration(&iteration_state, params.key_reg, params.value_reg)?;
        if !has_next {
            self.pc = params.loop_end as usize;
            return Ok(());
        }

        let loop_next_pc = params.loop_end - 1;
        let body_resume_pc = compute_body_resume_pc(self.pc, params.body_start);

        let loop_context = LoopContext {
            mode: mode.clone(),
            iteration_state,
            key_reg: params.key_reg,
            value_reg: params.value_reg,
            result_reg: params.result_reg,
            body_start: params.body_start,
            loop_end: params.loop_end,
            loop_next_pc,
            body_resume_pc,
            success_count: 0,
            total_iterations: 0,
            current_iteration_failed: false,
        };

        self.loop_stack.push(loop_context);

        self.pc = params.body_start as usize - 1;

        Ok(())
    }

    fn execute_loop_next_run_to_completion(
        &mut self,
        _body_start: u16,
        loop_end: u16,
    ) -> Result<()> {
        if let Some(mut loop_ctx) = self.loop_stack.pop() {
            let body_start = loop_ctx.body_start;
            let loop_end = loop_ctx.loop_end;

            loop_ctx.total_iterations += 1;

            let iteration_succeeded = self.check_iteration_success(&loop_ctx)?;

            if iteration_succeeded {
                loop_ctx.success_count += 1;
            }

            let action = self.determine_loop_action(&loop_ctx.mode, iteration_succeeded);

            match action {
                LoopAction::ExitWithSuccess => {
                    self.registers[loop_ctx.result_reg as usize] = Value::Bool(true);
                    self.pc = loop_end as usize - 1;
                    return Ok(());
                }
                LoopAction::ExitWithFailure => {
                    self.registers[loop_ctx.result_reg as usize] = Value::Bool(false);
                    self.pc = loop_end as usize - 1;
                    return Ok(());
                }
                LoopAction::Continue => {}
            }

            if let IterationState::Object {
                ref mut current_key,
                ..
            } = &mut loop_ctx.iteration_state
            {
                if loop_ctx.key_reg != loop_ctx.value_reg {
                    *current_key = Some(self.registers[loop_ctx.key_reg as usize].clone());
                }
            } else if let IterationState::Set {
                ref mut current_item,
                ..
            } = &mut loop_ctx.iteration_state
            {
                *current_item = Some(self.registers[loop_ctx.value_reg as usize].clone());
            }

            loop_ctx.iteration_state.advance();
            let has_next = self.setup_next_iteration(
                &loop_ctx.iteration_state,
                loop_ctx.key_reg,
                loop_ctx.value_reg,
            )?;

            if has_next {
                loop_ctx.current_iteration_failed = false;

                self.loop_stack.push(loop_ctx);
                self.pc = body_start as usize - 1;
            } else {
                let final_result = match loop_ctx.mode {
                    LoopMode::Any => Value::Bool(loop_ctx.success_count > 0),
                    LoopMode::Every => {
                        Value::Bool(loop_ctx.success_count == loop_ctx.total_iterations)
                    }
                    LoopMode::ForEach => Value::Bool(loop_ctx.success_count > 0),
                };

                self.registers[loop_ctx.result_reg as usize] = final_result;

                self.pc = loop_end as usize - 1;
            }

            Ok(())
        } else {
            self.pc = loop_end as usize;
            Ok(())
        }
    }

    fn execute_loop_start_suspendable(
        &mut self,
        mode: &LoopMode,
        params: LoopParams,
    ) -> Result<()> {
        let initial_result = match mode {
            LoopMode::Any | LoopMode::Every | LoopMode::ForEach => Value::Bool(false),
        };
        self.registers[params.result_reg as usize] = initial_result.clone();

        let collection_value = self.registers[params.collection as usize].clone();

        let iteration_state = match &collection_value {
            Value::Array(items) => {
                if items.is_empty() {
                    self.handle_empty_collection(mode, params.result_reg, params.loop_end)?;
                    return Ok(());
                }
                IterationState::Array {
                    items: items.clone(),
                    index: 0,
                }
            }
            Value::Object(obj) => {
                if obj.is_empty() {
                    self.handle_empty_collection(mode, params.result_reg, params.loop_end)?;
                    return Ok(());
                }
                IterationState::Object {
                    obj: obj.clone(),
                    current_key: None,
                    first_iteration: true,
                }
            }
            Value::Set(set) => {
                if set.is_empty() {
                    self.handle_empty_collection(mode, params.result_reg, params.loop_end)?;
                    return Ok(());
                }
                IterationState::Set {
                    items: set.clone(),
                    current_item: None,
                    first_iteration: true,
                }
            }
            _ => {
                self.handle_empty_collection(mode, params.result_reg, params.loop_end)?;
                return Ok(());
            }
        };

        let has_next =
            self.setup_next_iteration(&iteration_state, params.key_reg, params.value_reg)?;
        if !has_next {
            self.pc = params.loop_end as usize;
            return Ok(());
        }

        let loop_next_pc = params.loop_end - 1;
        let body_resume_pc = compute_body_resume_pc(self.pc, params.body_start);

        let loop_context = LoopContext {
            mode: mode.clone(),
            iteration_state,
            key_reg: params.key_reg,
            value_reg: params.value_reg,
            result_reg: params.result_reg,
            body_start: params.body_start,
            loop_end: params.loop_end,
            loop_next_pc,
            body_resume_pc,
            success_count: 0,
            total_iterations: 0,
            current_iteration_failed: false,
        };

        let frame = ExecutionFrame::new(
            params.body_start as usize,
            FrameKind::Loop {
                return_pc: params.loop_end as usize,
                context: loop_context,
            },
        );
        self.execution_stack.push(frame);

        Ok(())
    }

    fn execute_loop_next_suspendable(&mut self, body_start: u16, loop_end: u16) -> Result<()> {
        if !matches!(
            self.execution_stack.last(),
            Some(ExecutionFrame {
                kind: FrameKind::Loop { .. },
                ..
            })
        ) {
            if let Some(frame) = self.execution_stack.last_mut() {
                // Advance past the offending instruction so we do not repeatedly
                // resume at the same LoopNext when the owning loop frame has
                // already been popped (for example after a manual comprehension
                // finalizes in suspendable mode).
                let mut target_pc = loop_end as usize;
                if target_pc <= self.pc {
                    target_pc = self.pc.saturating_add(1);
                }
                frame.pc = target_pc;
                self.frame_pc_overridden = true;
            }
            return Ok(());
        }

        let (resume_pc, result_reg, loop_mode, iteration_succeeded) = {
            let frame = self
                .execution_stack
                .last_mut()
                .ok_or(VmError::AssertionFailed)?;
            match &mut frame.kind {
                FrameKind::Loop { return_pc, context } => {
                    context.total_iterations += 1;
                    let succeeded = !context.current_iteration_failed;
                    if succeeded {
                        context.success_count += 1;
                    }

                    (
                        *return_pc,
                        context.result_reg,
                        context.mode.clone(),
                        succeeded,
                    )
                }
                _ => return Err(VmError::AssertionFailed),
            }
        };

        let action = self.determine_loop_action(&loop_mode, iteration_succeeded);

        match action {
            LoopAction::ExitWithSuccess => {
                self.registers[result_reg as usize] = Value::Bool(true);
                let completed_frame = self.execution_stack.pop().expect("loop frame exists");
                if let Some(parent) = self.execution_stack.last_mut() {
                    parent.pc = resume_pc;
                    self.frame_pc_overridden = true;
                }
                drop(completed_frame);
                Ok(())
            }
            LoopAction::ExitWithFailure => {
                self.registers[result_reg as usize] = Value::Bool(false);
                let completed_frame = self.execution_stack.pop().expect("loop frame exists");
                if let Some(parent) = self.execution_stack.last_mut() {
                    parent.pc = resume_pc;
                    self.frame_pc_overridden = true;
                }
                drop(completed_frame);
                Ok(())
            }
            LoopAction::Continue => {
                let (mode, success_count, total_iterations, key_reg, value_reg, iteration_state) = {
                    let frame = self
                        .execution_stack
                        .last_mut()
                        .ok_or(VmError::AssertionFailed)?;
                    match &mut frame.kind {
                        FrameKind::Loop { context, .. } => {
                            if let IterationState::Object {
                                ref mut current_key,
                                ..
                            } = &mut context.iteration_state
                            {
                                if context.key_reg != context.value_reg {
                                    *current_key =
                                        Some(self.registers[context.key_reg as usize].clone());
                                }
                            } else if let IterationState::Set {
                                ref mut current_item,
                                ..
                            } = &mut context.iteration_state
                            {
                                *current_item =
                                    Some(self.registers[context.value_reg as usize].clone());
                            }

                            context.iteration_state.advance();
                            context.current_iteration_failed = false;

                            (
                                context.mode.clone(),
                                context.success_count,
                                context.total_iterations,
                                context.key_reg,
                                context.value_reg,
                                context.iteration_state.clone(),
                            )
                        }
                        _ => return Err(VmError::AssertionFailed),
                    }
                };

                let has_next = self.setup_next_iteration(&iteration_state, key_reg, value_reg)?;

                if has_next {
                    if let Some(frame) = self.execution_stack.last_mut() {
                        if let FrameKind::Loop { context, .. } = &frame.kind {
                            frame.pc = context.body_resume_pc;
                        } else {
                            frame.pc = body_start as usize;
                        }
                        self.frame_pc_overridden = true;
                    }
                    Ok(())
                } else {
                    let final_result = match mode {
                        LoopMode::Any => Value::Bool(success_count > 0),
                        LoopMode::Every => Value::Bool(success_count == total_iterations),
                        LoopMode::ForEach => Value::Bool(success_count > 0),
                    };

                    self.registers[result_reg as usize] = final_result;

                    let completed_frame = self.execution_stack.pop().expect("loop frame exists");
                    if let Some(parent) = self.execution_stack.last_mut() {
                        parent.pc = resume_pc;
                        self.frame_pc_overridden = true;
                    }
                    drop(completed_frame);

                    Ok(())
                }
            }
        }
    }

    fn handle_empty_collection(
        &mut self,
        mode: &LoopMode,
        result_reg: u8,
        loop_end: u16,
    ) -> Result<()> {
        let result = match mode {
            LoopMode::Any => Value::Bool(false),
            LoopMode::Every => Value::Bool(true),
            LoopMode::ForEach => Value::Bool(false),
        };

        self.registers[result_reg as usize] = result;
        self.pc = (loop_end as usize).saturating_sub(1);
        Ok(())
    }

    pub(super) fn setup_next_iteration(
        &mut self,
        state: &IterationState,
        key_reg: u8,
        value_reg: u8,
    ) -> Result<bool> {
        match state {
            IterationState::Array { items, index } => {
                if *index < items.len() {
                    if key_reg != value_reg {
                        let key_value = Value::from(*index as f64);
                        self.registers[key_reg as usize] = key_value;
                    }
                    let item_value = items[*index].clone();
                    self.registers[value_reg as usize] = item_value;
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            IterationState::Object {
                obj,
                current_key,
                first_iteration,
            } => {
                if *first_iteration {
                    if let Some((key, value)) = obj.iter().next() {
                        if key_reg != value_reg {
                            self.registers[key_reg as usize] = key.clone();
                        }
                        self.registers[value_reg as usize] = value.clone();
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                } else if let Some(ref current) = current_key {
                    let mut range_iter = obj.range((
                        core::ops::Bound::Excluded(current),
                        core::ops::Bound::Unbounded,
                    ));
                    if let Some((key, value)) = range_iter.next() {
                        if key_reg != value_reg {
                            self.registers[key_reg as usize] = key.clone();
                        }
                        self.registers[value_reg as usize] = value.clone();
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
            IterationState::Set {
                items,
                current_item,
                first_iteration,
            } => {
                if *first_iteration {
                    if let Some(item) = items.iter().next() {
                        if key_reg != value_reg {
                            self.registers[key_reg as usize] = item.clone();
                        }
                        self.registers[value_reg as usize] = item.clone();
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                } else if let Some(ref current) = current_item {
                    let mut range_iter = items.range((
                        core::ops::Bound::Excluded(current),
                        core::ops::Bound::Unbounded,
                    ));
                    if let Some(item) = range_iter.next() {
                        if key_reg != value_reg {
                            self.registers[key_reg as usize] = item.clone();
                        }
                        self.registers[value_reg as usize] = item.clone();
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                } else {
                    Ok(false)
                }
            }
        }
    }

    fn check_iteration_success(&self, loop_ctx: &LoopContext) -> Result<bool> {
        Ok(!loop_ctx.current_iteration_failed)
    }

    fn determine_loop_action(&self, mode: &LoopMode, success: bool) -> LoopAction {
        match (mode, success) {
            (LoopMode::Any, true) => LoopAction::ExitWithSuccess,
            (LoopMode::Every, false) => LoopAction::ExitWithFailure,
            (LoopMode::ForEach, _) => LoopAction::Continue,
            _ => LoopAction::Continue,
        }
    }

    fn handle_condition_run_to_completion(&mut self, condition_passed: bool) -> Result<()> {
        if condition_passed {
            return Ok(());
        }

        if !self.loop_stack.is_empty() {
            let (loop_mode, loop_next_pc, loop_end, result_reg) = {
                let loop_ctx = self.loop_stack.last().unwrap();
                (
                    loop_ctx.mode.clone(),
                    loop_ctx.loop_next_pc,
                    loop_ctx.loop_end,
                    loop_ctx.result_reg,
                )
            };

            match loop_mode {
                LoopMode::Any => {
                    if let Some(loop_ctx_mut) = self.loop_stack.last_mut() {
                        loop_ctx_mut.current_iteration_failed = true;
                    }

                    self.pc = loop_next_pc as usize - 1;
                }
                LoopMode::Every => {
                    self.loop_stack.pop();
                    self.pc = loop_end as usize - 1;
                    self.registers[result_reg as usize] = Value::Bool(false);
                }
                _ => {
                    if let Some(loop_ctx_mut) = self.loop_stack.last_mut() {
                        loop_ctx_mut.current_iteration_failed = true;
                    }
                    self.pc = loop_next_pc as usize - 1;
                }
            }
        } else if self.handle_comprehension_condition_failure_run_to_completion()? {
            // handled by comprehension context
        } else {
            return Err(VmError::AssertionFailed);
        }

        Ok(())
    }

    fn handle_condition_suspendable(&mut self, condition_passed: bool) -> Result<()> {
        if condition_passed {
            return Ok(());
        }

        if let Some(ExecutionFrame {
            kind: FrameKind::Loop { return_pc, context },
            ..
        }) = self.execution_stack.last_mut()
        {
            let resume_pc = *return_pc;
            match context.mode {
                LoopMode::Any | LoopMode::ForEach => {
                    context.current_iteration_failed = true;
                    self.pc = context.loop_next_pc as usize - 1;
                }
                LoopMode::Every => {
                    self.registers[context.result_reg as usize] = Value::Bool(false);
                    let completed_frame = self.execution_stack.pop().expect("loop frame exists");
                    if let Some(parent) = self.execution_stack.last_mut() {
                        parent.pc = resume_pc;
                    }
                    drop(completed_frame);
                }
            }
            Ok(())
        } else if self.handle_comprehension_condition_failure_suspendable()? {
            Ok(())
        } else {
            Err(VmError::AssertionFailed)
        }
    }
}
