// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::{ComprehensionBeginParams, ComprehensionMode};
use crate::value::Value;
use crate::Rc;
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::sync::Arc;
use alloc::vec::Vec;

use super::context::{ComprehensionContext, IterationState};
use super::errors::{Result, VmError};
use super::execution_model::{ExecutionFrame, ExecutionMode, FrameKind};
use super::machine::RegoVM;

impl RegoVM {
    pub(super) fn execute_comprehension_begin(
        &mut self,
        params: &ComprehensionBeginParams,
    ) -> Result<()> {
        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.execute_comprehension_begin_run_to_completion(params)
            }
            ExecutionMode::Suspendable => self.execute_comprehension_begin_suspendable(params),
        }
    }

    fn execute_comprehension_begin_run_to_completion(
        &mut self,
        params: &ComprehensionBeginParams,
    ) -> Result<()> {
        let initial_result = match params.mode {
            ComprehensionMode::Set => Value::new_set(),
            ComprehensionMode::Array => Value::new_array(),
            ComprehensionMode::Object => Value::Object(Rc::new(BTreeMap::new())),
        };
        self.set_register(params.result_reg, initial_result.clone())?;

        let auto_iterate = params.collection_reg != params.result_reg;
        let iteration_state = if auto_iterate {
            let source_value = self.get_register(params.collection_reg)?.clone();
            match source_value {
                Value::Array(items) => {
                    if items.is_empty() {
                        None
                    } else {
                        Some(IterationState::Array { items, index: 0 })
                    }
                }
                Value::Object(obj) => {
                    if obj.is_empty() {
                        None
                    } else {
                        Some(IterationState::Object {
                            obj,
                            current_key: None,
                            first_iteration: true,
                        })
                    }
                }
                Value::Set(set) => {
                    if set.is_empty() {
                        None
                    } else {
                        Some(IterationState::Set {
                            items: set,
                            current_item: None,
                            first_iteration: true,
                        })
                    }
                }
                Value::Undefined => None,
                Value::Null => None,
                _ => None,
            }
        } else {
            None
        };

        let has_iteration = if let Some(state) = iteration_state.as_ref() {
            self.setup_next_iteration(state, params.key_reg, params.value_reg)?
        } else {
            false
        };

        let resume_pc = if auto_iterate {
            usize::from(params.comprehension_end)
        } else {
            usize::from(params.comprehension_end.saturating_sub(1))
        };

        let mut comprehension_context = ComprehensionContext {
            mode: params.mode.clone(),
            result_reg: params.result_reg,
            key_reg: params.key_reg,
            value_reg: params.value_reg,
            body_start: params.body_start,
            comprehension_end: params.comprehension_end,
            iteration_state,
            resume_pc,
        };

        if auto_iterate {
            if has_iteration {
                self.pc = usize::from(params.body_start).saturating_sub(1);
            } else {
                comprehension_context.iteration_state = None;
                self.pc = usize::from(params.comprehension_end).saturating_sub(1);
            }
        }

        self.comprehension_stack.push(comprehension_context);

        Ok(())
    }

    fn execute_comprehension_begin_suspendable(
        &mut self,
        params: &ComprehensionBeginParams,
    ) -> Result<()> {
        let initial_result = match params.mode {
            ComprehensionMode::Set => Value::new_set(),
            ComprehensionMode::Array => Value::new_array(),
            ComprehensionMode::Object => Value::Object(Rc::new(BTreeMap::new())),
        };
        self.set_register(params.result_reg, initial_result.clone())?;

        let auto_iterate = params.collection_reg != params.result_reg;
        let iteration_state = if auto_iterate {
            let source_value = self.get_register(params.collection_reg)?.clone();
            match source_value {
                Value::Array(items) => {
                    if items.is_empty() {
                        None
                    } else {
                        Some(IterationState::Array { items, index: 0 })
                    }
                }
                Value::Object(obj) => {
                    if obj.is_empty() {
                        None
                    } else {
                        Some(IterationState::Object {
                            obj,
                            current_key: None,
                            first_iteration: true,
                        })
                    }
                }
                Value::Set(set) => {
                    if set.is_empty() {
                        None
                    } else {
                        Some(IterationState::Set {
                            items: set,
                            current_item: None,
                            first_iteration: true,
                        })
                    }
                }
                Value::Undefined => None,
                Value::Null => None,
                _ => None,
            }
        } else {
            None
        };

        let has_iteration = if let Some(state) = iteration_state.as_ref() {
            self.setup_next_iteration(state, params.key_reg, params.value_reg)?
        } else {
            false
        };

        let resume_pc = if auto_iterate {
            usize::from(params.comprehension_end)
        } else {
            usize::from(params.comprehension_end.saturating_sub(1))
        };

        let mut comprehension_context = ComprehensionContext {
            mode: params.mode.clone(),
            result_reg: params.result_reg,
            key_reg: params.key_reg,
            value_reg: params.value_reg,
            body_start: params.body_start,
            comprehension_end: params.comprehension_end,
            iteration_state,
            resume_pc,
        };

        let next_pc = if auto_iterate {
            if has_iteration {
                usize::from(params.body_start)
            } else {
                comprehension_context.iteration_state = None;
                usize::from(params.comprehension_end)
            }
        } else {
            self.pc.saturating_add(1)
        };

        let return_pc = comprehension_context.resume_pc;

        let frame = ExecutionFrame::new(
            next_pc,
            FrameKind::Comprehension {
                return_pc,
                context: comprehension_context,
            },
        );
        self.execution_stack.push(frame);

        Ok(())
    }

    pub(super) fn execute_comprehension_yield(
        &mut self,
        value_reg: u8,
        key_reg: Option<u8>,
    ) -> Result<()> {
        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.execute_comprehension_yield_run_to_completion(value_reg, key_reg)
            }
            ExecutionMode::Suspendable => {
                self.execute_comprehension_yield_suspendable(value_reg, key_reg)
            }
        }
    }

    fn execute_comprehension_yield_run_to_completion(
        &mut self,
        value_reg: u8,
        key_reg: Option<u8>,
    ) -> Result<()> {
        let mut comprehension_context = if let Some(context) = self.comprehension_stack.pop() {
            context
        } else {
            return Err(VmError::InvalidIteration {
                value: Value::String(Arc::from("No active comprehension")),
                pc: self.pc,
            });
        };

        let value_to_add = self.get_register(value_reg)?.clone();
        let key_value = if let Some(key_reg) = key_reg {
            Some(self.get_register(key_reg)?.clone())
        } else if matches!(comprehension_context.mode, ComprehensionMode::Object) {
            Some(self.get_register(comprehension_context.key_reg)?.clone())
        } else {
            None
        };

        let result_reg = comprehension_context.result_reg;
        let current_result = self.get_register(result_reg)?.clone();
        let mode = comprehension_context.mode.clone();

        let updated_result = match (mode, current_result) {
            (ComprehensionMode::Set, Value::Set(set)) => {
                let mut new_set = set.as_ref().clone();
                new_set.insert(value_to_add);
                Value::Set(crate::Rc::new(new_set))
            }
            (ComprehensionMode::Array, Value::Array(arr)) => {
                let mut new_arr = arr.as_ref().to_vec();
                new_arr.push(value_to_add);
                Value::Array(crate::Rc::new(new_arr))
            }
            (ComprehensionMode::Object, Value::Object(obj)) => {
                if let Some(key) = key_value {
                    let mut new_obj = obj.as_ref().clone();
                    new_obj.insert(key, value_to_add);
                    Value::Object(crate::Rc::new(new_obj))
                } else {
                    self.comprehension_stack.push(comprehension_context);
                    return Err(VmError::InvalidIteration {
                        value: Value::String(Arc::from("Object comprehension requires key")),
                        pc: self.pc,
                    });
                }
            }
            (_mode, other) => {
                self.comprehension_stack.push(comprehension_context);
                return Err(VmError::InvalidIteration {
                    value: other,
                    pc: self.pc,
                });
            }
        };

        self.set_register(result_reg, updated_result)?;

        if let Some(iter_state) = comprehension_context.iteration_state.as_mut() {
            match *iter_state {
                IterationState::Object {
                    ref mut current_key,
                    ..
                } => {
                    let tracked_key =
                        if comprehension_context.key_reg != comprehension_context.value_reg {
                            self.get_register(comprehension_context.key_reg)?.clone()
                        } else {
                            self.get_register(comprehension_context.value_reg)?.clone()
                        };
                    *current_key = Some(tracked_key);
                }
                IterationState::Set {
                    ref mut current_item,
                    ..
                } => {
                    *current_item =
                        Some(self.get_register(comprehension_context.value_reg)?.clone());
                }
                IterationState::Array { .. } => {}
            }

            iter_state.advance();
            let has_next = self.setup_next_iteration(
                iter_state,
                comprehension_context.key_reg,
                comprehension_context.value_reg,
            )?;

            if has_next {
                self.pc = usize::from(comprehension_context.body_start).saturating_sub(1);
            } else {
                comprehension_context.iteration_state = None;
                self.pc = usize::from(comprehension_context.comprehension_end).saturating_sub(1);
            }
        }

        self.comprehension_stack.push(comprehension_context);

        Ok(())
    }

    fn execute_comprehension_yield_suspendable(
        &mut self,
        value_reg: u8,
        key_reg: Option<u8>,
    ) -> Result<()> {
        let comprehension_index = (0..self.execution_stack.len())
            .rev()
            .find(|&idx| {
                self.execution_stack
                    .get(idx)
                    .is_some_and(|frame| matches!(frame.kind, FrameKind::Comprehension { .. }))
            })
            .ok_or(VmError::InvalidIteration {
                value: Value::String(Arc::from("No active comprehension")),
                pc: self.pc,
            })?;

        let (
            value_to_add,
            key_value,
            current_result,
            mode,
            result_reg_idx,
            key_reg_idx,
            value_reg_idx,
            iteration_key,
            iteration_value,
        ) = {
            let frame =
                self.execution_stack
                    .get(comprehension_index)
                    .ok_or(VmError::InvalidIteration {
                        value: Value::String(Arc::from("No active comprehension")),
                        pc: self.pc,
                    })?;

            if let FrameKind::Comprehension { ref context, .. } = frame.kind {
                let value_to_add = self.get_register(value_reg)?.clone();
                let key_value = if let Some(key_reg) = key_reg {
                    Some(self.get_register(key_reg)?.clone())
                } else if matches!(context.mode, ComprehensionMode::Object) {
                    Some(self.get_register(context.key_reg)?.clone())
                } else {
                    None
                };

                let result_reg_idx = context.result_reg;
                let current_result = self.get_register(result_reg_idx)?.clone();
                let mode = context.mode.clone();
                let iteration_key = self.get_register(context.key_reg)?.clone();
                let iteration_value = self.get_register(context.value_reg)?.clone();

                (
                    value_to_add,
                    key_value,
                    current_result,
                    mode,
                    result_reg_idx,
                    context.key_reg,
                    context.value_reg,
                    iteration_key,
                    iteration_value,
                )
            } else {
                return Err(VmError::InvalidIteration {
                    value: Value::String(Arc::from("No active comprehension")),
                    pc: self.pc,
                });
            }
        };

        let updated_result = match (mode, current_result) {
            (ComprehensionMode::Set, Value::Set(set)) => {
                let mut new_set = set.as_ref().clone();
                new_set.insert(value_to_add);
                Value::Set(crate::Rc::new(new_set))
            }
            (ComprehensionMode::Array, Value::Array(arr)) => {
                let mut new_arr = arr.as_ref().to_vec();
                new_arr.push(value_to_add);
                Value::Array(crate::Rc::new(new_arr))
            }
            (ComprehensionMode::Object, Value::Object(obj)) => {
                if let Some(key) = key_value {
                    let mut new_obj = obj.as_ref().clone();
                    new_obj.insert(key, value_to_add);
                    Value::Object(crate::Rc::new(new_obj))
                } else {
                    return Err(VmError::InvalidIteration {
                        value: Value::String(Arc::from("Object comprehension requires key")),
                        pc: self.pc,
                    });
                }
            }
            (_mode, other) => {
                return Err(VmError::InvalidIteration {
                    value: other,
                    pc: self.pc,
                });
            }
        };

        let (iteration_state_snapshot, body_start, comprehension_end) = {
            let frame = self.execution_stack.get_mut(comprehension_index).ok_or(
                VmError::InvalidIteration {
                    value: Value::String(Arc::from("No active comprehension")),
                    pc: self.pc,
                },
            )?;

            if let &mut FrameKind::Comprehension {
                ref mut context, ..
            } = &mut frame.kind
            {
                if let Some(iter_state) = context.iteration_state.as_mut() {
                    match *iter_state {
                        IterationState::Object {
                            ref mut current_key,
                            ..
                        } => {
                            let tracked_key = if context.key_reg != context.value_reg {
                                iteration_key.clone()
                            } else {
                                iteration_value.clone()
                            };
                            *current_key = Some(tracked_key);
                        }
                        IterationState::Set {
                            ref mut current_item,
                            ..
                        } => {
                            *current_item = Some(iteration_value.clone());
                        }
                        IterationState::Array { .. } => {}
                    }

                    iter_state.advance();
                }

                (
                    context.iteration_state.clone(),
                    context.body_start,
                    context.comprehension_end,
                )
            } else {
                return Err(VmError::InvalidIteration {
                    value: Value::String(Arc::from("No active comprehension")),
                    pc: self.pc,
                });
            }
        };

        self.set_register(result_reg_idx, updated_result)?;

        if let Some(state) = iteration_state_snapshot.as_ref() {
            let has_next = self.setup_next_iteration(state, key_reg_idx, value_reg_idx)?;

            if has_next {
                if let Some(frame) = self.execution_stack.get_mut(comprehension_index) {
                    frame.pc = usize::from(body_start);
                    self.frame_pc_overridden = true;
                }
            } else if let Some(frame) = self.execution_stack.get_mut(comprehension_index) {
                if let &mut FrameKind::Comprehension {
                    ref mut context, ..
                } = &mut frame.kind
                {
                    context.iteration_state = None;
                }
                frame.pc = usize::from(comprehension_end);
                self.frame_pc_overridden = true;
            }
        }

        Ok(())
    }

    pub(super) fn execute_comprehension_end(&mut self) -> Result<()> {
        match self.execution_mode {
            ExecutionMode::RunToCompletion => self.execute_comprehension_end_run_to_completion(),
            ExecutionMode::Suspendable => self.execute_comprehension_end_suspendable(),
        }
    }

    pub(super) fn handle_comprehension_condition_failure_run_to_completion(
        &mut self,
    ) -> Result<bool> {
        if let Some(mut context) = self.comprehension_stack.pop() {
            self.advance_comprehension_after_failure(&mut context)?;
            self.comprehension_stack.push(context);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub(super) fn handle_comprehension_condition_failure_suspendable(&mut self) -> Result<bool> {
        if let Some(mut frame) = self.execution_stack.pop() {
            let handled = if let &mut FrameKind::Comprehension {
                ref mut context, ..
            } = &mut frame.kind
            {
                self.advance_comprehension_after_failure(context)?;
                true
            } else {
                false
            };

            self.execution_stack.push(frame);
            if handled {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn advance_comprehension_after_failure(
        &mut self,
        context: &mut ComprehensionContext,
    ) -> Result<()> {
        if let Some(iter_state) = context.iteration_state.as_mut() {
            self.capture_comprehension_iteration_position(
                iter_state,
                context.key_reg,
                context.value_reg,
            )?;
            iter_state.advance();
            let has_next =
                self.setup_next_iteration(iter_state, context.key_reg, context.value_reg)?;
            if has_next {
                self.pc = usize::from(context.body_start.saturating_sub(1));
            } else {
                context.iteration_state = None;
                self.pc = usize::from(context.comprehension_end.saturating_sub(1));
            }
        } else {
            self.pc = usize::from(context.comprehension_end.saturating_sub(1));
        }

        Ok(())
    }

    fn capture_comprehension_iteration_position(
        &mut self,
        iter_state: &mut IterationState,
        key_reg: u8,
        value_reg: u8,
    ) -> Result<()> {
        match *iter_state {
            IterationState::Object {
                ref mut current_key,
                ..
            } => {
                let tracked_key = if key_reg != value_reg {
                    self.get_register(key_reg)?.clone()
                } else {
                    self.get_register(value_reg)?.clone()
                };
                *current_key = Some(tracked_key);
            }
            IterationState::Set {
                ref mut current_item,
                ..
            } => {
                *current_item = Some(self.get_register(value_reg)?.clone());
            }
            IterationState::Array { .. } => {}
        }

        Ok(())
    }

    fn execute_comprehension_end_run_to_completion(&mut self) -> Result<()> {
        self.comprehension_stack.pop().map_or_else(
            || {
                Err(VmError::InvalidIteration {
                    value: Value::String(Arc::from("No active comprehension context")),
                    pc: self.pc,
                })
            },
            |_context| Ok(()),
        )
    }

    fn execute_comprehension_end_suspendable(&mut self) -> Result<()> {
        let mut unwound_frames: Vec<ExecutionFrame> = Vec::new();

        loop {
            let frame = match self.execution_stack.pop() {
                Some(frame) => frame,
                None => {
                    // Restore any frames we already unwound before propagating the error.
                    while let Some(restored) = unwound_frames.pop() {
                        self.execution_stack.push(restored);
                    }
                    return Err(VmError::InvalidIteration {
                        value: Value::String(Arc::from("No active comprehension context")),
                        pc: self.pc,
                    });
                }
            };

            let ExecutionFrame {
                pc: frame_pc,
                kind: frame_kind,
            } = frame;

            match frame_kind {
                FrameKind::Comprehension {
                    return_pc: _,
                    context,
                } => {
                    let raw_target = context.resume_pc;
                    let resume_pc = if raw_target <= self.pc {
                        self.pc.saturating_add(1)
                    } else if raw_target == self.pc.saturating_add(1) {
                        raw_target
                    } else {
                        raw_target.saturating_sub(1)
                    };
                    if let Some(parent) = self.execution_stack.last_mut() {
                        parent.pc = resume_pc;
                    }
                    while let Some(restored) = unwound_frames.pop() {
                        self.execution_stack.push(restored);
                    }
                    return Ok(());
                }
                FrameKind::Loop { return_pc, context } => {
                    if let Some(parent) = self.execution_stack.last_mut() {
                        parent.pc = return_pc;
                    }
                    // Keep the loop frame available so we can restore it if we discover a mismatch.
                    unwound_frames.push(ExecutionFrame::new(
                        frame_pc,
                        FrameKind::Loop { return_pc, context },
                    ));
                }
                other_kind => {
                    let message = format!(
                        "Mismatched comprehension frame: frame={:?} stack_depth={} unwound_loops={}",
                        &other_kind,
                        self.execution_stack.len(),
                        unwound_frames.len()
                    );
                    // Put the unexpected frame back on the stack along with any loops we unwound.
                    self.execution_stack
                        .push(ExecutionFrame::new(frame_pc, other_kind));
                    while let Some(restored) = unwound_frames.pop() {
                        self.execution_stack.push(restored);
                    }
                    return Err(VmError::InvalidIteration {
                        value: Value::String(Arc::from(message.into_boxed_str())),
                        pc: self.pc,
                    });
                }
            }
        }
    }
}
