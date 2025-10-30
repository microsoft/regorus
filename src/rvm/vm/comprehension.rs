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
        self.registers[params.result_reg as usize] = initial_result.clone();

        let auto_iterate = params.collection_reg != params.result_reg;
        let iteration_state = if auto_iterate {
            let source_value = self.registers[params.collection_reg as usize].clone();
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

        let mut has_iteration = false;
        if let Some(state) = iteration_state.as_ref() {
            has_iteration = self.setup_next_iteration(state, params.key_reg, params.value_reg)?;
        }

        let resume_pc = if auto_iterate {
            params.comprehension_end as usize
        } else {
            params.comprehension_end.saturating_sub(1) as usize
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
                self.pc = params.body_start as usize - 1;
            } else {
                comprehension_context.iteration_state = None;
                self.pc = params.comprehension_end as usize - 1;
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
        self.registers[params.result_reg as usize] = initial_result.clone();

        let auto_iterate = params.collection_reg != params.result_reg;
        let iteration_state = if auto_iterate {
            let source_value = self.registers[params.collection_reg as usize].clone();
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
            params.comprehension_end as usize
        } else {
            params.comprehension_end.saturating_sub(1) as usize
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
                params.body_start as usize
            } else {
                comprehension_context.iteration_state = None;
                params.comprehension_end as usize
            }
        } else {
            self.pc + 1
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
            });
        };

        let value_to_add = self.registers[value_reg as usize].clone();
        let key_value = if let Some(key_reg) = key_reg {
            Some(self.registers[key_reg as usize].clone())
        } else if matches!(comprehension_context.mode, ComprehensionMode::Object) {
            Some(self.registers[comprehension_context.key_reg as usize].clone())
        } else {
            None
        };

        let result_reg = comprehension_context.result_reg as usize;
        let current_result = self.registers[result_reg].clone();
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
                    });
                }
            }
            (_mode, other) => {
                self.comprehension_stack.push(comprehension_context);
                return Err(VmError::InvalidIteration { value: other });
            }
        };

        self.registers[result_reg] = updated_result;

        if let Some(iter_state) = comprehension_context.iteration_state.as_mut() {
            match iter_state {
                IterationState::Object { current_key, .. } => {
                    let tracked_key =
                        if comprehension_context.key_reg != comprehension_context.value_reg {
                            self.registers[comprehension_context.key_reg as usize].clone()
                        } else {
                            self.registers[comprehension_context.value_reg as usize].clone()
                        };
                    *current_key = Some(tracked_key);
                }
                IterationState::Set { current_item, .. } => {
                    *current_item =
                        Some(self.registers[comprehension_context.value_reg as usize].clone());
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
                self.pc = comprehension_context.body_start as usize - 1;
            } else {
                comprehension_context.iteration_state = None;
                self.pc = comprehension_context.comprehension_end as usize - 1;
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
            })?;

        let (iteration_state_snapshot, key_reg_idx, value_reg_idx, body_start, comprehension_end) = {
            let frame = self.execution_stack.get_mut(comprehension_index).ok_or(
                VmError::InvalidIteration {
                    value: Value::String(Arc::from("No active comprehension")),
                },
            )?;

            match &mut frame.kind {
                FrameKind::Comprehension { context, .. } => {
                    let value_to_add = self.registers[value_reg as usize].clone();
                    let key_value = if let Some(key_reg) = key_reg {
                        Some(self.registers[key_reg as usize].clone())
                    } else if matches!(context.mode, ComprehensionMode::Object) {
                        Some(self.registers[context.key_reg as usize].clone())
                    } else {
                        None
                    };

                    let result_reg_idx = context.result_reg as usize;
                    let current_result = self.registers[result_reg_idx].clone();
                    let mode = context.mode.clone();

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
                                    value: Value::String(Arc::from(
                                        "Object comprehension requires key",
                                    )),
                                });
                            }
                        }
                        (_mode, other) => {
                            return Err(VmError::InvalidIteration { value: other });
                        }
                    };

                    self.registers[result_reg_idx] = updated_result;

                    if let Some(iter_state) = context.iteration_state.as_mut() {
                        match iter_state {
                            IterationState::Object { current_key, .. } => {
                                let tracked_key = if context.key_reg != context.value_reg {
                                    self.registers[context.key_reg as usize].clone()
                                } else {
                                    self.registers[context.value_reg as usize].clone()
                                };
                                *current_key = Some(tracked_key);
                            }
                            IterationState::Set { current_item, .. } => {
                                *current_item =
                                    Some(self.registers[context.value_reg as usize].clone());
                            }
                            IterationState::Array { .. } => {}
                        }

                        iter_state.advance();
                    }

                    (
                        context.iteration_state.clone(),
                        context.key_reg,
                        context.value_reg,
                        context.body_start,
                        context.comprehension_end,
                    )
                }
                _ => {
                    return Err(VmError::InvalidIteration {
                        value: Value::String(Arc::from("No active comprehension")),
                    });
                }
            }
        };

        if let Some(state) = iteration_state_snapshot.as_ref() {
            let has_next = self.setup_next_iteration(state, key_reg_idx, value_reg_idx)?;

            if has_next {
                if let Some(frame) = self.execution_stack.get_mut(comprehension_index) {
                    frame.pc = body_start as usize;
                    self.frame_pc_overridden = true;
                }
            } else if let Some(frame) = self.execution_stack.get_mut(comprehension_index) {
                if let FrameKind::Comprehension { context, .. } = &mut frame.kind {
                    context.iteration_state = None;
                }
                frame.pc = comprehension_end as usize;
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

    fn execute_comprehension_end_run_to_completion(&mut self) -> Result<()> {
        if let Some(_context) = self.comprehension_stack.pop() {
            Ok(())
        } else {
            Err(VmError::InvalidIteration {
                value: Value::String(Arc::from("No active comprehension context")),
            })
        }
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
                    });
                }
            }
        }
    }
}
