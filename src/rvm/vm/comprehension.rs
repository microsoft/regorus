// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::{ComprehensionBeginParams, ComprehensionMode};
use crate::value::Object;
use crate::value::Value;
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
            ComprehensionMode::Object => Object::new().into_value(),
        };
        self.set_register(params.result_reg, initial_result.clone())?;

        let auto_iterate = params.collection_reg != params.result_reg;
        let mut iteration_state = if auto_iterate {
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
                        // O(1) cursor over shared Rc<Object>.
                        let cursor = obj.cursor();
                        Some(IterationState::Object { obj, cursor })
                    }
                }
                Value::Set(set) => {
                    if set.is_empty() {
                        None
                    } else {
                        let cursor = set.cursor();
                        Some(IterationState::Set { items: set, cursor })
                    }
                }
                Value::Undefined => None,
                Value::Null => None,
                _ => None,
            }
        } else {
            None
        };

        let has_iteration = if let Some(state) = iteration_state.as_mut() {
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
            #[cfg(feature = "explanations")]
            has_assumption_dependent_yield: false,
            #[cfg(feature = "explanations")]
            assumptions_count_at_start: self.trace.assumptions.len(),
            #[cfg(feature = "explanations")]
            input_provenance_hint: None,
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
            ComprehensionMode::Object => Object::new().into_value(),
        };
        self.set_register(params.result_reg, initial_result.clone())?;

        let auto_iterate = params.collection_reg != params.result_reg;
        let mut iteration_state = if auto_iterate {
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
                        let cursor = obj.cursor();
                        Some(IterationState::Object { obj, cursor })
                    }
                }
                Value::Set(set) => {
                    if set.is_empty() {
                        None
                    } else {
                        let cursor = set.cursor();
                        Some(IterationState::Set { items: set, cursor })
                    }
                }
                Value::Undefined => None,
                Value::Null => None,
                _ => None,
            }
        } else {
            None
        };

        let has_iteration = if let Some(state) = iteration_state.as_mut() {
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
            #[cfg(feature = "explanations")]
            has_assumption_dependent_yield: false,
            #[cfg(feature = "explanations")]
            assumptions_count_at_start: self.trace.assumptions.len(),
            #[cfg(feature = "explanations")]
            input_provenance_hint: None,
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

    #[allow(clippy::if_then_some_else_none)]
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

        // Check before value_to_add is moved into the collection.
        #[cfg(feature = "explanations")]
        let value_is_undefined = value_to_add == Value::Undefined;

        // Take ownership of the result register so Rc refcount stays at 1,
        // allowing Rc::make_mut to mutate in-place instead of deep-cloning.
        let mut current_result = self.take_register(result_reg)?;

        match (&comprehension_context.mode, &mut current_result) {
            (&ComprehensionMode::Set, &mut Value::Set(ref mut set)) => {
                crate::Rc::make_mut(set).insert(value_to_add);
            }
            (&ComprehensionMode::Array, &mut Value::Array(ref mut arr)) => {
                crate::Rc::make_mut(arr).push(value_to_add);
            }
            (&ComprehensionMode::Object, &mut Value::Object(ref mut obj)) => {
                if let Some(key) = key_value {
                    crate::Rc::make_mut(obj).insert(key, value_to_add);
                } else {
                    self.set_register(result_reg, current_result)?;
                    self.comprehension_stack.push(comprehension_context);
                    return Err(VmError::InvalidIteration {
                        value: Value::String(Arc::from("Object comprehension requires key")),
                        pc: self.pc,
                    });
                }
            }
            (_mode, other) => {
                let offending = core::mem::replace(other, Value::Undefined);
                self.set_register(result_reg, current_result)?;
                self.comprehension_stack.push(comprehension_context);
                return Err(VmError::InvalidIteration {
                    value: offending,
                    pc: self.pc,
                });
            }
        }

        self.set_register(result_reg, current_result)?;

        // Track if this yield was produced via assumptions (PE soundness warning).
        #[cfg(feature = "explanations")]
        if self.assumption_dependent_depth > 0
            || self.trace.assumptions.len() > comprehension_context.assumptions_count_at_start
            || (value_is_undefined && self.explanation_settings.assume_unknown_input)
        {
            comprehension_context.has_assumption_dependent_yield = true;
            // Capture input provenance from the value register if available.
            if comprehension_context.input_provenance_hint.is_none() {
                let prov = self.provenance.get(value_reg);
                if let Some(path) = prov {
                    if self.explanation_settings.is_unknown_path(path.as_ref()) {
                        comprehension_context.input_provenance_hint =
                            Some(alloc::string::String::from(path.as_ref()));
                    }
                }
            }
        }

        if let Some(iter_state) = comprehension_context.iteration_state.as_mut() {
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

    #[allow(clippy::if_then_some_else_none)]
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

        let (value_to_add, key_value, mode, result_reg_idx, key_reg_idx, value_reg_idx) = {
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
                let mode = context.mode.clone();
                (
                    value_to_add,
                    key_value,
                    mode,
                    result_reg_idx,
                    context.key_reg,
                    context.value_reg,
                )
            } else {
                return Err(VmError::InvalidIteration {
                    value: Value::String(Arc::from("No active comprehension")),
                    pc: self.pc,
                });
            }
        };

        // Take ownership of the result register so Rc refcount stays at 1,
        // allowing Rc::make_mut to mutate in-place instead of deep-cloning.
        let mut current_result = self.take_register(result_reg_idx)?;

        match (&mode, &mut current_result) {
            (&ComprehensionMode::Set, &mut Value::Set(ref mut set)) => {
                crate::Rc::make_mut(set).insert(value_to_add);
            }
            (&ComprehensionMode::Array, &mut Value::Array(ref mut arr)) => {
                crate::Rc::make_mut(arr).push(value_to_add);
            }
            (&ComprehensionMode::Object, &mut Value::Object(ref mut obj)) => {
                if let Some(key) = key_value {
                    crate::Rc::make_mut(obj).insert(key, value_to_add);
                } else {
                    self.set_register(result_reg_idx, current_result)?;
                    return Err(VmError::InvalidIteration {
                        value: Value::String(Arc::from("Object comprehension requires key")),
                        pc: self.pc,
                    });
                }
            }
            (_mode, other) => {
                let offending = core::mem::replace(other, Value::Undefined);
                self.set_register(result_reg_idx, current_result)?;
                return Err(VmError::InvalidIteration {
                    value: offending,
                    pc: self.pc,
                });
            }
        }

        self.set_register(result_reg_idx, current_result)?;

        // Track if this yield was produced via assumptions (PE soundness warning).
        #[cfg(feature = "explanations")]
        {
            let assumption_dependent =
                if let Some(frame) = self.execution_stack.get(comprehension_index) {
                    if let FrameKind::Comprehension { ref context, .. } = frame.kind {
                        self.assumption_dependent_depth > 0
                            || self.trace.assumptions.len() > context.assumptions_count_at_start
                    } else {
                        false
                    }
                } else {
                    false
                };
            if assumption_dependent {
                if let Some(frame) = self.execution_stack.get_mut(comprehension_index) {
                    if let FrameKind::Comprehension {
                        ref mut context, ..
                    } = frame.kind
                    {
                        context.has_assumption_dependent_yield = true;
                    }
                }
            }
        }

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

        if let Some(mut state) = iteration_state_snapshot {
            let has_next = self.setup_next_iteration(&mut state, key_reg_idx, value_reg_idx)?;

            // `setup_next_iteration` advances Object's internal cursor; the
            // owning frame holds the iteration_state, so we must write the
            // updated state back. (The Array/Set variants are also unchanged
            // by copy, so the writeback is uniform.)
            if let Some(frame) = self.execution_stack.get_mut(comprehension_index) {
                if let FrameKind::Comprehension {
                    ref mut context, ..
                } = frame.kind
                {
                    context.iteration_state = Some(state);
                }
            }

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

    fn execute_comprehension_end_run_to_completion(&mut self) -> Result<()> {
        // `ComprehensionEnd` is reached from a loaded program; an empty stack
        // here means malformed user-supplied bytecode, which must still surface
        // as a typed error rather than a panic — including in debug builds.
        #[allow(unused)]
        let context = self
            .comprehension_stack
            .pop()
            .ok_or_else(|| VmError::InvalidIteration {
                value: Value::String(Arc::from("No active comprehension context")),
                pc: self.pc,
            })?;
        #[cfg(feature = "explanations")]
        if context.has_assumption_dependent_yield
            && self.explanation_settings.enabled
            && self.explanation_settings.eval_mode
                == crate::evaluation_trace::EvaluationMode::PartialEval
        {
            self.trace.warnings.push(alloc::format!(
                "comprehension result at PC {} is conditional on assumed inputs; \
                 aggregations over this result may be unsound",
                self.pc
            ));
            // Record an assumption that the comprehension depends on unknown input.
            if let Some(ref hint) = context.input_provenance_hint {
                let (rule_index, definition_index) = self.current_rule_scope();
                let iteration_index = self.current_loop_iteration_index();
                self.trace.record_assumption(
                    crate::evaluation_trace::AssumptionKind::Exists,
                    hint.clone(),
                    alloc::format!("{} is defined", hint),
                    u32::try_from(self.pc).unwrap_or(u32::MAX),
                    None,
                    None,
                    rule_index,
                    definition_index,
                    iteration_index,
                    self.current_conjunction_id(),
                );
            }
        }

        Ok(())
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
                    // The accumulated result already resides in `result_reg`; no
                    // result-register post-processing is required before resuming.
                    #[cfg(feature = "explanations")]
                    if context.has_assumption_dependent_yield
                        && self.explanation_settings.enabled
                        && self.explanation_settings.eval_mode
                            == crate::evaluation_trace::EvaluationMode::PartialEval
                    {
                        self.trace.warnings.push(alloc::format!(
                            "comprehension result at PC {} is conditional on assumed inputs; \
                             aggregations over this result may be unsound",
                            self.pc
                        ));
                        if let Some(ref hint) = context.input_provenance_hint {
                            let (rule_index, definition_index) = self.current_rule_scope();
                            let iteration_index = self.current_loop_iteration_index();
                            self.trace.record_assumption(
                                crate::evaluation_trace::AssumptionKind::Exists,
                                hint.clone(),
                                alloc::format!("{} is defined", hint),
                                u32::try_from(self.pc).unwrap_or(u32::MAX),
                                None,
                                None,
                                rule_index,
                                definition_index,
                                iteration_index,
                                self.current_conjunction_id(),
                            );
                        }
                    }
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
