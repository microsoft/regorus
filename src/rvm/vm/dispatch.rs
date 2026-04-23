// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::{GuardMode, Instruction, LiteralOrRegister};
use crate::rvm::program::Program;
use crate::value::Value;
use alloc::collections::BTreeSet;
#[cfg(feature = "explanations")]
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use core::mem;

use super::errors::{Result, VmError};
use super::execution_model::{ExecutionMode, SuspendReason};
use super::loops::LoopParams;
use super::machine::RegoVM;

pub(super) enum InstructionOutcome {
    Continue,
    Return(Value),
    Break,
    Suspend { reason: SuspendReason },
}

impl RegoVM {
    #[cfg(feature = "explanations")]
    pub(super) fn runtime_path_for_register(&self, register: u8) -> Option<alloc::string::String> {
        self.provenance.get(register).and_then(|path| {
            self.explanation_settings
                .is_unknown_path(path.as_ref())
                .then(|| String::from(path.as_ref()))
        })
    }

    #[cfg(feature = "explanations")]
    pub(super) fn current_rule_scope(&self) -> (u16, u16) {
        self.call_rule_stack
            .last()
            .map(|ctx| {
                (
                    ctx.rule_index,
                    u16::try_from(ctx.current_definition_index).unwrap_or(u16::MAX),
                )
            })
            .unwrap_or((0, 0))
    }

    #[cfg(feature = "explanations")]
    pub(super) fn current_loop_iteration_index(&self) -> Option<u32> {
        self.loop_stack.last().map(|l| l.iteration_index)
    }

    /// Get the current conjunction scope ID.
    #[cfg(feature = "explanations")]
    pub(super) fn current_conjunction_id(&self) -> u32 {
        self.conjunction_id_stack.last().copied().unwrap_or(0)
    }

    /// Push a new conjunction scope (increments the global counter).
    #[cfg(feature = "explanations")]
    pub(super) fn push_conjunction_scope(&mut self) {
        let id = self.trace.next_conjunction_id;
        self.trace.next_conjunction_id = id.saturating_add(1);
        self.conjunction_id_stack.push(id);
    }

    /// Pop the current conjunction scope.
    #[cfg(feature = "explanations")]
    pub(super) fn pop_conjunction_scope(&mut self) {
        self.conjunction_id_stack.pop();
    }

    #[cfg(feature = "explanations")]
    fn record_runtime_comparison_assumption(
        &mut self,
        left: u8,
        right: u8,
        operator: &str,
        condition_text: alloc::string::String,
    ) -> bool {
        let left_path = self.runtime_path_for_register(left);
        let right_path = self.runtime_path_for_register(right);

        let (input_path, assumed_value) = if let Some(path) = left_path {
            // Only assume if the input-path register is actually undefined.
            // If the value exists but doesn't match, it's a genuine failure.
            match self.get_register(left) {
                Ok(v) if *v == Value::Undefined => {}
                _ => return false,
            }
            let value = self
                .get_register(right)
                .ok()
                .and_then(|value| (!matches!(value, Value::Undefined)).then(|| value.clone()));
            (path, value)
        } else if let Some(path) = right_path {
            match self.get_register(right) {
                Ok(v) if *v == Value::Undefined => {}
                _ => return false,
            }
            let value = self
                .get_register(left)
                .ok()
                .and_then(|value| (!matches!(value, Value::Undefined)).then(|| value.clone()));
            (path, value)
        } else {
            return false;
        };

        let (rule_index, definition_index) = self.current_rule_scope();
        let iteration_index = self.current_loop_iteration_index();
        self.trace.record_assumption(
            crate::evaluation_trace::AssumptionKind::ConditionHolds,
            input_path,
            condition_text,
            u32::try_from(self.pc).unwrap_or(u32::MAX),
            Some(String::from(operator)),
            assumed_value,
            rule_index,
            definition_index,
            iteration_index,
            self.current_conjunction_id(),
        );
        // Attach pending data lookup context (from ChainedIndex) if available.
        if let Some(ctx) = self.pending_data_lookup.take() {
            if let Some(last) = self.trace.assumptions.last_mut() {
                last.data_lookup_context = Some(ctx);
            }
        }
        true
    }

    /// Record an assumption for a builtin call whose result is Undefined
    /// because one or more arguments trace to unknown input paths.
    #[cfg(feature = "explanations")]
    fn record_builtin_assumption(
        &mut self,
        params_index: u16,
        dest_register: u8,
        condition_text: String,
    ) -> bool {
        let params = match self
            .program
            .instruction_data
            .get_builtin_call_params(params_index)
        {
            Some(p) => p.clone(),
            None => return false,
        };

        // Only proceed if the builtin's dest register matches the guard register.
        if params.dest != dest_register {
            return false;
        }

        // Find the first argument that is Undefined and traces to an input path.
        let mut input_path = None;
        for &arg_reg in params.arg_registers() {
            if matches!(self.get_register(arg_reg), Ok(v) if *v == Value::Undefined) {
                if let Some(path) = self.runtime_path_for_register(arg_reg) {
                    input_path = Some(path);
                    break;
                }
            }
        }

        let input_path = match input_path {
            Some(p) => p,
            None => return false,
        };

        let (rule_index, definition_index) = self.current_rule_scope();
        let iteration_index = self.current_loop_iteration_index();
        self.trace.record_assumption(
            crate::evaluation_trace::AssumptionKind::ConditionHolds,
            input_path,
            condition_text,
            u32::try_from(self.pc).unwrap_or(u32::MAX),
            None,
            None,
            rule_index,
            definition_index,
            iteration_index,
            self.current_conjunction_id(),
        );
        true
    }

    #[cfg(feature = "explanations")]
    fn maybe_assume_guard_condition(&mut self, register: u8, mode: GuardMode) -> bool {
        if !self.explanation_settings.assume_unknown_input {
            return false;
        }

        let pc = u32::try_from(self.pc).unwrap_or(u32::MAX);
        let static_info = self
            .program
            .condition_infos
            .get(self.pc)
            .and_then(Option::as_ref);
        let condition_text = static_info
            .map(|info| info.text.clone())
            .unwrap_or_default();

        match mode {
            GuardMode::NotUndefined => {
                let Some(input_path) = self.runtime_path_for_register(register).or_else(|| {
                    static_info.and_then(|info| {
                        info.checked_provenance.as_ref().and_then(|prov| {
                            let rendered = alloc::format!("{}", prov);
                            self.explanation_settings
                                .is_unknown_path(&rendered)
                                .then_some(rendered)
                        })
                    })
                }) else {
                    return false;
                };

                let (rule_index, definition_index) = self.current_rule_scope();
                let iteration_index = self.current_loop_iteration_index();
                self.trace.record_assumption(
                    crate::evaluation_trace::AssumptionKind::Exists,
                    input_path,
                    condition_text,
                    pc,
                    None,
                    None,
                    rule_index,
                    definition_index,
                    iteration_index,
                    self.current_conjunction_id(),
                );
                true
            }
            GuardMode::Condition => {
                let Some(prev_pc) = self.pc.checked_sub(1) else {
                    return false;
                };
                let Some(prev_instr) = self.program.instructions.get(prev_pc) else {
                    return false;
                };

                match *prev_instr {
                    Instruction::Eq { dest, left, right } if dest == register => {
                        self.record_runtime_comparison_assumption(left, right, "==", condition_text)
                    }
                    Instruction::Ne { dest, left, right } if dest == register => {
                        self.record_runtime_comparison_assumption(left, right, "!=", condition_text)
                    }
                    Instruction::Lt { dest, left, right } if dest == register => {
                        self.record_runtime_comparison_assumption(left, right, "<", condition_text)
                    }
                    Instruction::Le { dest, left, right } if dest == register => {
                        self.record_runtime_comparison_assumption(left, right, "<=", condition_text)
                    }
                    Instruction::Gt { dest, left, right } if dest == register => {
                        self.record_runtime_comparison_assumption(left, right, ">", condition_text)
                    }
                    Instruction::Ge { dest, left, right } if dest == register => {
                        self.record_runtime_comparison_assumption(left, right, ">=", condition_text)
                    }
                    Instruction::Contains {
                        dest,
                        collection,
                        value,
                    } if dest == register => self.record_runtime_comparison_assumption(
                        collection,
                        value,
                        "in",
                        condition_text,
                    ),
                    Instruction::BuiltinCall { params_index } => {
                        self.record_builtin_assumption(params_index, register, condition_text)
                    }
                    _ => false,
                }
            }
            GuardMode::Not => {
                // In PE mode, if the value is true but was produced by
                // assumption-dependent evaluation, treat the negation as
                // assumed to hold rather than unconditionally failing.
                if self.explanation_settings.eval_mode
                    == crate::evaluation_trace::EvaluationMode::PartialEval
                {
                    let value = self.get_register(register).ok();
                    let is_assumption_derived_true = matches!(value, Some(v) if *v == Value::Bool(true))
                        && self.assumption_dependent_depth > 0;
                    let is_undefined = matches!(value, Some(v) if *v == Value::Undefined);

                    if is_assumption_derived_true || is_undefined {
                        let (rule_index, definition_index) = self.current_rule_scope();
                        let iteration_index = self.current_loop_iteration_index();
                        self.trace.record_assumption(
                            crate::evaluation_trace::AssumptionKind::NegationHolds,
                            String::new(),
                            condition_text,
                            pc,
                            None,
                            None,
                            rule_index,
                            definition_index,
                            iteration_index,
                            self.current_conjunction_id(),
                        );
                        return true;
                    }
                }
                false
            }
        }
    }

    pub(super) fn execute_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        self.execute_load_and_move(program, instruction)
    }

    fn execute_load_and_move(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            Load { dest, literal_idx } => {
                if let Some(value) = program.literals.get(usize::from(literal_idx)) {
                    self.set_register(dest, value.clone())?;
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::LiteralIndexOutOfBounds {
                        index: literal_idx,
                        pc: self.pc,
                    })
                }
            }
            LoadTrue { dest } => {
                self.set_register(dest, Value::Bool(true))?;
                Ok(InstructionOutcome::Continue)
            }
            LoadFalse { dest } => {
                self.set_register(dest, Value::Bool(false))?;
                Ok(InstructionOutcome::Continue)
            }
            LoadNull { dest } => {
                self.set_register(dest, Value::Null)?;
                Ok(InstructionOutcome::Continue)
            }
            LoadBool { dest, value } => {
                self.set_register(dest, Value::Bool(value))?;
                Ok(InstructionOutcome::Continue)
            }
            LoadData { dest } => {
                self.set_register(dest, self.data.clone())?;
                #[cfg(feature = "explanations")]
                self.provenance.set_root(dest, "data");
                Ok(InstructionOutcome::Continue)
            }
            LoadInput { dest } => {
                self.set_register(dest, self.input.clone())?;
                #[cfg(feature = "explanations")]
                self.provenance.set_root(dest, "input");
                Ok(InstructionOutcome::Continue)
            }
            LoadContext { dest } => {
                self.set_register(dest, self.context.clone())?;
                Ok(InstructionOutcome::Continue)
            }
            LoadMetadata { dest } => {
                self.set_register(dest, self.metadata_value.clone())?;
                Ok(InstructionOutcome::Continue)
            }
            Move { dest, src } => {
                let value = self.get_register(src)?.clone();
                self.set_register(dest, value.clone())?;
                #[cfg(feature = "explanations")]
                self.provenance.copy(dest, src);
                #[cfg(feature = "explanations")]
                if self.explanation_settings.enabled
                    && program
                        .binding_infos
                        .get(self.pc)
                        .and_then(|b| b.as_ref())
                        .is_some()
                {
                    let pc = u32::try_from(self.pc).unwrap_or(u32::MAX);
                    let passed = !matches!(value, Value::Undefined);
                    self.trace.record_condition(
                        pc,
                        passed,
                        false,
                        Some(value),
                        self.provenance
                            .get(dest)
                            .map(|path| path.as_ref().to_string()),
                        None,
                        None,
                    );
                }
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_arithmetic_instruction(program, other),
        }
    }

    fn execute_arithmetic_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            Add { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.add_values(a, b)?;
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            Sub { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.sub_values(a, b)?;
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            Mul { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.mul_values(a, b)?;
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            Div { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.div_values(a, b)?;
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            Mod { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.mod_values(a, b)?;
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_comparison_instruction(program, other),
        }
    }

    fn execute_comparison_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            Eq { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                self.set_register(dest, Value::Bool(a == b))?;
                #[cfg(feature = "explanations")]
                self.provenance.copy_first_available(dest, left, right);
                Ok(InstructionOutcome::Continue)
            }
            Ne { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                self.set_register(dest, Value::Bool(a != b))?;
                #[cfg(feature = "explanations")]
                self.provenance.copy_first_available(dest, left, right);
                Ok(InstructionOutcome::Continue)
            }
            Lt { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                        ),
                        pc: self.pc,
                    });
                }

                self.set_register(dest, Value::Bool(a < b))?;
                Ok(InstructionOutcome::Continue)
            }
            Le { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                        ),
                        pc: self.pc,
                    });
                }

                self.set_register(dest, Value::Bool(a <= b))?;
                Ok(InstructionOutcome::Continue)
            }
            Gt { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                        ),
                        pc: self.pc,
                    });
                }

                self.set_register(dest, Value::Bool(a > b))?;
                Ok(InstructionOutcome::Continue)
            }
            Ge { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                        ),
                        pc: self.pc,
                    });
                }

                self.set_register(dest, Value::Bool(a >= b))?;
                Ok(InstructionOutcome::Continue)
            }
            And { dest, left, right } => {
                let left_value = self.get_register(left)?;
                let right_value = self.get_register(right)?;

                if left_value == &Value::Undefined || right_value == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                match (self.to_bool(left_value), self.to_bool(right_value)) {
                    (Some(a), Some(b)) => {
                        self.set_register(dest, Value::Bool(a && b))?;
                        Ok(InstructionOutcome::Continue)
                    }
                    _ => Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: logical AND expects booleans (left={left_value:?}, right={right_value:?})"
                        ),
                        pc: self.pc,
                    }),
                }
            }
            Or { dest, left, right } => {
                let left_value = self.get_register(left)?;
                let right_value = self.get_register(right)?;

                if left_value == &Value::Undefined || right_value == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                match (self.to_bool(left_value), self.to_bool(right_value)) {
                    (Some(a), Some(b)) => {
                        self.set_register(dest, Value::Bool(a || b))?;
                        Ok(InstructionOutcome::Continue)
                    }
                    _ => Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: logical OR expects booleans (left={left_value:?}, right={right_value:?})"
                        ),
                        pc: self.pc,
                    }),
                }
            }
            Not { dest, operand } => {
                // Pop negation scope pushed by NegationBegin.
                #[cfg(feature = "explanations")]
                let negation_scope_id = if self.explanation_settings.assume_unknown_input {
                    // The scope was pushed by NegationBegin before the inner
                    // body.  Pop it now and remember the id for the
                    // NegationHolds assumption we may record below.
                    let stack = &mut self.trace.negation_scope_stack;
                    let id = stack.last().copied();
                    stack.pop();
                    id
                } else {
                    None
                };

                let operand_value = self.get_register(operand)?.clone();
                #[allow(unused_assignments)]
                let negated = match operand_value {
                    Value::Undefined => true,
                    Value::Bool(b) => {
                        // In PE mode, if the operand is true but was produced
                        // via assumptions, treat it as Undefined (indeterminate)
                        // so that the negation yields true (unknown negated = assumed to hold).
                        #[cfg(feature = "explanations")]
                        if b && self.explanation_settings.eval_mode
                            == crate::evaluation_trace::EvaluationMode::PartialEval
                            && self.assumption_dependent_depth > 0
                        {
                            self.assumption_dependent_depth =
                                self.assumption_dependent_depth.saturating_sub(1);
                            true // treat as Undefined → negation is true
                        } else {
                            !b
                        }
                        #[cfg(not(feature = "explanations"))]
                        {
                            !b
                        }
                    }
                    _ => false,
                };

                // In PE mode, record a NegationHolds assumption when the
                // negation succeeds because the operand depends on unknown
                // input (either Undefined directly or true-via-assumptions).
                #[cfg(feature = "explanations")]
                if negated
                    && self.explanation_settings.eval_mode
                        == crate::evaluation_trace::EvaluationMode::PartialEval
                    && self.explanation_settings.assume_unknown_input
                {
                    let is_assumption_involved = matches!(operand_value, Value::Undefined)
                        || self.trace.assumptions.iter().any(|a| {
                            negation_scope_id.is_some_and(|nid| a.negation_scope_id == Some(nid))
                        });

                    if is_assumption_involved {
                        // For simple Undefined operands (e.g. `not input.user.blocked`),
                        // record an inner Exists assumption for the operand path so the
                        // negation has a meaningful inner condition.
                        if operand_value == Value::Undefined {
                            if let Some(input_path) = self.runtime_path_for_register(operand) {
                                let pc = u32::try_from(self.pc).unwrap_or(u32::MAX);
                                let (rule_index, definition_index) = self.current_rule_scope();
                                let iteration_index = self.current_loop_iteration_index();
                                // Temporarily re-push the negation scope so the inner
                                // assumption is tagged with it.
                                if let Some(nid) = negation_scope_id {
                                    self.trace.negation_scope_stack.push(nid);
                                }
                                self.trace.record_assumption(
                                    crate::evaluation_trace::AssumptionKind::Exists,
                                    input_path,
                                    String::new(),
                                    pc,
                                    None,
                                    None,
                                    rule_index,
                                    definition_index,
                                    iteration_index,
                                    self.current_conjunction_id(),
                                );
                                if negation_scope_id.is_some() {
                                    self.trace.negation_scope_stack.pop();
                                }
                            }
                        }

                        // Record the NegationHolds assumption at the outer scope.
                        let static_info = self
                            .program
                            .condition_infos
                            .get(self.pc)
                            .and_then(Option::as_ref);
                        let condition_text = static_info
                            .map(|info| info.text.clone())
                            .unwrap_or_default();
                        let pc = u32::try_from(self.pc).unwrap_or(u32::MAX);
                        let (rule_index, definition_index) = self.current_rule_scope();
                        let iteration_index = self.current_loop_iteration_index();
                        self.trace.record_assumption(
                            crate::evaluation_trace::AssumptionKind::NegationHolds,
                            String::new(),
                            condition_text,
                            pc,
                            None,
                            None,
                            rule_index,
                            definition_index,
                            iteration_index,
                            self.current_conjunction_id(),
                        );
                        // Tag the NegationHolds with the scope it owns so
                        // materialize_pe can find the matching inner assumptions.
                        if let Some(last) = self.trace.assumptions.last_mut() {
                            last.owned_negation_scope_id = negation_scope_id;
                        }
                    }
                }

                self.set_register(dest, Value::Bool(negated))?;
                Ok(InstructionOutcome::Continue)
            }
            NegationBegin {} => {
                // Push a negation scope so that assumptions recorded inside
                // the negated body are tagged with this scope ID.
                #[cfg(feature = "explanations")]
                if self.explanation_settings.assume_unknown_input {
                    self.trace.push_negation_scope();
                }
                Ok(InstructionOutcome::Continue)
            }
            AssertEq { left, right } => {
                let a_val = self.get_register(left)?.clone();
                let b_val = self.get_register(right)?.clone();
                #[allow(unused_mut)]
                let mut passed =
                    a_val != Value::Undefined && b_val != Value::Undefined && a_val == b_val;
                #[cfg(feature = "explanations")]
                let mut assumed = false;
                #[cfg(feature = "explanations")]
                if !passed && self.explanation_settings.assume_unknown_input {
                    let cond_text = program
                        .condition_infos
                        .get(self.pc)
                        .and_then(Option::as_ref)
                        .map(|info| info.text.clone())
                        .unwrap_or_default();
                    if self.record_runtime_comparison_assumption(left, right, "==", cond_text) {
                        passed = true;
                        assumed = true;
                    }
                }
                #[cfg(feature = "explanations")]
                if self.explanation_settings.enabled {
                    let pc = u32::try_from(self.pc).unwrap_or(u32::MAX);
                    self.trace.record_condition(
                        pc,
                        passed,
                        assumed,
                        Some(a_val),
                        self.provenance
                            .get(left)
                            .map(|path| path.as_ref().to_string()),
                        Some(b_val),
                        self.provenance
                            .get(right)
                            .map(|path| path.as_ref().to_string()),
                    );
                }
                self.handle_condition(passed)?;
                Ok(InstructionOutcome::Continue)
            }
            Guard { register, mode } => {
                let value = self.get_register(register)?.clone();
                #[allow(unused_mut)]
                let mut passed = match mode {
                    GuardMode::Not => match value {
                        Value::Undefined => true,
                        Value::Bool(b) => !b,
                        _ => false,
                    },
                    GuardMode::Condition => match value {
                        Value::Bool(b) => b,
                        Value::Undefined => false,
                        _ => true,
                    },
                    GuardMode::NotUndefined => !matches!(value, Value::Undefined),
                };
                #[cfg(feature = "explanations")]
                let assumed = if !passed
                    && self.explanation_settings.assume_unknown_input
                    && self.maybe_assume_guard_condition(register, mode)
                {
                    passed = true;
                    true
                } else {
                    false
                };
                #[cfg(feature = "explanations")]
                if self.explanation_settings.enabled {
                    let pc = u32::try_from(self.pc).unwrap_or(u32::MAX);
                    self.trace.record_condition(
                        pc,
                        passed,
                        assumed,
                        Some(value),
                        self.provenance
                            .get(register)
                            .map(|path| path.as_ref().to_string()),
                        None,
                        None,
                    );
                }
                self.handle_condition(passed)?;
                Ok(InstructionOutcome::Continue)
            }
            ReturnUndefinedIfNotTrue { condition } => {
                let value = self.get_register(condition)?;
                if matches!(value, Value::Bool(true)) {
                    Ok(InstructionOutcome::Continue)
                } else {
                    Ok(InstructionOutcome::Return(Value::Undefined))
                }
            }
            CoalesceUndefinedToNull { register } => {
                let value = self.get_register(register)?;
                if matches!(value, Value::Undefined) {
                    self.set_register(register, Value::Null)?;
                }
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_call_instruction(program, other),
        }
    }

    fn execute_call_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            BuiltinCall { params_index } => {
                self.execute_builtin_call(params_index)?;
                Ok(InstructionOutcome::Continue)
            }
            HostAwait { dest, arg, id } => {
                let argument = self.get_register(arg)?.clone();
                let identifier = self
                    .registers
                    .get(usize::from(id))
                    .cloned()
                    .unwrap_or(Value::Undefined);
                match self.execution_mode {
                    ExecutionMode::RunToCompletion => {
                        let response = self.next_host_await_response(&identifier, dest)?;
                        self.set_register(dest, response)?;
                        Ok(InstructionOutcome::Continue)
                    }
                    ExecutionMode::Suspendable => Ok(InstructionOutcome::Suspend {
                        reason: SuspendReason::HostAwait {
                            dest,
                            argument,
                            identifier,
                        },
                    }),
                }
            }
            FunctionCall { params_index } => {
                self.execute_function_call(params_index)?;
                Ok(InstructionOutcome::Continue)
            }
            Return { value } => {
                let result = self.get_register(value)?.clone();
                Ok(InstructionOutcome::Return(result))
            }
            CallRule { dest, rule_index } => {
                self.execute_call_rule(dest, rule_index)?;
                Ok(InstructionOutcome::Continue)
            }
            RuleInit {
                result_reg,
                rule_index,
            } => {
                self.execute_rule_init(result_reg, rule_index)?;
                Ok(InstructionOutcome::Continue)
            }
            DestructuringSuccess {} => Ok(InstructionOutcome::Break),
            RuleReturn {} => {
                self.execute_rule_return()?;
                Ok(InstructionOutcome::Break)
            }
            other => self.execute_collection_instruction(program, other),
        }
    }

    fn execute_collection_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            ObjectSet { obj, key, value } => {
                let key_value = self.get_register(key)?.clone();
                let value_value = self.get_register(value)?.clone();

                // Take ownership so Rc refcount stays at 1 and make_mut is a no-op.
                let mut obj_value = self.take_register(obj)?;

                if let Ok(obj_mut) = obj_value.as_object_mut() {
                    obj_mut.insert(key_value, value_value);
                    self.set_register(obj, obj_value)?;
                } else {
                    let offending = obj_value.clone();
                    self.set_register(obj, obj_value)?;
                    return Err(VmError::RegisterNotObject {
                        register: obj,
                        value: offending,
                        pc: self.pc,
                    });
                }
                Ok(InstructionOutcome::Continue)
            }
            ObjectDeepSet { params_index } => {
                let params = program
                    .instruction_data
                    .get_object_deep_set_params(params_index)
                    .ok_or(VmError::InvalidObjectCreateParams {
                        index: params_index,
                        pc: self.pc,
                        available: program.instruction_data.object_deep_set_params.len(),
                    })?
                    .clone();

                // Read all key values and the leaf value upfront
                let key_values: alloc::vec::Vec<Value> = params
                    .keys
                    .iter()
                    .map(|&k| self.get_register(k).cloned())
                    .collect::<core::result::Result<_, _>>()?;
                let leaf_value = self.get_register(params.value)?.clone();

                let mut root = self.take_register(params.obj)?;
                self.object_deep_set(
                    &mut root,
                    &key_values,
                    leaf_value,
                    params.multi_value,
                    params.obj,
                )?;
                self.set_register(params.obj, root)?;
                Ok(InstructionOutcome::Continue)
            }
            ObjectCreate { params_index } => {
                let params = program
                    .instruction_data
                    .get_object_create_params(params_index)
                    .ok_or(VmError::InvalidObjectCreateParams {
                        index: params_index,
                        pc: self.pc,
                        available: program.instruction_data.object_create_params.len(),
                    })?;

                let mut any_undefined = false;

                for &(_, value_reg) in params.literal_key_field_pairs() {
                    if matches!(self.get_register(value_reg)?, Value::Undefined) {
                        any_undefined = true;
                        break;
                    }
                }

                if !any_undefined {
                    for &(key_reg, value_reg) in params.field_pairs() {
                        if matches!(self.get_register(key_reg)?, Value::Undefined)
                            || matches!(self.get_register(value_reg)?, Value::Undefined)
                        {
                            any_undefined = true;
                            break;
                        }
                    }
                }

                if any_undefined {
                    self.set_register(params.dest, Value::Undefined)?;
                } else {
                    let mut obj_value = program
                        .literals
                        .get(usize::from(params.template_literal_idx))
                        .ok_or(VmError::InvalidTemplateLiteralIndex {
                            index: params.template_literal_idx,
                            pc: self.pc,
                            available: program.literals.len(),
                        })?
                        .clone();

                    if let Ok(obj_mut) = obj_value.as_object_mut() {
                        let mut literal_updates = params.literal_key_field_pairs().iter();
                        let mut current_literal_update = literal_updates.next();

                        for (key, value) in obj_mut.iter_mut() {
                            if let Some(&(literal_idx, value_reg)) = current_literal_update {
                                if let Some(literal_key) =
                                    program.literals.get(usize::from(literal_idx))
                                {
                                    if key == literal_key {
                                        *value = self.get_register(value_reg)?.clone();
                                        current_literal_update = literal_updates.next();
                                    }
                                }
                            } else {
                                break;
                            }
                        }

                        while let Some(&(literal_idx, value_reg)) = current_literal_update {
                            if let Some(key_value) = program.literals.get(usize::from(literal_idx))
                            {
                                let value_value = self.get_register(value_reg)?.clone();
                                obj_mut.insert(key_value.clone(), value_value);
                            }
                            current_literal_update = literal_updates.next();
                        }

                        for &(key_reg, value_reg) in params.field_pairs() {
                            let key_value = self.get_register(key_reg)?.clone();
                            let value_value = self.get_register(value_reg)?.clone();
                            obj_mut.insert(key_value, value_value);
                        }
                    } else {
                        return Err(VmError::ObjectCreateInvalidTemplate {
                            template: obj_value,
                            pc: self.pc,
                        });
                    }

                    self.set_register(params.dest, obj_value)?;
                }
                Ok(InstructionOutcome::Continue)
            }
            Index {
                dest,
                container,
                key,
            } => {
                let key_value = self.get_register(key)?;
                let container_value = self.get_register(container)?;
                let result = container_value[key_value].clone();
                #[cfg(feature = "explanations")]
                let key_clone = key_value.clone();
                self.set_register(dest, result.clone())?;
                #[cfg(feature = "explanations")]
                {
                    // When the result is Undefined because the key is unknown
                    // (from input), propagate the key's input provenance to the
                    // dest register so downstream comparisons can fire assumptions.
                    if result == Value::Undefined && self.explanation_settings.assume_unknown_input
                    {
                        if let Some(key_path) = self.provenance.get(key).cloned() {
                            if self.explanation_settings.is_unknown_path(key_path.as_ref()) {
                                self.provenance.set_path(dest, Some(key_path));
                            } else {
                                self.provenance.append_index(dest, container, &key_clone);
                            }
                        } else {
                            self.provenance.append_index(dest, container, &key_clone);
                        }
                    } else {
                        self.provenance.append_index(dest, container, &key_clone);
                    }
                }
                Ok(InstructionOutcome::Continue)
            }
            IndexLiteral {
                dest,
                container,
                literal_idx,
            } => {
                let container_value = self.get_register(container)?;

                if let Some(key_value) = program.literals.get(usize::from(literal_idx)) {
                    let result = container_value[key_value].clone();
                    self.set_register(dest, result)?;
                    #[cfg(feature = "explanations")]
                    {
                        if let Ok(field) = key_value.as_string() {
                            self.provenance
                                .append_field(dest, container, field.as_ref());
                        } else {
                            self.provenance.append_index(dest, container, key_value);
                        }
                    }
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::LiteralIndexOutOfBounds {
                        index: literal_idx,
                        pc: self.pc,
                    })
                }
            }
            ArrayNew { dest } => {
                let empty_array = Value::new_array();
                self.set_register(dest, empty_array)?;
                Ok(InstructionOutcome::Continue)
            }
            ArrayPush { arr, value } => {
                let value_to_push = self.get_register(value)?.clone();

                // Take ownership so Rc refcount stays at 1 and make_mut is a no-op.
                let mut arr_value = self.take_register(arr)?;

                if let Ok(arr_mut) = arr_value.as_array_mut() {
                    arr_mut.push(value_to_push);
                    self.set_register(arr, arr_value)?;
                } else {
                    let offending = arr_value.clone();
                    self.set_register(arr, arr_value)?;
                    return Err(VmError::RegisterNotArray {
                        register: arr,
                        value: offending,
                        pc: self.pc,
                    });
                }
                Ok(InstructionOutcome::Continue)
            }
            ArrayPushDefined { arr, value } => {
                // Skip undefined values — matches Azure Policy's
                // `field('alias[*].property')` collection semantics where
                // absent nested properties are excluded from the collected
                // array.
                if self.get_register(value)? == &Value::Undefined {
                    return Ok(InstructionOutcome::Continue);
                }

                let value_to_push = self.get_register(value)?.clone();

                let mut arr_value = self.take_register(arr)?;

                if let Ok(arr_mut) = arr_value.as_array_mut() {
                    arr_mut.push(value_to_push);
                    self.set_register(arr, arr_value)?;
                } else {
                    let offending = arr_value.clone();
                    self.set_register(arr, arr_value)?;
                    return Err(VmError::RegisterNotArray {
                        register: arr,
                        value: offending,
                        pc: self.pc,
                    });
                }
                Ok(InstructionOutcome::Continue)
            }
            ArrayCreate { params_index } => {
                if let Some(params) = program
                    .instruction_data
                    .get_array_create_params(params_index)
                {
                    let mut any_undefined = false;
                    for &reg in params.element_registers() {
                        if matches!(self.get_register(reg)?, Value::Undefined) {
                            any_undefined = true;
                            break;
                        }
                    }

                    if any_undefined {
                        self.set_register(params.dest, Value::Undefined)?;
                    } else {
                        let elements: Vec<Value> = params
                            .element_registers()
                            .iter()
                            .map(|&reg| self.get_register(reg).cloned())
                            .collect::<Result<Vec<_>>>()?;

                        let array_value = Value::from_array(elements);
                        self.set_register(params.dest, array_value)?;
                    }
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::InvalidArrayCreateParams {
                        index: params_index,
                        pc: self.pc,
                        available: program.instruction_data.array_create_params.len(),
                    })
                }
            }
            SetNew { dest } => {
                let empty_set = Value::new_set();
                self.set_register(dest, empty_set)?;
                Ok(InstructionOutcome::Continue)
            }
            SetAdd { set, value } => {
                let value_to_add = self.get_register(value)?.clone();

                // Never add undefined values to a set.
                if matches!(value_to_add, Value::Undefined) {
                    return Ok(InstructionOutcome::Continue);
                }

                // Take ownership so Rc refcount stays at 1 and make_mut is a no-op.
                let mut set_value = self.take_register(set)?;

                if let Ok(set_mut) = set_value.as_set_mut() {
                    set_mut.insert(value_to_add.clone());
                    #[cfg(feature = "explanations")]
                    if self.explanation_settings.enabled {
                        if let Some(ctx) = self.call_rule_stack.last() {
                            if ctx.rule_type == crate::rvm::program::RuleType::PartialSet
                                && set == ctx.result_reg
                            {
                                let condition_end_index =
                                    u32::try_from(self.trace.condition_outcomes.len())
                                        .unwrap_or(u32::MAX);
                                let condition_start_index =
                                    u32::try_from(ctx.current_body_condition_start)
                                        .unwrap_or(u32::MAX);
                                self.trace.record_emission(
                                    ctx.rule_index,
                                    u16::try_from(ctx.current_definition_index).unwrap_or(u16::MAX),
                                    condition_start_index,
                                    condition_end_index,
                                    value_to_add.clone(),
                                );
                            }
                        }
                    }
                    self.set_register(set, set_value)?;
                } else {
                    let offending = set_value.clone();
                    self.set_register(set, set_value)?;
                    return Err(VmError::RegisterNotSet {
                        register: set,
                        value: offending,
                        pc: self.pc,
                    });
                }
                Ok(InstructionOutcome::Continue)
            }
            SetCreate { params_index } => {
                if let Some(params) = program.instruction_data.get_set_create_params(params_index) {
                    let mut any_undefined = false;
                    for &reg in params.element_registers() {
                        if matches!(self.get_register(reg)?, Value::Undefined) {
                            any_undefined = true;
                            break;
                        }
                    }

                    if any_undefined {
                        self.set_register(params.dest, Value::Undefined)?;
                    } else {
                        let mut set = alloc::collections::BTreeSet::new();
                        for &reg in params.element_registers() {
                            set.insert(self.get_register(reg)?.clone());
                        }

                        let set_value = Value::from(set);
                        self.set_register(params.dest, set_value)?;
                    }
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::InvalidSetCreateParams {
                        index: params_index,
                        pc: self.pc,
                        available: program.instruction_data.set_create_params.len(),
                    })
                }
            }
            Contains {
                dest,
                collection,
                value,
            } => {
                let value_to_check = self.get_register(value)?;
                let collection_value = self.get_register(collection)?;

                let result = match *collection_value {
                    Value::Set(ref set_elements) => {
                        Value::Bool(set_elements.contains(value_to_check))
                    }
                    Value::Array(ref array_items) => {
                        Value::Bool(array_items.contains(value_to_check))
                    }
                    Value::Object(ref object_fields) => {
                        Value::Bool(object_fields.values().any(|v| v == value_to_check))
                    }
                    _ => Value::Bool(false),
                };

                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            Count { dest, collection } => {
                let collection_value = self.get_register(collection)?;

                let result = match *collection_value {
                    Value::Array(ref array_items) => Value::from(array_items.len()),
                    Value::Object(ref object_fields) => Value::from(object_fields.len()),
                    Value::Set(ref set_elements) => Value::from(set_elements.len()),
                    _ => Value::Undefined,
                };

                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_loop_instruction(program, other),
        }
    }

    fn execute_loop_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            LoopStart { params_index } => {
                let loop_params_len = program.instruction_data.loop_params.len();

                let loop_params = program
                    .instruction_data
                    .get_loop_params(params_index)
                    .ok_or(VmError::InvalidLoopParams {
                        index: params_index,
                        pc: self.pc,
                        available: loop_params_len,
                    })?;
                let mode = loop_params.mode;

                let params = LoopParams {
                    collection: loop_params.collection,
                    key_reg: loop_params.key_reg,
                    value_reg: loop_params.value_reg,
                    result_reg: loop_params.result_reg,
                    body_start: loop_params.body_start,
                    loop_end: loop_params.loop_end,
                };
                self.execute_loop_start(&mode, params)?;
                Ok(InstructionOutcome::Continue)
            }
            LoopNext {
                body_start,
                loop_end,
            } => {
                self.execute_loop_next(body_start, loop_end)?;
                Ok(InstructionOutcome::Continue)
            }
            Halt {} => {
                let result = self.get_register(0)?.clone();
                Ok(InstructionOutcome::Return(result))
            }
            other => self.execute_policy_instruction(program, other),
        }
    }

    #[cfg(not(feature = "azure_policy"))]
    fn execute_policy_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        match instruction {
            instruction @ (Instruction::PolicyCondition { .. }
            | Instruction::LogicalBlockStart { .. }
            | Instruction::LogicalBlockEnd { .. }
            | Instruction::AllOfNext { .. }
            | Instruction::AnyOfNext { .. }) => Err(VmError::UnhandledInstruction {
                instruction: alloc::format!("{:?} requires the azure_policy feature", instruction),
                pc: self.pc,
            }),
            other => self.execute_virtual_instruction(program, other),
        }
    }

    /// Check whether `l` "contains" `r` using Azure Policy semantics.
    ///
    /// Works on strings (case-insensitive substring), arrays/sets (element
    /// membership), and objects (key membership). For string haystacks,
    /// non-string scalar RHS values are coerced to strings before the
    /// substring check. For non-string scalar LHS values, coercion to string
    /// only happens when the RHS is already a string.
    #[cfg(feature = "azure_policy")]
    #[inline]
    fn policy_contains_check(l: &Value, r: &Value) -> bool {
        use crate::builtins::azure_policy::helpers::{case_insensitive_equals, coerce_to_string};
        use crate::languages::azure_policy::strings;

        match *l {
            Value::String(ref haystack) => match *r {
                Value::String(ref needle) => strings::case_fold::contains(haystack, needle),
                _ => coerce_to_string(r)
                    .is_some_and(|needle| strings::case_fold::contains(haystack, &needle)),
            },
            Value::Array(ref items) => items.iter().any(|item| case_insensitive_equals(item, r)),
            Value::Set(ref items) => items.iter().any(|item| case_insensitive_equals(item, r)),
            // ARM template contains(object, key) checks key membership.
            Value::Object(ref map) => map.keys().any(|key| case_insensitive_equals(key, r)),
            // Coerce non-string scalar LHS (e.g., count result)
            // to a string only when the RHS is already a string.
            _ => {
                if let Value::String(ref needle) = *r {
                    coerce_to_string(l)
                        .is_some_and(|haystack| strings::case_fold::contains(&haystack, needle))
                } else {
                    false
                }
            }
        }
    }

    /// Evaluate a Policy comparison operator.  Undefined LHS → false.
    #[cfg(feature = "azure_policy")]
    fn policy_compare(
        &mut self,
        dest: u8,
        left: u8,
        right: u8,
        cmp: fn(i8) -> bool,
    ) -> Result<InstructionOutcome> {
        use crate::builtins::azure_policy::helpers::{compare_values, is_undefined};

        let l = self.get_register(left)?;
        if is_undefined(l) {
            self.set_register(dest, Value::Bool(false))?;
        } else {
            let r = self.get_register(right)?;
            let result = compare_values(l, r).is_some_and(cmp);
            self.set_register(dest, Value::Bool(result))?;
        }
        Ok(InstructionOutcome::Continue)
    }

    #[cfg(feature = "azure_policy")]
    fn execute_policy_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use crate::builtins::azure_policy::helpers::{
            as_boolish, case_insensitive_equals, coerce_to_string_ci,
            collection_any_ci_eq_excluding_null, collection_has_null, is_true, is_undefined,
            match_like_pattern_ci, match_pattern,
        };
        use crate::rvm::instructions::{LogicalBlockMode, PolicyOp};

        use Instruction::*;
        match instruction {
            PolicyCondition {
                dest,
                left,
                right,
                op,
            } => {
                let l = self.get_register(left)?;
                let result = match op {
                    PolicyOp::Equals => {
                        let r = self.get_register(right)?;
                        if is_undefined(l) {
                            matches!(r, Value::Null)
                        } else {
                            case_insensitive_equals(l, r)
                        }
                    }
                    PolicyOp::NotEquals => {
                        let r = self.get_register(right)?;
                        if is_undefined(l) {
                            !matches!(r, Value::Null)
                        } else {
                            !case_insensitive_equals(l, r)
                        }
                    }
                    PolicyOp::Greater => {
                        return self.policy_compare(dest, left, right, |c| c > 0);
                    }
                    PolicyOp::GreaterOrEquals => {
                        return self.policy_compare(dest, left, right, |c| c >= 0);
                    }
                    PolicyOp::Less => {
                        return self.policy_compare(dest, left, right, |c| c < 0);
                    }
                    PolicyOp::LessOrEquals => {
                        return self.policy_compare(dest, left, right, |c| c <= 0);
                    }
                    PolicyOp::In => {
                        let r = self.get_register(right)?;
                        if is_undefined(l) {
                            collection_has_null(r)
                        } else if matches!(*l, Value::Null) || is_undefined(r) {
                            false
                        } else {
                            collection_any_ci_eq_excluding_null(r, l)
                        }
                    }
                    PolicyOp::NotIn => {
                        let r = self.get_register(right)?;
                        if is_undefined(l) {
                            !collection_has_null(r)
                        } else if matches!(*l, Value::Null) || is_undefined(r) {
                            true
                        } else {
                            !collection_any_ci_eq_excluding_null(r, l)
                        }
                    }
                    PolicyOp::Contains | PolicyOp::NotContains => {
                        let negated = op.is_negated();
                        if is_undefined(l) {
                            negated
                        } else {
                            let r = self.get_register(right)?;
                            if is_undefined(r) {
                                // undefined RHS: positive → false, negated → false
                                false
                            } else {
                                negated ^ Self::policy_contains_check(l, r)
                            }
                        }
                    }
                    PolicyOp::ContainsKey | PolicyOp::NotContainsKey => {
                        let negated = op.is_negated();
                        if is_undefined(l) {
                            negated
                        } else {
                            let r = self.get_register(right)?;
                            if is_undefined(r) {
                                false
                            } else {
                                let found = match *l {
                                    Value::Object(ref map) => {
                                        map.keys().any(|key| case_insensitive_equals(key, r))
                                    }
                                    _ => false,
                                };
                                negated ^ found
                            }
                        }
                    }
                    PolicyOp::Like | PolicyOp::NotLike => {
                        let negated = op.is_negated();
                        if is_undefined(l) {
                            negated
                        } else {
                            let r = self.get_register(right)?;
                            let positive = match (coerce_to_string_ci(l), coerce_to_string_ci(r)) {
                                (Some(input), Some(pattern)) => {
                                    match_like_pattern_ci(&input, &pattern)
                                }
                                _ => false,
                            };
                            negated ^ positive
                        }
                    }
                    PolicyOp::Match
                    | PolicyOp::NotMatch
                    | PolicyOp::MatchInsensitively
                    | PolicyOp::NotMatchInsensitively => {
                        let negated = op.is_negated();
                        let case_insensitive = matches!(
                            op,
                            PolicyOp::MatchInsensitively | PolicyOp::NotMatchInsensitively
                        );
                        if is_undefined(l) {
                            negated
                        } else {
                            let r = self.get_register(right)?;
                            negated ^ match_pattern(l, r, case_insensitive)
                        }
                    }
                    PolicyOp::Exists => {
                        let r = self.get_register(right)?;
                        let expected = as_boolish(r).unwrap_or(false);
                        let is_defined = !is_undefined(l) && !matches!(l, Value::Null);
                        is_defined == expected
                    }
                    PolicyOp::ValueConditionGuard => {
                        // left = value register, right = condition register
                        if is_undefined(l) {
                            self.set_register(dest, Value::Bool(false))?;
                            return Ok(InstructionOutcome::Continue);
                        } else {
                            let c = self.get_register(right)?.clone();
                            self.set_register(dest, c)?;
                            return Ok(InstructionOutcome::Continue);
                        }
                    }
                    PolicyOp::Not => {
                        // left = operand, right unused
                        !is_true(l)
                    }
                };
                self.set_register(dest, Value::Bool(result))?;
                Ok(InstructionOutcome::Continue)
            }

            // AllOf / AnyOf structured instructions
            LogicalBlockStart {
                mode: _,
                result,
                end_pc: _,
            } => {
                // Initialize result to false (pessimistic).
                self.set_register(result, Value::Bool(false))?;
                Ok(InstructionOutcome::Continue)
            }
            AllOfNext {
                check,
                result,
                end_pc,
            } => {
                let val = self.get_register(check)?;
                if !matches!(val, Value::Bool(true)) {
                    // Child failed — short-circuit. Ensure the block result is false.
                    self.set_register(result, Value::Bool(false))?;
                    self.pc = usize::from(end_pc);
                }
                Ok(InstructionOutcome::Continue)
            }
            AnyOfNext {
                check,
                result,
                end_pc,
            } => {
                let val = self.get_register(check)?;
                if matches!(val, Value::Bool(true)) {
                    // Child succeeded — short-circuit.
                    self.set_register(result, Value::Bool(true))?;
                    self.pc = usize::from(end_pc);
                }
                Ok(InstructionOutcome::Continue)
            }
            LogicalBlockEnd { mode, result } => {
                match mode {
                    LogicalBlockMode::AllOf => {
                        // All children passed — set result to true.
                        self.set_register(result, Value::Bool(true))?;
                    }
                    LogicalBlockMode::AnyOf => {
                        // No child matched — result stays false (set by LogicalBlockStart).
                    }
                }
                Ok(InstructionOutcome::Continue)
            }

            other => self.execute_virtual_instruction(program, other),
        }
    }

    fn execute_virtual_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            ChainedIndex { params_index } => {
                let params = program
                    .instruction_data
                    .get_chained_index_params(params_index)
                    .ok_or(VmError::InvalidChainedIndexParams {
                        index: params_index,
                        pc: self.pc,
                        available: program.instruction_data.chained_index_params.len(),
                    })?;

                let mut current_value = self.get_register(params.root)?.clone();
                #[cfg(feature = "explanations")]
                let mut current_path = self
                    .provenance
                    .get(params.root)
                    .map(|path| path.as_ref().to_string());

                for (comp_idx, component) in params.path_components.iter().enumerate() {
                    let _ = comp_idx; // used under #[cfg(feature = "explanations")]
                    let key_value = match *component {
                        LiteralOrRegister::Literal(idx) => program
                            .literals
                            .get(usize::from(idx))
                            .ok_or(VmError::LiteralIndexOutOfBounds {
                                index: idx,
                                pc: self.pc,
                            })?
                            .clone(),
                        LiteralOrRegister::Register(reg) => self.get_register(reg)?.clone(),
                    };

                    #[cfg(feature = "explanations")]
                    {
                        // In PE mode, when a key register is Undefined and
                        // traces to an input path, propagate its provenance
                        // to the dest register so downstream comparisons can
                        // fire assumptions.
                        if key_value == Value::Undefined
                            && self.explanation_settings.assume_unknown_input
                        {
                            if let &LiteralOrRegister::Register(reg) = component {
                                if let Some(path) = self.runtime_path_for_register(reg) {
                                    // If the base is a concrete object, capture
                                    // it for data-key inversion in PE reports.
                                    if matches!(current_value, Value::Object(_)) {
                                        self.pending_data_lookup =
                                            Some(crate::evaluation_trace::DataLookupContext {
                                                data_object: current_value.clone(),
                                                key_input_path: path.clone(),
                                            });
                                    }
                                    current_value = Value::Undefined;
                                    current_path = Some(path);
                                    break;
                                }
                            }
                        }

                        current_path = current_path
                            .as_deref()
                            .map(|base| Self::append_path_component(base, &key_value));
                    }

                    current_value = current_value[&key_value].clone();

                    if current_value == Value::Undefined {
                        // Value became Undefined, but keep appending remaining
                        // literal path components to current_path so provenance
                        // captures the full path (e.g. "input.user.role" not
                        // just "input.user").
                        #[cfg(feature = "explanations")]
                        if let Some(remaining_components) =
                            params.path_components.get(comp_idx.saturating_add(1)..)
                        {
                            for remaining in remaining_components {
                                if let &LiteralOrRegister::Literal(idx) = remaining {
                                    if let Some(lit) = program.literals.get(usize::from(idx)) {
                                        current_path = current_path
                                            .as_deref()
                                            .map(|base| Self::append_path_component(base, lit));
                                    } else {
                                        break;
                                    }
                                } else {
                                    // Register component — can't know the key statically
                                    break;
                                }
                            }
                        }
                        break;
                    }
                }

                self.set_register(params.dest, current_value)?;
                #[cfg(feature = "explanations")]
                self.provenance
                    .set_path(params.dest, current_path.map(|path| path.into()));
                Ok(InstructionOutcome::Continue)
            }
            VirtualDataDocumentLookup { params_index } => {
                self.execute_virtual_data_document_lookup(params_index)?;
                Ok(InstructionOutcome::Continue)
            }
            ComprehensionBegin { params_index } => {
                let params = program
                    .instruction_data
                    .get_comprehension_begin_params(params_index)
                    .ok_or(VmError::InvalidComprehensionBeginParams {
                        index: params_index,
                        pc: self.pc,
                        available: program.instruction_data.comprehension_begin_params.len(),
                    })?
                    .clone();
                self.execute_comprehension_begin(&params)?;
                Ok(InstructionOutcome::Continue)
            }
            ComprehensionYield { value_reg, key_reg } => {
                self.execute_comprehension_yield(value_reg, key_reg)?;
                Ok(InstructionOutcome::Continue)
            }
            ComprehensionEnd {} => {
                self.execute_comprehension_end()?;
                Ok(InstructionOutcome::Continue)
            }
            unexpected => Err(VmError::UnhandledInstruction {
                instruction: alloc::format!("{:?}", unexpected),
                pc: self.pc,
            }),
        }
    }

    fn object_deep_set(
        &self,
        current: &mut Value,
        key_values: &[Value],
        leaf_value: Value,
        multi_value: bool,
        obj_register: u8,
    ) -> Result<()> {
        let Some((first_key, remaining_keys)) = key_values.split_first() else {
            return Ok(());
        };

        let offending = current.clone();
        let object = current
            .as_object_mut()
            .map_err(|_| VmError::RegisterNotObject {
                register: obj_register,
                value: offending,
                pc: self.pc,
            })?;

        if remaining_keys.is_empty() {
            if multi_value {
                let leaf = match object.entry(first_key.clone()) {
                    alloc::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
                    alloc::collections::btree_map::Entry::Vacant(entry) => {
                        entry.insert(Value::new_set())
                    }
                };

                let leaf_snapshot = leaf.clone();
                let set = leaf.as_set_mut().map_err(|_| VmError::RegisterNotSet {
                    register: obj_register,
                    value: leaf_snapshot,
                    pc: self.pc,
                })?;
                set.insert(leaf_value);
            } else {
                object.insert(first_key.clone(), leaf_value);
            }

            return Ok(());
        }

        let child = match object.entry(first_key.clone()) {
            alloc::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
            alloc::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(Value::new_object())
            }
        };

        if !matches!(child, Value::Object(_)) {
            return Err(VmError::RegisterNotObject {
                register: obj_register,
                value: child.clone(),
                pc: self.pc,
            });
        }

        self.object_deep_set(child, remaining_keys, leaf_value, multi_value, obj_register)
    }
}
