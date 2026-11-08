// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]
use super::Compiler;
use super::Register;
use crate::compiler::destructuring_planner::plans::{
    AssignmentPlan, BindingPlan, DestructuringPlan, WildcardSide,
};
use crate::lexer::Span;
use crate::rvm::instructions::{BuiltinCallParams, GuardMode, Instruction};
use crate::value::Value;
use alloc::vec::Vec;
use anyhow::{bail, Result};

#[derive(Clone, Copy, Debug)]
pub enum PlanContext {
    ColonAssignment,
    Assignment,
    FunctionParameter,
    LoopIndex,
    SomeIn,
}

impl<'a> Compiler<'a> {
    pub(super) fn emit_match_failure_branch(
        &mut self,
        register: Register,
        mode: GuardMode,
        span: &Span,
    ) -> Result<usize> {
        let scratch = self.alloc_register()?;
        let operand = if matches!(mode, GuardMode::NotUndefined) {
            self.emit_instruction(
                Instruction::Eq {
                    dest: scratch,
                    left: register,
                    right: register,
                },
                span,
            );
            scratch
        } else {
            register
        };
        self.emit_instruction(
            Instruction::Not {
                dest: scratch,
                operand,
            },
            span,
        );
        let branch = self.program.instructions.len();
        self.emit_instruction(
            Instruction::AnyOfNext {
                check: scratch,
                result: scratch,
                end_pc: 0,
            },
            span,
        );
        Ok(branch)
    }

    pub(super) fn patch_match_failure_branches(&mut self, branches: &[usize]) -> Result<()> {
        let end_pc = self
            .program
            .instructions
            .len()
            .checked_sub(1)
            .and_then(|pc| u16::try_from(pc).ok())
            .ok_or_else(|| {
                anyhow::anyhow!("match branch target exceeds the RVM instruction limit")
            })?;
        for &branch in branches {
            let Some(Instruction::AnyOfNext { end_pc: target, .. }) =
                self.program.instructions.get_mut(branch)
            else {
                bail!("match branch instruction is missing or invalid");
            };
            *target = end_pc;
        }
        Ok(())
    }

    fn emit_match_check(
        &mut self,
        register: Register,
        mode: GuardMode,
        span: &Span,
        failures: &mut Vec<usize>,
    ) -> Result<()> {
        if self.soft_assert_mode {
            failures.push(self.emit_match_failure_branch(register, mode, span)?);
        } else {
            self.emit_instruction(Instruction::Guard { register, mode }, span);
        }
        Ok(())
    }

    fn with_match_result<F>(&mut self, span: &Span, f: F) -> Result<Option<Register>>
    where
        F: FnOnce(&mut Self, &mut Vec<usize>) -> Result<()>,
    {
        let result_register = if self.soft_assert_mode {
            Some(self.load_bool_literal(false, span)?)
        } else {
            None
        };
        let saved_roots = (self.current_input_register, self.current_data_register);
        let mut failures = Vec::new();
        let result = f(self, &mut failures);
        if result_register.is_some() {
            // A failed match skips expressions whose root loads do not dominate the join.
            (self.current_input_register, self.current_data_register) = saved_roots;
        }
        result?;
        if let Some(dest) = result_register {
            self.emit_instruction(Instruction::LoadBool { dest, value: true }, span);
            self.patch_match_failure_branches(&failures)?;
        }
        Ok(result_register)
    }

    pub fn compile_assignment_plan_using_hoisted_destructuring(
        &mut self,
        plan: &AssignmentPlan,
        span: &Span,
    ) -> Result<Register> {
        match plan {
            AssignmentPlan::ColonEquals {
                rhs_expr, lhs_plan, ..
            } => {
                let rhs_reg = self.compile_rego_expr_with_span(rhs_expr, rhs_expr.span(), false)?;
                let _ = self.apply_destructuring_plan(
                    lhs_plan,
                    rhs_reg,
                    span,
                    PlanContext::ColonAssignment,
                )?;
                Ok(rhs_reg)
            }
            AssignmentPlan::EqualsBindLeft {
                rhs_expr, lhs_plan, ..
            } => {
                let rhs_reg = self.compile_rego_expr_with_span(rhs_expr, rhs_expr.span(), false)?;
                let result = self.apply_destructuring_plan(
                    lhs_plan,
                    rhs_reg,
                    span,
                    PlanContext::Assignment,
                )?;
                result.map_or_else(|| self.load_bool_literal(true, span), Ok)
            }
            AssignmentPlan::EqualsBindRight {
                lhs_expr, rhs_plan, ..
            } => {
                let lhs_reg = self.compile_rego_expr_with_span(lhs_expr, lhs_expr.span(), false)?;
                let result = self.apply_destructuring_plan(
                    rhs_plan,
                    lhs_reg,
                    span,
                    PlanContext::Assignment,
                )?;
                result.map_or_else(|| self.load_bool_literal(true, span), Ok)
            }
            AssignmentPlan::EqualsBothSides { element_pairs, .. } => {
                let result = self.with_match_result(span, |compiler, failures| {
                    for (value_expr, value_plan) in element_pairs {
                        let value_reg = compiler.compile_rego_expr_with_span(
                            value_expr,
                            value_expr.span(),
                            false,
                        )?;
                        compiler
                            .apply_destructuring_plan_impl(value_plan, value_reg, span, failures)?;
                    }
                    Ok(())
                })?;
                result.map_or_else(|| self.load_bool_literal(true, span), Ok)
            }
            AssignmentPlan::EqualityCheck { lhs_expr, rhs_expr } => {
                let lhs_reg = self.compile_rego_expr_with_span(lhs_expr, lhs_expr.span(), false)?;
                let rhs_reg = self.compile_rego_expr_with_span(rhs_expr, rhs_expr.span(), false)?;
                let dest = self.alloc_register()?;
                self.emit_instruction(
                    Instruction::Eq {
                        dest,
                        left: lhs_reg,
                        right: rhs_reg,
                    },
                    span,
                );
                if !self.soft_assert_mode {
                    self.emit_instruction(
                        Instruction::Guard {
                            register: dest,
                            mode: GuardMode::Condition,
                        },
                        span,
                    );
                }
                Ok(dest)
            }
            AssignmentPlan::WildcardMatch {
                lhs_expr,
                rhs_expr,
                wildcard_side,
            } => match wildcard_side {
                WildcardSide::Both => self.load_bool_literal(true, span),
                WildcardSide::Lhs => {
                    let rhs_reg =
                        self.compile_rego_expr_with_span(rhs_expr, rhs_expr.span(), false)?;
                    let result = self.with_match_result(span, |compiler, failures| {
                        compiler.emit_match_check(rhs_reg, GuardMode::NotUndefined, span, failures)
                    })?;
                    result.map_or_else(|| self.load_bool_literal(true, span), Ok)
                }
                WildcardSide::Rhs => {
                    let lhs_reg =
                        self.compile_rego_expr_with_span(lhs_expr, lhs_expr.span(), false)?;
                    let result = self.with_match_result(span, |compiler, failures| {
                        compiler.emit_match_check(lhs_reg, GuardMode::NotUndefined, span, failures)
                    })?;
                    result.map_or_else(|| self.load_bool_literal(true, span), Ok)
                }
            },
        }
    }

    pub fn apply_binding_plan(
        &mut self,
        plan: &BindingPlan,
        value_register: Register,
        span: &Span,
    ) -> Result<Option<Register>> {
        match plan {
            BindingPlan::Assignment { .. } => {
                bail!("assignment binding plans should be handled via compile_assignment_plan")
            }
            BindingPlan::LoopIndex {
                destructuring_plan, ..
            } => self.apply_destructuring_plan(
                destructuring_plan,
                value_register,
                span,
                PlanContext::LoopIndex,
            ),
            BindingPlan::Parameter {
                destructuring_plan, ..
            } => self.apply_destructuring_plan(
                destructuring_plan,
                value_register,
                span,
                PlanContext::FunctionParameter,
            ),
            BindingPlan::SomeIn { .. } => {
                bail!("use apply_some_in_binding_plan for SomeIn bindings")
            }
        }
    }

    pub fn apply_some_in_binding_plan(
        &mut self,
        key_plan: Option<&DestructuringPlan>,
        key_register: Option<Register>,
        key_span: Option<&Span>,
        value_plan: &DestructuringPlan,
        value_register: Register,
        value_span: &Span,
    ) -> Result<()> {
        if let (Some(plan), Some(register)) = (key_plan, key_register) {
            let span = key_span.unwrap_or(value_span);
            let _ = self.apply_destructuring_plan(plan, register, span, PlanContext::SomeIn)?;
        }
        let _ = self.apply_destructuring_plan(
            value_plan,
            value_register,
            value_span,
            PlanContext::SomeIn,
        )?;
        Ok(())
    }

    fn apply_destructuring_plan(
        &mut self,
        plan: &DestructuringPlan,
        value_register: Register,
        span: &Span,
        _context: PlanContext,
    ) -> Result<Option<Register>> {
        self.with_match_result(span, |compiler, failures| {
            compiler.apply_destructuring_plan_impl(plan, value_register, span, failures)
        })
    }

    fn apply_destructuring_plan_impl(
        &mut self,
        plan: &DestructuringPlan,
        value_register: Register,
        span: &Span,
        failures: &mut Vec<usize>,
    ) -> Result<()> {
        if !matches!(
            plan,
            DestructuringPlan::Array { .. } | DestructuringPlan::Object { .. }
        ) {
            self.emit_match_check(value_register, GuardMode::NotUndefined, span, failures)?;
        }
        match plan {
            DestructuringPlan::Var(name_span) => {
                self.bind_variable(name_span, value_register, span)?;
            }
            DestructuringPlan::Ignore => {}
            DestructuringPlan::EqualityExpr(expected_expr) => {
                let expected_reg =
                    self.compile_rego_expr_with_span(expected_expr, expected_expr.span(), false)?;
                let cmp_reg = self.alloc_register()?;
                self.emit_instruction(
                    Instruction::Eq {
                        dest: cmp_reg,
                        left: value_register,
                        right: expected_reg,
                    },
                    span,
                );
                self.emit_match_check(cmp_reg, GuardMode::Condition, span, failures)?;
            }
            DestructuringPlan::EqualityValue(expected_value) => {
                let expected_reg = self.load_literal_value(expected_value, span)?;
                let cmp_reg = self.alloc_register()?;
                self.emit_instruction(
                    Instruction::Eq {
                        dest: cmp_reg,
                        left: value_register,
                        right: expected_reg,
                    },
                    span,
                );
                self.emit_match_check(cmp_reg, GuardMode::Condition, span, failures)?;
            }
            DestructuringPlan::Array { element_plans } => {
                self.assert_collection_kind(value_register, "is_array", span, failures)?;
                self.assert_array_length(value_register, element_plans.len(), span, failures)?;
                for (index, element_plan) in element_plans.iter().enumerate() {
                    let literal_idx = self.add_literal(Value::from(index));
                    let element_reg = self.alloc_register()?;
                    self.emit_instruction(
                        Instruction::IndexLiteral {
                            dest: element_reg,
                            container: value_register,
                            literal_idx,
                        },
                        span,
                    );
                    self.apply_destructuring_plan_impl(element_plan, element_reg, span, failures)?;
                }
            }
            DestructuringPlan::Object {
                field_plans,
                dynamic_fields,
            } => {
                self.assert_collection_kind(value_register, "is_object", span, failures)?;
                for (key, field_plan) in field_plans {
                    let literal_idx = self.add_literal(key.clone());
                    let field_reg = self.alloc_register()?;
                    self.emit_instruction(
                        Instruction::IndexLiteral {
                            dest: field_reg,
                            container: value_register,
                            literal_idx,
                        },
                        span,
                    );
                    self.apply_destructuring_plan_impl(field_plan, field_reg, span, failures)?;
                }

                for (key_expr, field_plan) in dynamic_fields {
                    let key_reg =
                        self.compile_rego_expr_with_span(key_expr, key_expr.span(), false)?;
                    let field_reg = self.alloc_register()?;
                    self.emit_instruction(
                        Instruction::Index {
                            dest: field_reg,
                            container: value_register,
                            key: key_reg,
                        },
                        span,
                    );
                    self.apply_destructuring_plan_impl(field_plan, field_reg, span, failures)?;
                }
            }
        }
        Ok(())
    }

    fn bind_variable(
        &mut self,
        name_span: &Span,
        value_register: Register,
        span: &Span,
    ) -> Result<()> {
        let var_name = name_span.text();
        if var_name == "_" {
            return Ok(());
        }

        if self.is_var_bound_in_current_scope(var_name) {
            bail!("Variable '{var_name}' already defined in current scope");
        }

        let dest = self.alloc_register()?;
        self.emit_instruction(
            Instruction::Move {
                dest,
                src: value_register,
            },
            span,
        );
        self.add_variable(var_name, dest);

        Ok(())
    }

    fn load_bool_literal(&mut self, value: bool, span: &Span) -> Result<Register> {
        let dest = self.alloc_register()?;
        self.emit_instruction(Instruction::LoadBool { dest, value }, span);
        Ok(dest)
    }

    fn load_literal_value(&mut self, value: &Value, span: &Span) -> Result<Register> {
        let literal_idx = self.add_literal(value.clone());
        let dest = self.alloc_register()?;
        self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
        Ok(dest)
    }

    fn assert_array_length(
        &mut self,
        array_register: Register,
        expected_length: usize,
        span: &Span,
        failures: &mut Vec<usize>,
    ) -> Result<()> {
        let expected_literal = self.add_literal(Value::from(expected_length));
        let actual_len_reg = self.alloc_register()?;
        self.emit_instruction(
            Instruction::Count {
                dest: actual_len_reg,
                collection: array_register,
            },
            span,
        );

        let expected_len_reg = self.alloc_register()?;
        self.emit_instruction(
            Instruction::Load {
                dest: expected_len_reg,
                literal_idx: expected_literal,
            },
            span,
        );

        let cmp_reg = self.alloc_register()?;
        self.emit_instruction(
            Instruction::Eq {
                dest: cmp_reg,
                left: actual_len_reg,
                right: expected_len_reg,
            },
            span,
        );
        self.emit_match_check(cmp_reg, GuardMode::Condition, span, failures)
    }

    fn assert_collection_kind(
        &mut self,
        register: Register,
        builtin: &str,
        span: &Span,
        failures: &mut Vec<usize>,
    ) -> Result<()> {
        let dest = self.alloc_register()?;
        let builtin_index = self.get_builtin_index(builtin)?;
        let params_index = self.program.add_builtin_call_params(BuiltinCallParams {
            dest,
            builtin_index,
            num_args: 1,
            args: [register, 0, 0, 0, 0, 0, 0, 0],
        });
        self.emit_instruction(Instruction::BuiltinCall { params_index }, span);
        self.emit_match_check(dest, GuardMode::Condition, span, failures)
    }
}
