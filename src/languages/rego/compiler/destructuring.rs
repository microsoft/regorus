// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]
use super::Compiler;
use super::Register;
use crate::compiler::destructuring_planner::plans::{
    AssignmentPlan, BindingPlan, DestructuringPlan, WildcardSide,
};
use crate::lexer::Span;
use crate::rvm::instructions::Instruction;
use crate::value::Value;
use anyhow::{bail, Result};

#[derive(Clone, Copy, Debug)]
pub enum PlanContext {
    ColonAssignment,
    Assignment,
    FunctionParameter,
    LoopIndex,
    SomeIn,
}

impl PlanContext {
    fn require_defined_values(self) -> bool {
        matches!(
            self,
            PlanContext::Assignment
                | PlanContext::FunctionParameter
                | PlanContext::LoopIndex
                | PlanContext::SomeIn
        )
    }
}

impl<'a> Compiler<'a> {
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
                let _ = self.apply_destructuring_plan(
                    lhs_plan,
                    rhs_reg,
                    span,
                    PlanContext::Assignment,
                )?;
                Ok(self.load_bool_literal(true, span))
            }
            AssignmentPlan::EqualsBindRight {
                lhs_expr, rhs_plan, ..
            } => {
                let lhs_reg = self.compile_rego_expr_with_span(lhs_expr, lhs_expr.span(), false)?;
                let _ = self.apply_destructuring_plan(
                    rhs_plan,
                    lhs_reg,
                    span,
                    PlanContext::Assignment,
                )?;
                Ok(self.load_bool_literal(true, span))
            }
            AssignmentPlan::EqualsBothSides { element_pairs, .. } => {
                for (value_expr, value_plan) in element_pairs {
                    let value_reg =
                        self.compile_rego_expr_with_span(value_expr, value_expr.span(), false)?;
                    let _ = self.apply_destructuring_plan(
                        value_plan,
                        value_reg,
                        span,
                        PlanContext::Assignment,
                    )?;
                }
                Ok(self.load_bool_literal(true, span))
            }
            AssignmentPlan::EqualityCheck { lhs_expr, rhs_expr } => {
                let lhs_reg = self.compile_rego_expr_with_span(lhs_expr, lhs_expr.span(), false)?;
                let rhs_reg = self.compile_rego_expr_with_span(rhs_expr, rhs_expr.span(), false)?;
                let dest = self.alloc_register();
                self.emit_instruction(
                    Instruction::Eq {
                        dest,
                        left: lhs_reg,
                        right: rhs_reg,
                    },
                    span,
                );
                if !self.soft_assert_mode {
                    self.emit_instruction(Instruction::AssertCondition { condition: dest }, span);
                }
                Ok(dest)
            }
            AssignmentPlan::WildcardMatch {
                lhs_expr,
                rhs_expr,
                wildcard_side,
            } => match wildcard_side {
                WildcardSide::Both => Ok(self.load_bool_literal(true, span)),
                WildcardSide::Lhs => {
                    let rhs_reg =
                        self.compile_rego_expr_with_span(rhs_expr, rhs_expr.span(), false)?;
                    self.emit_instruction(
                        Instruction::AssertNotUndefined { register: rhs_reg },
                        span,
                    );
                    Ok(self.load_bool_literal(true, span))
                }
                WildcardSide::Rhs => {
                    let lhs_reg =
                        self.compile_rego_expr_with_span(lhs_expr, lhs_expr.span(), false)?;
                    self.emit_instruction(
                        Instruction::AssertNotUndefined { register: lhs_reg },
                        span,
                    );
                    Ok(self.load_bool_literal(true, span))
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
        value_plan: &DestructuringPlan,
        value_register: Register,
        span: &Span,
    ) -> Result<()> {
        if let (Some(plan), Some(register)) = (key_plan, key_register) {
            let _ = self.apply_destructuring_plan(plan, register, span, PlanContext::SomeIn)?;
        }
        let _ =
            self.apply_destructuring_plan(value_plan, value_register, span, PlanContext::SomeIn)?;
        Ok(())
    }

    fn apply_destructuring_plan(
        &mut self,
        plan: &DestructuringPlan,
        value_register: Register,
        span: &Span,
        context: PlanContext,
    ) -> Result<Option<Register>> {
        match plan {
            DestructuringPlan::Var(name_span) => {
                self.bind_variable(name_span, value_register, span, context)?;
            }
            DestructuringPlan::Ignore => {}
            DestructuringPlan::EqualityExpr(expected_expr) => {
                let expected_reg =
                    self.compile_rego_expr_with_span(expected_expr, expected_expr.span(), false)?;
                let cmp_reg = self.alloc_register();
                self.emit_instruction(
                    Instruction::Eq {
                        dest: cmp_reg,
                        left: value_register,
                        right: expected_reg,
                    },
                    span,
                );
                if self.soft_assert_mode {
                    return Ok(Some(cmp_reg));
                }
                self.emit_instruction(Instruction::AssertCondition { condition: cmp_reg }, span);
            }
            DestructuringPlan::EqualityValue(expected_value) => {
                let expected_reg = self.load_literal_value(expected_value, span);
                let cmp_reg = self.alloc_register();
                self.emit_instruction(
                    Instruction::Eq {
                        dest: cmp_reg,
                        left: value_register,
                        right: expected_reg,
                    },
                    span,
                );
                if self.soft_assert_mode {
                    return Ok(Some(cmp_reg));
                }
                self.emit_instruction(Instruction::AssertCondition { condition: cmp_reg }, span);
            }
            DestructuringPlan::Array { element_plans } => {
                self.assert_array_length(value_register, element_plans.len(), span)?;
                for (index, element_plan) in element_plans.iter().enumerate() {
                    let literal_idx = self.add_literal(Value::from(index));
                    let element_reg = self.alloc_register();
                    self.emit_instruction(
                        Instruction::IndexLiteral {
                            dest: element_reg,
                            container: value_register,
                            literal_idx,
                        },
                        span,
                    );
                    if context.require_defined_values() {
                        self.emit_instruction(
                            Instruction::AssertNotUndefined {
                                register: element_reg,
                            },
                            span,
                        );
                    }
                    let _ =
                        self.apply_destructuring_plan(element_plan, element_reg, span, context)?;
                }
            }
            DestructuringPlan::Object {
                field_plans,
                dynamic_fields,
            } => {
                for (key, field_plan) in field_plans {
                    let literal_idx = self.add_literal(key.clone());
                    let field_reg = self.alloc_register();
                    self.emit_instruction(
                        Instruction::IndexLiteral {
                            dest: field_reg,
                            container: value_register,
                            literal_idx,
                        },
                        span,
                    );
                    self.emit_instruction(
                        Instruction::AssertNotUndefined {
                            register: field_reg,
                        },
                        span,
                    );
                    let _ = self.apply_destructuring_plan(field_plan, field_reg, span, context)?;
                }

                for (key_expr, field_plan) in dynamic_fields {
                    let key_reg =
                        self.compile_rego_expr_with_span(key_expr, key_expr.span(), false)?;
                    let field_reg = self.alloc_register();
                    self.emit_instruction(
                        Instruction::Index {
                            dest: field_reg,
                            container: value_register,
                            key: key_reg,
                        },
                        span,
                    );
                    self.emit_instruction(
                        Instruction::AssertNotUndefined {
                            register: field_reg,
                        },
                        span,
                    );
                    let _ = self.apply_destructuring_plan(field_plan, field_reg, span, context)?;
                }
            }
        }
        Ok(None)
    }

    fn bind_variable(
        &mut self,
        name_span: &Span,
        value_register: Register,
        span: &Span,
        context: PlanContext,
    ) -> Result<()> {
        let var_name = name_span.text();
        if var_name == "_" {
            return Ok(());
        }

        if self.is_var_bound_in_current_scope(var_name) {
            bail!("Variable '{var_name}' already defined in current scope");
        }

        let dest = self.alloc_register();
        self.emit_instruction(
            Instruction::Move {
                dest,
                src: value_register,
            },
            span,
        );
        self.add_variable(var_name, dest);

        if context.require_defined_values() {
            self.emit_instruction(Instruction::AssertNotUndefined { register: dest }, span);
        }

        Ok(())
    }

    fn load_bool_literal(&mut self, value: bool, span: &Span) -> Register {
        let dest = self.alloc_register();
        self.emit_instruction(Instruction::LoadBool { dest, value }, span);
        dest
    }

    fn load_literal_value(&mut self, value: &Value, span: &Span) -> Register {
        let literal_idx = self.add_literal(value.clone());
        let dest = self.alloc_register();
        self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
        dest
    }

    fn assert_array_length(
        &mut self,
        array_register: Register,
        expected_length: usize,
        span: &Span,
    ) -> Result<()> {
        let expected_literal = self.add_literal(Value::from(expected_length));
        let actual_len_reg = self.alloc_register();
        self.emit_instruction(
            Instruction::Count {
                dest: actual_len_reg,
                collection: array_register,
            },
            span,
        );

        let expected_len_reg = self.alloc_register();
        self.emit_instruction(
            Instruction::Load {
                dest: expected_len_reg,
                literal_idx: expected_literal,
            },
            span,
        );

        let cmp_reg = self.alloc_register();
        self.emit_instruction(
            Instruction::Eq {
                dest: cmp_reg,
                left: actual_len_reg,
                right: expected_len_reg,
            },
            span,
        );
        self.emit_instruction(Instruction::AssertCondition { condition: cmp_reg }, span);
        Ok(())
    }
}
