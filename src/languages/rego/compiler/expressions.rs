// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::unused_trait_names, clippy::pattern_type_mismatch)]

mod collection_literals;
mod operations;

use super::{Compiler, CompilerError, Register, Result};
use crate::ast::{Expr, ExprRef};
use crate::compiler::destructuring_planner::plans::BindingPlan;
use crate::lexer::Span;
use crate::rvm::Instruction;
use crate::Value;
use alloc::{format, string::ToString};

impl<'a> Compiler<'a> {
    /// Compile a Rego expression to RVM instructions
    pub fn compile_rego_expr(&mut self, expr: &ExprRef) -> Result<Register> {
        self.compile_rego_expr_with_span(expr, expr.span(), false)
    }

    /// Compile a Rego expression to RVM instructions with span tracking
    pub fn compile_rego_expr_with_span(
        &mut self,
        expr: &ExprRef,
        span: &Span,
        assert_condition: bool,
    ) -> Result<Register> {
        if let Some(reg) = self.loop_expr_register_map.get(expr).cloned() {
            let result_reg = reg;
            if assert_condition {
                self.emit_instruction(
                    Instruction::AssertCondition {
                        condition: result_reg,
                    },
                    span,
                );
            }
            return Ok(result_reg);
        }

        let result_reg = match expr.as_ref() {
            Expr::Number { value, .. }
            | Expr::String { value, .. }
            | Expr::RawString { value, .. }
            | Expr::Bool { value, .. } => {
                let dest = self.alloc_register();
                let literal_idx = self.add_literal(value.clone());
                self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
                dest
            }
            Expr::Null { .. } => {
                let dest = self.alloc_register();
                let literal_idx = self.add_literal(Value::Null);
                self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
                dest
            }
            Expr::Array { items, .. } => self.compile_array_literal(items, span)?,
            Expr::Set { items, .. } => self.compile_set_literal(items, span)?,
            Expr::Object { fields, .. } => self.compile_object_literal(fields, span)?,
            Expr::ArithExpr { lhs, op, rhs, .. } => self.compile_arith_expr(lhs, rhs, op, span)?,
            Expr::BoolExpr { lhs, op, rhs, .. } => self.compile_bool_expr(lhs, rhs, op, span)?,
            Expr::AssignExpr { .. } => {
                let binding_plan =
                    self.expect_binding_plan_for_expr(expr, "assignment expression")?;

                let result: Result<Register> = match binding_plan {
                    BindingPlan::Assignment { plan } => self
                        .compile_assignment_plan_using_hoisted_destructuring(&plan, span)
                        .map_err(|e| CompilerError::from(e).at(span)),
                    other => Err(CompilerError::UnexpectedBindingPlan {
                        context: "assignment expression".to_string(),
                        found: format!("{other:?}"),
                    }
                    .at(span)),
                };

                return result;
            }
            Expr::Var { value, .. } => {
                if let Value::String(_var_name) = value {
                    self.compile_chained_ref(expr, span)?
                } else {
                    let dest = self.alloc_register();
                    let literal_idx = self.add_literal(value.clone());
                    self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
                    dest
                }
            }
            Expr::RefDot { .. } | Expr::RefBrack { .. } => self.compile_chained_ref(expr, span)?,
            Expr::Membership {
                value, collection, ..
            } => self.compile_membership(value, collection, span)?,
            Expr::ArrayCompr { term, query, .. } => {
                self.compile_array_comprehension(term, query, span)?
            }
            Expr::SetCompr { term, query, .. } => {
                self.compile_set_comprehension(term, query, span)?
            }
            Expr::ObjectCompr {
                key, value, query, ..
            } => self.compile_object_comprehension(key, value, query, span)?,
            Expr::Call { fcn, params, .. } => {
                self.compile_function_call(fcn, params, span.clone())?
            }
            Expr::UnaryExpr { expr, .. } => self.compile_unary_minus(expr, span)?,
            Expr::BinExpr { op, lhs, rhs, .. } => self.compile_bin_expr(lhs, rhs, op, span)?,
            #[cfg(feature = "rego-extensions")]
            Expr::OrExpr { lhs, rhs, .. } => self.compile_or_expr(lhs, rhs, span)?,
        };

        if assert_condition {
            self.emit_instruction(
                Instruction::AssertCondition {
                    condition: result_reg,
                },
                span,
            );
        }

        Ok(result_reg)
    }
}
