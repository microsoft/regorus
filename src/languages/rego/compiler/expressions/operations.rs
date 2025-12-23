// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

use super::{Compiler, CompilerError, Register, Result};
use crate::ast::{ArithOp, BinOp, BoolOp, ExprRef};
use crate::lexer::Span;
use crate::rvm::instructions::BuiltinCallParams;
use crate::rvm::Instruction;
use crate::Value;

impl<'a> Compiler<'a> {
    pub(super) fn compile_arith_expr(
        &mut self,
        lhs: &ExprRef,
        rhs: &ExprRef,
        op: &ArithOp,
        span: &Span,
    ) -> Result<Register> {
        let lhs_reg = self.compile_rego_expr_with_span(lhs, lhs.span(), false)?;
        let rhs_reg = self.compile_rego_expr_with_span(rhs, rhs.span(), false)?;
        let dest = self.alloc_register();

        match op {
            ArithOp::Add => self.emit_instruction(
                Instruction::Add {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
            ArithOp::Sub => self.emit_instruction(
                Instruction::Sub {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
            ArithOp::Mul => self.emit_instruction(
                Instruction::Mul {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
            ArithOp::Div => self.emit_instruction(
                Instruction::Div {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
            ArithOp::Mod => self.emit_instruction(
                Instruction::Mod {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
        }
        Ok(dest)
    }

    pub(super) fn compile_bool_expr(
        &mut self,
        lhs: &ExprRef,
        rhs: &ExprRef,
        op: &BoolOp,
        span: &Span,
    ) -> Result<Register> {
        let lhs_reg = self.compile_rego_expr_with_span(lhs, lhs.span(), false)?;
        let rhs_reg = self.compile_rego_expr_with_span(rhs, rhs.span(), false)?;
        let dest = self.alloc_register();

        match op {
            BoolOp::Eq => self.emit_instruction(
                Instruction::Eq {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
            BoolOp::Lt => self.emit_instruction(
                Instruction::Lt {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
            BoolOp::Gt => self.emit_instruction(
                Instruction::Gt {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
            BoolOp::Ge => self.emit_instruction(
                Instruction::Ge {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
            BoolOp::Le => self.emit_instruction(
                Instruction::Le {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
            BoolOp::Ne => self.emit_instruction(
                Instruction::Ne {
                    dest,
                    left: lhs_reg,
                    right: rhs_reg,
                },
                span,
            ),
        }
        Ok(dest)
    }

    pub(super) fn compile_bin_expr(
        &mut self,
        lhs: &ExprRef,
        rhs: &ExprRef,
        op: &BinOp,
        span: &Span,
    ) -> Result<Register> {
        let lhs_reg = self.compile_rego_expr_with_span(lhs, lhs.span(), false)?;
        let rhs_reg = self.compile_rego_expr_with_span(rhs, rhs.span(), false)?;
        let dest = self.alloc_register();

        match op {
            BinOp::Union => {
                let builtin_index = self.get_builtin_index("__builtin_sets.union")?;
                let params = BuiltinCallParams {
                    dest,
                    builtin_index,
                    num_args: 2,
                    args: [lhs_reg, rhs_reg, 0, 0, 0, 0, 0, 0],
                };
                let params_index = self
                    .program
                    .instruction_data
                    .add_builtin_call_params(params);
                self.emit_instruction(Instruction::BuiltinCall { params_index }, span);
            }
            BinOp::Intersection => {
                let builtin_index = self.get_builtin_index("__builtin_sets.intersection")?;
                let params = BuiltinCallParams {
                    dest,
                    builtin_index,
                    num_args: 2,
                    args: [lhs_reg, rhs_reg, 0, 0, 0, 0, 0, 0],
                };
                let params_index = self
                    .program
                    .instruction_data
                    .add_builtin_call_params(params);
                self.emit_instruction(Instruction::BuiltinCall { params_index }, span);
            }
        }
        Ok(dest)
    }

    pub(super) fn compile_membership(
        &mut self,
        value: &ExprRef,
        collection: &ExprRef,
        span: &Span,
    ) -> Result<Register> {
        let value_reg = self.compile_rego_expr_with_span(value, value.span(), false)?;
        let collection_reg =
            self.compile_rego_expr_with_span(collection, collection.span(), false)?;

        let dest = self.alloc_register();
        self.emit_instruction(
            Instruction::Contains {
                dest,
                collection: collection_reg,
                value: value_reg,
            },
            span,
        );
        Ok(dest)
    }

    pub(super) fn compile_unary_minus(&mut self, expr: &ExprRef, span: &Span) -> Result<Register> {
        match expr.as_ref() {
            crate::ast::Expr::Number { .. } if !expr.span().text().starts_with('-') => {
                let operand_reg = self.compile_rego_expr_with_span(expr, expr.span(), false)?;
                let zero_literal_idx = self.add_literal(Value::from(0));
                let zero_reg = self.alloc_register();
                self.emit_instruction(
                    Instruction::Load {
                        dest: zero_reg,
                        literal_idx: zero_literal_idx,
                    },
                    span,
                );

                let dest = self.alloc_register();
                self.emit_instruction(
                    Instruction::Sub {
                        dest,
                        left: zero_reg,
                        right: operand_reg,
                    },
                    span,
                );
                Ok(dest)
            }
            _ => Err(CompilerError::InvalidUnaryMinus.at(span)),
        }
    }

    #[cfg(feature = "rego-extensions")]
    pub(super) fn compile_or_expr(
        &mut self,
        lhs: &ExprRef,
        rhs: &ExprRef,
        span: &Span,
    ) -> Result<Register> {
        let lhs_reg = self.compile_rego_expr_with_span(lhs, lhs.span(), false)?;
        let rhs_reg = self.compile_rego_expr_with_span(rhs, rhs.span(), false)?;

        let dest = self.alloc_register();
        self.emit_instruction(
            Instruction::Or {
                dest,
                left: lhs_reg,
                right: rhs_reg,
            },
            span,
        );
        Ok(dest)
    }
}
