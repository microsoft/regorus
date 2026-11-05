// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

use super::{Compiler, CompilerError, Register, Result};
use crate::ast::{ArithOp, BinOp, BoolOp, ExprRef};
use crate::lexer::Span;
use crate::rvm::instructions::BuiltinCallParams;
use crate::rvm::Instruction;
use crate::Value;
use alloc::string::ToString as _;

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
        let dest = self.alloc_register()?;

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
        let dest = self.alloc_register()?;

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
        let dest = self.alloc_register()?;

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
        key: Option<&ExprRef>,
        value: &ExprRef,
        collection: &ExprRef,
        span: &Span,
    ) -> Result<Register> {
        let value_reg = self.compile_rego_expr_with_span(value, value.span(), false)?;
        let collection_reg =
            self.compile_rego_expr_with_span(collection, collection.span(), false)?;

        let dest = self.alloc_register()?;
        if let Some(key) = key {
            let is_array_reg = self.alloc_register()?;
            let is_object_reg = self.alloc_register()?;
            for (name, result) in [("is_array", is_array_reg), ("is_object", is_object_reg)] {
                let builtin_index = self.get_builtin_index(name)?;
                let params_index =
                    self.program
                        .instruction_data
                        .add_builtin_call_params(BuiltinCallParams {
                            dest: result,
                            builtin_index,
                            num_args: 1,
                            args: [collection_reg, 0, 0, 0, 0, 0, 0, 0],
                        });
                self.emit_instruction(Instruction::BuiltinCall { params_index }, span);
            }
            self.emit_instruction(
                Instruction::Or {
                    dest: is_array_reg,
                    left: is_array_reg,
                    right: is_object_reg,
                },
                span,
            );
            self.emit_instruction(
                Instruction::Not {
                    dest: is_array_reg,
                    operand: is_array_reg,
                },
                span,
            );
            self.emit_instruction(Instruction::LoadFalse { dest }, span);
            // Invalid containers return false without evaluating the key.
            let branch_index = self.program.instructions.len();
            self.emit_instruction(
                Instruction::AnyOfNext {
                    check: is_array_reg,
                    result: is_array_reg,
                    end_pc: 0,
                },
                span,
            );
            let saved_input_register = self.current_input_register;
            let saved_data_register = self.current_data_register;
            let key_reg = self.compile_rego_expr_with_span(key, key.span(), false)?;
            let indexed_reg = self.alloc_register()?;
            self.emit_instruction(
                Instruction::Index {
                    dest: indexed_reg,
                    container: collection_reg,
                    key: key_reg,
                },
                span,
            );
            self.emit_instruction(
                Instruction::Eq {
                    dest,
                    left: indexed_reg,
                    right: value_reg,
                },
                span,
            );
            // A missing index must yield false, not an undefined comparison.
            self.emit_instruction(
                Instruction::Not {
                    dest,
                    operand: dest,
                },
                span,
            );
            self.emit_instruction(
                Instruction::Not {
                    dest,
                    operand: dest,
                },
                span,
            );

            // Root loads inside the skipped key cannot be reused afterwards.
            self.current_input_register = saved_input_register;
            self.current_data_register = saved_data_register;
            let end_pc = self
                .program
                .instructions
                .len()
                .checked_sub(1)
                .and_then(|pc| u16::try_from(pc).ok())
                .ok_or_else(|| CompilerError::General {
                    message: "membership branch target exceeds the RVM instruction limit"
                        .to_string(),
                })?;
            let Some(Instruction::AnyOfNext {
                end_pc: branch_end_pc,
                ..
            }) = self.program.instructions.get_mut(branch_index)
            else {
                return Err(CompilerError::General {
                    message: "membership branch instruction is missing or invalid".to_string(),
                }
                .into());
            };
            *branch_end_pc = end_pc;
            return Ok(dest);
        }
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
                let zero_reg = self.alloc_register()?;
                self.emit_instruction(
                    Instruction::Load {
                        dest: zero_reg,
                        literal_idx: zero_literal_idx,
                    },
                    span,
                );

                let dest = self.alloc_register()?;
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

        let dest = self.alloc_register()?;
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
