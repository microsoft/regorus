// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::as_conversions,
    clippy::pattern_type_mismatch
)]

use super::{Compiler, CompilerError, ComprehensionType, ContextType, Result};
use crate::ast::{self, Expr, ExprRef, LiteralStmt, Query};
use crate::compiler::hoist::{is_safe_literal_key_call, prioritize_key_binding};
use crate::rvm::instructions::GuardMode;
use crate::rvm::program::RuleType;
use crate::rvm::Instruction;
use alloc::format;
use alloc::string::ToString as _;
use alloc::vec::Vec;

impl<'a> Compiler<'a> {
    fn is_safe_projected_key_call(&self, expr: &ExprRef) -> Result<bool> {
        let Expr::Call { fcn, params, .. } = expr.as_ref() else {
            return Ok(false);
        };
        if !is_safe_literal_key_call(fcn, params).map_err(CompilerError::from)? {
            return Ok(false);
        }
        let original_path = crate::utils::get_path_string(fcn, None)
            .map_err(|_| CompilerError::InvalidFunctionExpression)?;
        let full_path = if self.policy.inner.rules.contains_key(&original_path) {
            original_path.clone()
        } else if let Some(resolved) = self.resolve_fcn_path_through_imports(&original_path) {
            resolved
        } else {
            crate::utils::get_path_string(fcn, Some(&self.current_package))
                .map_err(|_| CompilerError::InvalidFunctionExpressionWithPackage)?
        };
        Ok(self.is_builtin(&original_path)
            && !self.is_user_defined_function(&full_path)
            && !self.host_await_builtins.contains_key(&original_path))
    }

    pub(super) fn compile_query(&mut self, query: &Query) -> Result<()> {
        self.push_scope();

        let result = {
            let schedule = match &self.policy.inner.schedule {
                Some(s) => s
                    .queries
                    .get_checked(self.current_module_index, query.qidx)
                    .map_err(|err| {
                        CompilerError::General {
                            message: format!("schedule out of bounds: {err}"),
                        }
                        .at(&query.span)
                    })?,
                None => None,
            };

            let mut ordered_stmts: Vec<&LiteralStmt> = match schedule {
                Some(schedule) => schedule
                    .order
                    .iter()
                    .map(|i| &query.stmts[*i as usize])
                    .collect(),
                None => query.stmts.iter().collect(),
            };
            if let Some(context) = self.context_stack.last() {
                prioritize_key_binding(
                    &mut ordered_stmts,
                    context.key_expr.as_ref(),
                    context.key_filter.as_ref(),
                    |expr| {
                        self.is_safe_projected_key_call(expr)
                            .map_err(|err| anyhow::anyhow!("{err}"))
                    },
                )
                .map_err(|err| {
                    CompilerError::General {
                        message: err.to_string(),
                    }
                    .at(&query.span)
                })?;
            }
            self.hoist_loops_and_compile_statements(&ordered_stmts)
        };

        self.pop_scope();

        result
    }

    pub(super) fn hoist_loops_and_compile_statements(
        &mut self,
        stmts: &[&LiteralStmt],
    ) -> Result<()> {
        if self.hoist_projected_key_loops_before_body(stmts)? {
            return Ok(());
        }
        if let Some(context) = self.context_stack.last() {
            let span = context.span.clone();
            self.emit_key_filter_guard(&span)?;
        }
        for (idx, stmt) in stmts.iter().enumerate() {
            if !stmt.with_mods.is_empty() {
                return Err(CompilerError::WithKeywordUnsupported.at(&stmt.span));
            }
            let loop_exprs = self.get_statement_loops(stmt)?;

            if !loop_exprs.is_empty() {
                self.compile_hoisted_loops(&stmts[idx..], &loop_exprs)?;
                self.emit_key_filter_guard(&stmt.span)?;
                return Ok(());
            }

            if matches!(&stmt.literal, ast::Literal::SomeIn { .. }) {
                if let ast::Literal::SomeIn {
                    ref key,
                    ref value,
                    ref collection,
                    ..
                } = &stmt.literal
                {
                    let some_result_reg = self.compile_some_in_loop_with_remaining_statements(
                        key,
                        value,
                        collection,
                        &stmts[idx..],
                    )?;
                    // Inside an `every` body a `some ... in` acts as a condition
                    // on the current iteration: if it matches nothing the
                    // iteration must fail. Unlike a top-level rule body (where
                    // per-iteration context yields produce the results), the
                    // `every` body has no yield, so the loop result register is
                    // otherwise discarded. Guard on it so a `some` that matches
                    // nothing fails the enclosing `every` iteration.
                    if matches!(
                        self.context_stack.last().map(|c| &c.context_type),
                        Some(ContextType::Every)
                    ) {
                        self.emit_instruction(
                            Instruction::Guard {
                                register: some_result_reg,
                                mode: GuardMode::Condition,
                            },
                            &stmt.span,
                        );
                    }
                    self.emit_key_filter_guard(&stmt.span)?;
                    return Ok(());
                }
            }

            self.compile_single_statement(stmt)?;
            self.emit_key_filter_guard(&stmt.span)?;
        }

        self.hoist_loops_and_emit_context_yield()
    }

    fn hoist_projected_key_loops_before_body(&mut self, stmts: &[&LiteralStmt]) -> Result<bool> {
        let key_expr = match self.context_stack.last() {
            Some(context)
                if matches!(context.context_type, ContextType::Rule(_))
                    && context.key_filter.is_some()
                    && !context.key_loops_hoisted =>
            {
                context.key_expr.clone()
            }
            _ => None,
        };
        let Some(key_expr) = key_expr else {
            return Ok(false);
        };
        let loops = self.get_expr_loops(&key_expr)?;
        if loops.is_empty() {
            return Ok(false);
        }
        let Some(first_loop) = loops.first() else {
            return Ok(false);
        };
        if !crate::compiler::hoist::key_expr_is_ready(
            &first_loop.collection,
            |node| Ok(self.loop_expr_register_map.contains_key(node)),
            |span| self.lookup_variable(span.text()).is_some(),
            |call| self.is_safe_projected_key_call(call).map_err(Into::into),
        )
        .map_err(CompilerError::from)?
        {
            return Ok(false);
        }
        if let Some(context) = self.context_stack.last_mut() {
            context.key_loops_hoisted = true;
        }
        self.compile_hoisted_loops(stmts, &loops)?;
        Ok(true)
    }

    pub(super) fn emit_key_filter_guard(&mut self, span: &crate::lexer::Span) -> Result<()> {
        let Some((expr, filter)) = self.context_stack.last().and_then(|context| {
            if context.key_filter_guarded {
                return None;
            }
            let (ContextType::Rule(_), Some(filter), Some(expr)) = (
                &context.context_type,
                context.key_filter.as_ref(),
                context.key_expr.as_ref(),
            ) else {
                return None;
            };
            Some((expr.clone(), filter.clone()))
        }) else {
            return Ok(());
        };
        if !crate::compiler::hoist::key_expr_is_ready(
            &expr,
            |node| Ok(self.loop_expr_register_map.contains_key(node)),
            |key_span| self.lookup_variable(key_span.text()).is_some(),
            |call| self.is_safe_projected_key_call(call).map_err(Into::into),
        )
        .map_err(CompilerError::from)?
        {
            return Ok(());
        }
        let key_register = self.compile_rego_expr(&expr)?;
        self.emit_key_match_guard(key_register, filter, span);
        if let Some(context) = self.context_stack.last_mut() {
            context.key_filter_guarded = true;
        }
        Ok(())
    }

    fn emit_key_match_guard(
        &mut self,
        key_register: super::Register,
        filter: crate::Value,
        span: &crate::lexer::Span,
    ) {
        let literal_idx = self.add_literal(filter);
        let expected = self.alloc_register();
        self.emit_instruction(
            Instruction::Load {
                dest: expected,
                literal_idx,
            },
            span,
        );
        let matches = self.alloc_register();
        self.emit_instruction(
            Instruction::Eq {
                dest: matches,
                left: key_register,
                right: expected,
            },
            span,
        );
        self.emit_instruction(
            Instruction::Guard {
                register: matches,
                mode: GuardMode::Condition,
            },
            span,
        );
    }

    pub(super) fn hoist_loops_and_emit_context_yield(&mut self) -> Result<()> {
        if let Some(context) = self.context_stack.last() {
            let span = context.span.clone();
            self.emit_key_filter_guard(&span)?;
        }
        if let Some(context) = self.context_stack.last() {
            match &context.context_type {
                ContextType::Every => {
                    return Ok(());
                }
                ContextType::Rule(_) | ContextType::Comprehension(_) => {}
            }
        }

        let (key_expr, value_expr) = match self.context_stack.last_mut() {
            Some(context) => {
                if context.key_value_loops_hoisted {
                    return self.emit_context_yield();
                }
                (context.key_expr.clone(), context.value_expr.clone())
            }
            None => return Ok(()),
        };

        let mut key_value_loops = Vec::new();

        if let Some(expr) = key_expr.as_ref() {
            let key_loops_hoisted = self
                .context_stack
                .last()
                .is_some_and(|context| context.key_loops_hoisted);
            if !key_loops_hoisted && !Self::is_simple_literal(expr) {
                key_value_loops.extend(self.get_expr_loops(expr)?);
            }
        }

        if let Some(expr) = value_expr.as_ref() {
            key_value_loops.extend(self.get_expr_loops(expr)?);
        }

        if let Some(context) = self.context_stack.last() {
            let span = context.span.clone();
            self.emit_key_filter_guard(&span)?;
        }

        if !key_value_loops.is_empty() {
            if let Some(context) = self.context_stack.last_mut() {
                context.key_value_loops_hoisted = true;
            }
            self.compile_hoisted_loops(&[], &key_value_loops)
        } else {
            self.emit_context_yield()
        }
    }

    pub(super) fn emit_context_yield(&mut self) -> Result<()> {
        if let Some(context) = self.context_stack.last().cloned() {
            let dest_register = context.dest_register;
            let span = &context.span;
            let projected_key_register = if context.key_filter.is_some() {
                context
                    .key_expr
                    .as_ref()
                    .map(|expr| self.compile_rego_expr(expr))
                    .transpose()?
            } else {
                None
            };
            if let (Some(key_register), Some(key)) =
                (projected_key_register, context.key_filter.clone())
            {
                self.emit_key_match_guard(key_register, key, span);
            }
            let value_register = match context.value_expr {
                Some(expr) => self.compile_rego_expr(&expr)?,
                None => {
                    let value_reg = self.alloc_register();
                    self.emit_instruction(
                        Instruction::LoadBool {
                            dest: value_reg,
                            value: true,
                        },
                        span,
                    );
                    value_reg
                }
            };

            let key_register = match projected_key_register {
                Some(register) => register,
                None => context
                    .key_expr
                    .map(|key_expr| self.compile_rego_expr(&key_expr))
                    .unwrap_or(Ok(value_register))?,
            };

            match context.context_type {
                ContextType::Comprehension(ComprehensionType::Array) => {
                    self.emit_instruction(
                        Instruction::ComprehensionYield {
                            value_reg: value_register,
                            key_reg: None,
                        },
                        span,
                    );
                }
                ContextType::Comprehension(ComprehensionType::Set) => {
                    self.emit_instruction(
                        Instruction::ComprehensionYield {
                            value_reg: value_register,
                            key_reg: None,
                        },
                        span,
                    );
                }
                ContextType::Rule(RuleType::PartialSet) => {
                    self.emit_instruction(
                        Instruction::SetAdd {
                            set: dest_register,
                            value: value_register,
                        },
                        span,
                    );
                }
                ContextType::Comprehension(ComprehensionType::Object) => {
                    self.emit_instruction(
                        Instruction::ComprehensionYield {
                            value_reg: value_register,
                            key_reg: Some(key_register),
                        },
                        span,
                    );
                }
                ContextType::Rule(RuleType::PartialObject) => {
                    self.emit_instruction(
                        if context.multi_value {
                            Instruction::ObjectSetAdd {
                                obj: dest_register,
                                key: key_register,
                                value: value_register,
                            }
                        } else {
                            Instruction::ObjectSet {
                                obj: dest_register,
                                key: key_register,
                                value: value_register,
                            }
                        },
                        span,
                    );
                }
                ContextType::Rule(RuleType::Complete) => {
                    self.emit_instruction(
                        Instruction::Move {
                            dest: dest_register,
                            src: value_register,
                        },
                        span,
                    );
                }
                ContextType::Every => {}
            }
            Ok(())
        } else {
            Err(CompilerError::MissingYieldContext.into())
        }
    }

    pub(super) fn compile_single_statement(&mut self, stmt: &LiteralStmt) -> Result<()> {
        match &stmt.literal {
            ast::Literal::Expr { expr, .. } => {
                let assert_condition = !matches!(expr.as_ref(), ast::Expr::AssignExpr { .. });
                let _condition_reg =
                    self.compile_rego_expr_with_span(expr, &stmt.span, assert_condition)?;
            }
            ast::Literal::SomeIn { .. } => {
                return Err(CompilerError::SomeInNotHoisted.at(&stmt.span));
            }
            ast::Literal::Every {
                key,
                value,
                domain,
                query,
                ..
            } => {
                self.compile_every_quantifier(key, value, domain, query, &stmt.span)?;
            }
            ast::Literal::SomeVars { vars, .. } => {
                for var in vars {
                    self.add_unbound_variable(var.text());
                }
            }
            ast::Literal::NotExpr { expr, .. } => {
                let expr_reg = self.with_soft_assert_mode(true, |compiler| {
                    compiler.compile_rego_expr_with_span(expr, expr.span(), false)
                })?;

                let negated_reg = self.alloc_register();
                self.emit_instruction(
                    Instruction::Not {
                        dest: negated_reg,
                        operand: expr_reg,
                    },
                    &stmt.span,
                );

                self.emit_instruction(
                    Instruction::Guard {
                        register: negated_reg,
                        mode: GuardMode::Condition,
                    },
                    &stmt.span,
                );
            }
        }
        Ok(())
    }
}
