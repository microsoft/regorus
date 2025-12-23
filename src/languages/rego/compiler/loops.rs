// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

use super::{CompilationContext, Compiler, CompilerError, ContextType, Register, Result};
use crate::ast::{self, ExprRef, LiteralStmt, Query};
use crate::compiler::destructuring_planner::plans::BindingPlan;
use crate::compiler::hoist::{HoistedLoop, LoopType};
use crate::lexer::Span;
use crate::rvm::instructions::{LoopMode, LoopStartParams};
use crate::rvm::Instruction;
use crate::Value;
use alloc::format;
use alloc::string::ToString;
use alloc::vec::Vec;

impl<'a> Compiler<'a> {
    pub(super) fn get_statement_loops(&self, stmt: &LiteralStmt) -> Result<Vec<HoistedLoop>> {
        let loops = self
            .policy
            .inner
            .loop_hoisting_table
            .get_statement_loops(self.current_module_index, stmt.sidx)
            .map_err(|err| {
                CompilerError::General {
                    message: format!("loop hoisting table out of bounds: {err}"),
                }
                .at(&stmt.span)
            })?;

        loops.cloned().ok_or_else(|| {
            CompilerError::General {
                message: format!(
                    "missing loop hoisting data for statement at {}:{}",
                    stmt.span.line, stmt.span.col
                ),
            }
            .at(&stmt.span)
        })
    }

    pub(super) fn get_expr_loops(&self, expr: &ExprRef) -> Result<Vec<HoistedLoop>> {
        let module_idx = self.current_module_index;
        let expr_idx = expr.as_ref().eidx();
        let loops = self
            .policy
            .inner
            .loop_hoisting_table
            .get_expr_loops(module_idx, expr_idx)
            .map_err(|err| {
                CompilerError::General {
                    message: format!("loop hoisting table out of bounds: {err}"),
                }
                .at(expr.span())
            })?;

        loops.cloned().ok_or_else(|| {
            CompilerError::General {
                message: format!(
                    "missing loop hoisting data for expression at {}:{}",
                    expr.span().line,
                    expr.span().col
                ),
            }
            .at(expr.span())
        })
    }

    pub(super) fn compile_hoisted_loops(
        &mut self,
        stmts: &[&LiteralStmt],
        loops: &[HoistedLoop],
    ) -> Result<()> {
        if loops.is_empty() {
            if !stmts.is_empty() {
                self.compile_single_statement(stmts[0])?;
                return self.hoist_loops_and_compile_statements(&stmts[1..]);
            } else {
                self.hoist_loops_and_emit_context_yield()?;
            }
        }

        let current_loop = &loops[0];
        let remaining_loops = &loops[1..];

        match current_loop.loop_type {
            LoopType::IndexIteration => {
                self.compile_index_iteration_loop(
                    &current_loop.loop_expr,
                    &current_loop.key,
                    &current_loop.value,
                    &current_loop.collection,
                    stmts,
                    remaining_loops,
                )?;
                Ok(())
            }
            LoopType::Walk => Err(CompilerError::General {
                message: "walk loops are not yet supported in the RVM compiler".to_string(),
            }
            .into()),
        }
    }

    pub(super) fn compile_every_quantifier(
        &mut self,
        key: &Option<Span>,
        value: &Span,
        domain: &ExprRef,
        query: &Query,
        span: &Span,
    ) -> Result<()> {
        let collection_reg = self.compile_rego_expr(domain)?;

        let key_reg = self.alloc_register();
        let value_reg = self.alloc_register();
        let result_reg = self.alloc_register();

        let value_var_name = value.text().to_string();
        let key_var_name = key.as_ref().map(|k| k.text().to_string());

        let actual_key_reg = if key_var_name.is_none() || key_var_name.as_deref() == Some("_") {
            value_reg
        } else {
            key_reg
        };

        let loop_params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::Every,
            collection: collection_reg,
            key_reg: actual_key_reg,
            value_reg,
            result_reg,
            body_start: 0,
            loop_end: 0,
        });

        self.emit_instruction(
            Instruction::LoopStart {
                params_index: loop_params_index,
            },
            span,
        );

        let body_start = self.program.instructions.len() as u16;

        self.push_scope();

        let every_context = CompilationContext {
            context_type: ContextType::Every,
            dest_register: result_reg,
            key_expr: None,
            value_expr: None,
            span: span.clone(),
            key_value_loops_hoisted: false,
        };
        self.push_context(every_context);

        self.add_variable(&value_var_name, value_reg);
        if let Some(ref key_name) = key_var_name {
            self.add_variable(key_name, key_reg);
        }

        self.compile_query(query)?;

        self.pop_context();
        self.pop_scope();

        self.emit_instruction(
            Instruction::LoopNext {
                body_start,
                loop_end: 0,
            },
            span,
        );

        let loop_end = self.program.instructions.len() as u16;

        self.program
            .update_loop_params(loop_params_index, |params| {
                params.body_start = body_start;
                params.loop_end = loop_end;
            });

        let loop_next_idx = self.program.instructions.len() - 1;
        if let Instruction::LoopNext {
            loop_end: ref mut end,
            ..
        } = &mut self.program.instructions[loop_next_idx]
        {
            *end = loop_end;
        }

        Ok(())
    }

    fn compile_index_iteration_loop(
        &mut self,
        loop_expr: &Option<ExprRef>,
        key_var: &Option<ExprRef>,
        _value_var: &ExprRef,
        collection: &ExprRef,
        remaining_stmts: &[&LiteralStmt],
        remaining_loops: &[HoistedLoop],
    ) -> Result<()> {
        let collection_reg = self.compile_rego_expr(collection)?;

        let key_reg = self.alloc_register();
        let value_reg = self.alloc_register();
        let result_reg = self.alloc_register();

        if let Some(loop_expr) = loop_expr {
            self.loop_expr_register_map
                .insert(loop_expr.clone(), value_reg);
        }

        let mut key_binding_plan: Option<(BindingPlan, Span)> = None;
        if let Some(key_var) = key_var {
            if let Some(binding_plan) = self.get_binding_plan_for_expr(key_var)? {
                if let BindingPlan::LoopIndex { .. } = &binding_plan {
                    key_binding_plan = Some((binding_plan, key_var.span().clone()));
                } else {
                    return Err(CompilerError::UnexpectedBindingPlan {
                        context: format!("loop index pattern {}", key_var.span().text()),
                        found: format!("{binding_plan:?}"),
                    }
                    .at(key_var.span()));
                }
            } else {
                match key_var.as_ref() {
                    ast::Expr::Var { value, .. } => {
                        let var_name = match value {
                            Value::String(s) => {
                                if s.as_ref() == "_" {
                                    "".to_string()
                                } else {
                                    s.to_string()
                                }
                            }
                            _ => value.to_string(),
                        };
                        if !var_name.is_empty() && var_name != "_" {
                            self.store_variable(var_name, key_reg);
                        }
                    }
                    _ => {
                        return Err(CompilerError::MissingBindingPlan {
                            context: format!("loop index pattern {}", key_var.span().text()),
                        }
                        .at(key_var.span()));
                    }
                }
            }
            self.loop_expr_register_map.insert(key_var.clone(), key_reg);
        }

        let loop_params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::ForEach,
            collection: collection_reg,
            key_reg,
            value_reg,
            result_reg,
            body_start: 0,
            loop_end: 0,
        });
        self.emit_instruction(
            Instruction::LoopStart {
                params_index: loop_params_index,
            },
            collection.span(),
        );

        let body_start = self.program.instructions.len() as u16;

        if let Some((binding_plan, plan_span)) = key_binding_plan.as_ref() {
            let _ = self
                .apply_binding_plan(binding_plan, key_reg, plan_span)
                .map_err(|e| CompilerError::from(e).at(plan_span))?;
        }

        let body_stmts = &remaining_stmts[0..];
        self.compile_hoisted_loops(body_stmts, remaining_loops)?;

        self.emit_instruction(
            Instruction::LoopNext {
                body_start,
                loop_end: 0,
            },
            collection.span(),
        );

        let loop_end = self.program.instructions.len() as u16;

        self.program
            .update_loop_params(loop_params_index, |params| {
                params.body_start = body_start;
                params.loop_end = loop_end;
            });

        let loop_next_idx = self.program.instructions.len() - 1;
        if let Instruction::LoopNext {
            loop_end: ref mut end,
            ..
        } = &mut self.program.instructions[loop_next_idx]
        {
            *end = loop_end;
        }

        Ok(())
    }

    pub(super) fn compile_some_in_loop_with_remaining_statements(
        &mut self,
        key: &Option<ExprRef>,
        value: &ExprRef,
        collection: &ExprRef,
        remaining_stmts: &[&LiteralStmt],
    ) -> Result<Register> {
        let loop_body_stmts = &remaining_stmts[1..];
        self.compile_some_in_loop_with_body(key, value, collection, loop_body_stmts)
    }

    fn compile_some_in_loop_with_body(
        &mut self,
        key: &Option<ExprRef>,
        value: &ExprRef,
        collection: &ExprRef,
        loop_body_stmts: &[&LiteralStmt],
    ) -> Result<Register> {
        let collection_reg = self.compile_rego_expr(collection)?;

        let key_reg = self.alloc_register();
        let value_reg = self.alloc_register();
        let result_reg = self.alloc_register();

        let loop_params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::ForEach,
            collection: collection_reg,
            key_reg,
            value_reg,
            result_reg,
            body_start: 0,
            loop_end: 0,
        });
        self.emit_instruction(
            Instruction::LoopStart {
                params_index: loop_params_index,
            },
            collection.span(),
        );

        let body_start = self.program.instructions.len() as u16;

        if let Some(binding_plan) = self.get_binding_plan_for_expr(collection)? {
            if let BindingPlan::SomeIn {
                key_plan,
                value_plan,
                ..
            } = &binding_plan
            {
                let key_register = key_plan.as_ref().map(|_| key_reg);
                self.apply_some_in_binding_plan(
                    key_plan.as_ref(),
                    key_register,
                    value_plan,
                    value_reg,
                    collection.span(),
                )
                .map_err(|e| CompilerError::from(e).at(collection.span()))?;
            } else {
                return Err(CompilerError::UnexpectedBindingPlan {
                    context: format!("some-in binding {}", collection.span().text()),
                    found: format!("{binding_plan:?}"),
                }
                .at(collection.span()));
            }
        } else {
            if let Some(key_expr) = key {
                match key_expr.as_ref() {
                    ast::Expr::Var {
                        value: var_name, ..
                    } => {
                        let var_name = var_name
                            .as_string()
                            .map_err(|err| {
                                CompilerError::General {
                                    message: format!(
                                        "Failed to read some-in key variable name: {err}"
                                    ),
                                }
                                .at(key_expr.span())
                            })?
                            .to_string();
                        self.store_variable(var_name, key_reg);
                    }
                    _ => {
                        return Err(CompilerError::MissingBindingPlan {
                            context: format!("some-in key pattern {}", key_expr.span().text()),
                        }
                        .at(key_expr.span()));
                    }
                }
            }

            match value.as_ref() {
                ast::Expr::Var {
                    value: var_name, ..
                } => {
                    let var_name = var_name
                        .as_string()
                        .map_err(|err| {
                            CompilerError::General {
                                message: format!(
                                    "Failed to read some-in value variable name: {err}"
                                ),
                            }
                            .at(value.span())
                        })?
                        .to_string();
                    self.store_variable(var_name, value_reg);
                }
                _ => {
                    return Err(CompilerError::MissingBindingPlan {
                        context: format!("some-in value pattern {}", value.span().text()),
                    }
                    .at(value.span()));
                }
            }
        }

        self.hoist_loops_and_compile_statements(loop_body_stmts)?;

        self.emit_instruction(
            Instruction::LoopNext {
                body_start,
                loop_end: 0,
            },
            collection.span(),
        );

        let loop_end = self.program.instructions.len() as u16;

        self.program
            .update_loop_params(loop_params_index, |params| {
                params.body_start = body_start;
                params.loop_end = loop_end;
            });

        let loop_next_idx = self.program.instructions.len() - 1;
        if let Instruction::LoopNext {
            loop_end: ref mut end,
            ..
        } = &mut self.program.instructions[loop_next_idx]
        {
            *end = loop_end;
        }

        Ok(result_reg)
    }
}
