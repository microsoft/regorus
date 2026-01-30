// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::arithmetic_side_effects,
    clippy::indexing_slicing,
    clippy::unseparated_literal_suffix,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

use super::{Compiler, CompilerError, Register, Result};
use crate::ast::ExprRef;
use crate::builtins;
use crate::compiler::destructuring_planner::plans::BindingPlan;
use crate::lexer::Span;
use crate::rvm::instructions::{BuiltinCallParams, FunctionCallParams};
use crate::rvm::Instruction;
use crate::utils::get_path_string;
use alloc::{format, string::ToString, vec::Vec};

enum CallTarget {
    User {
        rule_index: u16,
        expected_args: Option<usize>,
    },
    Builtin {
        builtin_index: u16,
        expected_args: Option<usize>,
    },
    HostAwait {
        expected_args: Option<usize>,
    },
}

impl<'a> Compiler<'a> {
    pub(super) fn compile_function_call(
        &mut self,
        fcn: &ExprRef,
        params: &[ExprRef],
        span: Span,
    ) -> Result<Register> {
        let fcn_path = get_path_string(fcn, None)
            .map_err(|_| CompilerError::InvalidFunctionExpression.at(&span))?;

        let original_fcn_path = fcn_path.clone();
        let full_fcn_path = if self.policy.inner.rules.contains_key(&fcn_path) {
            fcn_path
        } else {
            get_path_string(fcn, Some(&self.current_package))
                .map_err(|_| CompilerError::InvalidFunctionExpressionWithPackage.at(&span))?
        };

        let mut out_param_plan: Option<(BindingPlan, Span)> = None;
        let mut params_to_compile = params.len();

        let call_target = self.determine_call_target(&original_fcn_path, &full_fcn_path, &span)?;

        let expected_args = match &call_target {
            CallTarget::User { expected_args, .. } => *expected_args,
            CallTarget::Builtin { expected_args, .. } => *expected_args,
            CallTarget::HostAwait { expected_args } => *expected_args,
        };

        if let Some(expected) = expected_args {
            if params.len() == expected + 1 {
                if let Some(last_param) = params.last() {
                    let plan = self.expect_binding_plan_for_expr(
                        last_param,
                        &format!("extra argument for function '{}'", original_fcn_path),
                    )?;

                    match plan {
                        BindingPlan::Parameter { .. } => {
                            out_param_plan = Some((plan, last_param.span().clone()));
                            params_to_compile -= 1;
                        }
                        other => {
                            return Err(CompilerError::UnexpectedBindingPlan {
                                context: "function extra argument".to_string(),
                                found: format!("{other:?}"),
                            }
                            .at(last_param.span()));
                        }
                    }
                }
            }
        }

        let mut arg_regs = Vec::new();
        for param in params.iter().take(params_to_compile) {
            let param_reg = self.compile_rego_expr_with_span(param, param.span(), false)?;
            arg_regs.push(param_reg);
        }

        let dest = self.alloc_register();

        match call_target {
            CallTarget::User { rule_index, .. } => {
                let mut args_array = [0u8; 8];
                let num_args = arg_regs.len().min(8) as u8;
                for (i, &reg) in arg_regs.iter().take(8).enumerate() {
                    args_array[i] = reg;
                }

                let params_index = self.program.add_function_call_params(FunctionCallParams {
                    func_rule_index: rule_index,
                    dest,
                    num_args,
                    args: args_array,
                });
                self.emit_instruction(Instruction::FunctionCall { params_index }, &span);
            }
            CallTarget::Builtin { builtin_index, .. } => {
                let mut args_array = [0u8; 8];
                let num_args = arg_regs.len().min(8) as u8;
                for (i, &reg) in arg_regs.iter().take(8).enumerate() {
                    args_array[i] = reg;
                }

                let params_index = self.program.add_builtin_call_params(BuiltinCallParams {
                    dest,
                    builtin_index,
                    num_args,
                    args: args_array,
                });
                self.emit_instruction(Instruction::BuiltinCall { params_index }, &span);
            }
            CallTarget::HostAwait { .. } => {
                if arg_regs.len() != 2 {
                    return Err(CompilerError::General {
                        message: format!(
                            "__builtin_host_await expects 2 arguments, got {}",
                            arg_regs.len()
                        ),
                    }
                    .at(&span));
                }

                self.emit_instruction(
                    Instruction::HostAwait {
                        dest,
                        arg: arg_regs[0],
                        id: arg_regs[1],
                    },
                    &span,
                );
            }
        }

        if let Some((plan, plan_span)) = &out_param_plan {
            let plan_result = self
                .apply_binding_plan(plan, dest, plan_span)
                .map_err(|err| CompilerError::from(err).at(plan_span))?;
            if let Some(result_reg) = plan_result {
                self.emit_instruction(
                    Instruction::Move {
                        dest,
                        src: result_reg,
                    },
                    &span,
                );
            } else {
                self.emit_instruction(Instruction::LoadBool { dest, value: true }, &span);
            }
        }

        Ok(dest)
    }

    fn lookup_builtin_arity(&self, name: &str) -> Option<usize> {
        if name == "print" {
            Some(2)
        } else {
            builtins::BUILTINS
                .get(name)
                .map(|(_, arity)| *arity as usize)
        }
    }
}

impl<'a> Compiler<'a> {
    fn determine_call_target(
        &mut self,
        original_fcn_path: &str,
        full_fcn_path: &str,
        span: &Span,
    ) -> Result<CallTarget> {
        if original_fcn_path == "__builtin_host_await" {
            return Ok(CallTarget::HostAwait {
                expected_args: Some(2),
            });
        }

        if self.is_user_defined_function(full_fcn_path) {
            let rule_index = self.get_or_assign_rule_index(full_fcn_path)?;
            let expected_args = self
                .policy
                .inner
                .functions
                .get(full_fcn_path)
                .map(|(_, arity, _)| *arity as usize)
                .or_else(|| {
                    self.rule_function_param_count
                        .get(rule_index as usize)
                        .and_then(|count| *count)
                });
            Ok(CallTarget::User {
                rule_index,
                expected_args,
            })
        } else if self.is_builtin(original_fcn_path) {
            let builtin_index = self.get_builtin_index(original_fcn_path)?;
            let expected_args = self.lookup_builtin_arity(original_fcn_path);
            Ok(CallTarget::Builtin {
                builtin_index,
                expected_args,
            })
        } else {
            Err(CompilerError::UnknownFunction {
                name: original_fcn_path.to_string(),
            }
            .at(span))
        }
    }
}
