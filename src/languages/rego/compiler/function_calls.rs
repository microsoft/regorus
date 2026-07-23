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
use crate::value::Value;
use alloc::{
    format,
    string::{String, ToString},
    vec::Vec,
};

/// Resolved destination of a Rego function-call expression. Produced by
/// [`Compiler::determine_call_target`] and consumed by
/// [`Compiler::compile_function_call`] to choose which instruction to emit.
/// Carrying the discrimination in the type (rather than re-matching on a
/// magic name at the emit site) keeps the host-await handling honest under
/// future refactors — the compiler will refuse to build if a new variant is
/// added without updating every match site.
enum CallTarget {
    User {
        rule_index: u16,
        expected_args: Option<usize>,
    },
    Builtin {
        builtin_index: u16,
        expected_args: Option<usize>,
    },
    /// Explicit `__builtin_host_await(arg, id)` call form (2 user args).
    /// The identifier is supplied by the policy author at runtime via the
    /// second argument register.
    ExplicitHostAwait,
    /// A registered host-awaitable builtin invoked by its registered name
    /// (1 user arg). The identifier is the registered name itself and is
    /// baked into the bytecode as a string literal at compile time.
    RegisteredHostAwait { identifier: String },
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
        } else if let Some(resolved) = self.resolve_fcn_path_through_imports(&original_fcn_path) {
            // Resolve a leading import alias before module-prefixing and builtins.
            resolved
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
            // Both host-await variants have a known fixed arity; carrying it
            // in the variant lets the rest of the compiler depend on the type
            // rather than re-matching on the magic name `__builtin_host_await`.
            CallTarget::ExplicitHostAwait => Some(2),
            CallTarget::RegisteredHostAwait { .. } => Some(1),
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
            CallTarget::ExplicitHostAwait => {
                // Explicit __builtin_host_await(arg, id) — 2 arguments
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
            CallTarget::RegisteredHostAwait { identifier } => {
                // Registered host-awaitable builtin — the identifier is the
                // registered name and is baked into the bytecode as a literal.
                if arg_regs.len() != 1 {
                    return Err(CompilerError::General {
                        message: format!(
                            "host-awaitable builtin '{}' expects exactly 1 argument, got {}",
                            identifier,
                            arg_regs.len()
                        ),
                    }
                    .at(&span));
                }
                let id_reg = self.alloc_register();
                let literal_idx = self.add_literal(Value::String(identifier.into()));
                self.emit_instruction(
                    Instruction::Load {
                        dest: id_reg,
                        literal_idx,
                    },
                    &span,
                );
                self.emit_instruction(
                    Instruction::HostAwait {
                        dest,
                        arg: arg_regs[0],
                        id: id_reg,
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

    /// Rewrite an import-aliased call path to its target, e.g. `b.f(1)` to
    /// `data.a.b.f` after `import data.a.b`. Resolves only when the target is
    /// a known function (the `rules` map cannot be used here: it also indexes
    /// value rules and every rule-path prefix, which must not become callable
    /// through an alias), so an alias whose target defines the called
    /// function shadows a like-named builtin namespace, while other spellings
    /// keep their prior meaning (e.g. a builtin call). OPA instead rewrites
    /// aliases unconditionally and rejects calls to a missing target at
    /// compile time.
    fn resolve_fcn_path_through_imports(&self, path: &str) -> Option<String> {
        if self.policy.inner.imports.is_empty() || path.starts_with("data.") {
            return None;
        }
        let (alias, rest) = match path.split_once('.') {
            Some((alias, rest)) => (alias, Some(rest)),
            None => (path, None),
        };
        let import_key = format!("{}.{}", self.current_package, alias);
        let import_expr = self.policy.inner.imports.get(&import_key)?;
        let target = get_path_string(import_expr, None).ok()?;
        let candidate = match rest {
            Some(rest) => format!("{target}.{rest}"),
            None => target,
        };
        self.policy
            .inner
            .functions
            .contains_key(&candidate)
            .then_some(candidate)
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
            return Ok(CallTarget::ExplicitHostAwait);
        }

        // Check registered host-awaitable builtins. Registered builtins are
        // restricted to arg_count == 1 at registration time (see
        // `Compiler::register_host_await_builtin`), so the variant doesn't
        // need to carry an arity — it's fixed at 1.
        //
        // We deliberately match against `original_fcn_path` only, not
        // `full_fcn_path`. Registration intercepts the *unqualified* call
        // form (e.g. `lookup(x)` inside the policy's own package). A
        // package-qualified call like `data.other.lookup(x)` is left to
        // resolve through the normal user-defined / builtin path, so a
        // registered name does not leak into unrelated packages that
        // happen to expose a rule with the same identifier. This is
        // documented on `register_host_await_builtin`; the
        // `registered_host_await.yaml` suite pins the behavior.
        if self.host_await_builtins.contains_key(original_fcn_path) {
            return Ok(CallTarget::RegisteredHostAwait {
                identifier: original_fcn_path.to_string(),
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
