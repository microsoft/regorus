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
use crate::ast::{Expr, ExprRef, Literal, Query, Rule, RuleHead};
use crate::builtins;
use crate::compiler::destructuring_planner::plans::BindingPlan;
use crate::lexer::Span;
use crate::rvm::instructions::{BuiltinCallParams, FunctionCallParams};
use crate::rvm::Instruction;
use crate::utils::{append_path_component, get_path_string, split_canonical_path_root};
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

enum CallIdentity {
    UserDefined { path: String },
    Builtin { name: String },
    ExplicitHostAwait,
    RegisteredHostAwait { identifier: String },
    Unknown { name: String },
}

struct ResolvedCall {
    original_path: String,
    identity: CallIdentity,
}

impl<'a> Compiler<'a> {
    pub(super) fn compile_function_call(
        &mut self,
        fcn: &ExprRef,
        params: &[ExprRef],
        span: Span,
    ) -> Result<Register> {
        let resolved_call = self.resolve_call_identity(fcn, &self.current_package, &span)?;
        let original_fcn_path = resolved_call.original_path.clone();

        let mut out_param_plan: Option<(BindingPlan, Span)> = None;
        let mut params_to_compile = params.len();

        let call_target = self.determine_call_target(resolved_call, &span)?;

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
    fn resolve_fcn_path_through_imports(
        &self,
        path: &str,
        current_package: &str,
    ) -> Option<String> {
        if self.policy.inner.imports.is_empty() {
            return None;
        }
        let (alias, suffix) = split_canonical_path_root(path)?;
        if alias == "data" {
            return None;
        }
        let import_key = append_path_component(current_package, alias).ok()?;
        let import_expr = self.policy.inner.imports.get(&import_key)?;
        let mut candidate = get_path_string(import_expr.as_ref(), None).ok()?;
        candidate.push_str(suffix);
        self.is_user_defined_function(&candidate)
            .then_some(candidate)
    }

    fn resolve_call_identity(
        &self,
        fcn: &ExprRef,
        current_package: &str,
        span: &Span,
    ) -> Result<ResolvedCall> {
        let original_path = get_path_string(fcn, None)
            .map_err(|_| CompilerError::InvalidFunctionExpression.at(span))?;

        let full_path = if self.policy.inner.rules.contains_key(&original_path) {
            original_path.clone()
        } else if let Some(resolved) =
            self.resolve_fcn_path_through_imports(&original_path, current_package)
        {
            resolved
        } else {
            get_path_string(fcn, Some(current_package))
                .map_err(|_| CompilerError::InvalidFunctionExpressionWithPackage.at(span))?
        };

        let identity = if original_path == "__builtin_host_await" {
            CallIdentity::ExplicitHostAwait
        } else if self.host_await_builtins.contains_key(&original_path) {
            CallIdentity::RegisteredHostAwait {
                identifier: original_path.clone(),
            }
        } else if self.is_user_defined_function(&full_path) {
            CallIdentity::UserDefined { path: full_path }
        } else if self.is_builtin(&original_path) {
            CallIdentity::Builtin {
                name: original_path.clone(),
            }
        } else {
            CallIdentity::Unknown {
                name: original_path.clone(),
            }
        };

        Ok(ResolvedCall {
            original_path,
            identity,
        })
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
        resolved_call: ResolvedCall,
        span: &Span,
    ) -> Result<CallTarget> {
        match resolved_call.identity {
            CallIdentity::ExplicitHostAwait => Ok(CallTarget::ExplicitHostAwait),
            CallIdentity::RegisteredHostAwait { identifier } => {
                Ok(CallTarget::RegisteredHostAwait { identifier })
            }
            CallIdentity::UserDefined { path } => {
                let rule_index = self.get_or_assign_rule_index(&path)?;
                let expected_args = self
                    .policy
                    .inner
                    .functions
                    .get(&path)
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
            }
            CallIdentity::Builtin { name } => {
                let builtin_index = self.get_builtin_index(&name)?;
                let expected_args = self.lookup_builtin_arity(&name);
                Ok(CallTarget::Builtin {
                    builtin_index,
                    expected_args,
                })
            }
            CallIdentity::Unknown { name } => Err(CompilerError::UnknownFunction { name }.at(span)),
        }
    }
}

pub(super) fn validate_all_modules(compiler: &Compiler<'_>) -> Result<()> {
    for module in compiler.policy.get_modules() {
        let package = get_path_string(&module.package.refr, Some("data")).map_err(|error| {
            CompilerError::General {
                message: format!("Failed to get package path for module: {error}"),
            }
        })?;
        for rule in &module.policy {
            validate_rule_calls(compiler, &package, rule)?;
        }
    }
    Ok(())
}

fn validate_rule_calls(compiler: &Compiler<'_>, package: &str, rule: &Rule) -> Result<()> {
    match rule {
        Rule::Spec { head, bodies, .. } => {
            match head {
                RuleHead::Compr { refr, assign, .. } => {
                    validate_expr_calls(compiler, package, refr)?;
                    if let Some(assign) = assign {
                        validate_expr_calls(compiler, package, &assign.value)?;
                    }
                }
                RuleHead::Set { refr, key, .. } => {
                    validate_expr_calls(compiler, package, refr)?;
                    if let Some(key) = key {
                        validate_expr_calls(compiler, package, key)?;
                    }
                }
                RuleHead::Func {
                    refr, args, assign, ..
                } => {
                    validate_expr_calls(compiler, package, refr)?;
                    for arg in args {
                        validate_expr_calls(compiler, package, arg)?;
                    }
                    if let Some(assign) = assign {
                        validate_expr_calls(compiler, package, &assign.value)?;
                    }
                }
            }
            for body in bodies {
                if let Some(assign) = &body.assign {
                    validate_expr_calls(compiler, package, &assign.value)?;
                }
                validate_query_calls(compiler, package, &body.query)?;
            }
        }
        Rule::Default {
            refr, args, value, ..
        } => {
            validate_expr_calls(compiler, package, refr)?;
            for arg in args {
                validate_expr_calls(compiler, package, arg)?;
            }
            validate_expr_calls(compiler, package, value)?;
        }
    }
    Ok(())
}

fn validate_query_calls(compiler: &Compiler<'_>, package: &str, query: &Query) -> Result<()> {
    for statement in &query.stmts {
        match &statement.literal {
            Literal::SomeVars { .. } => {}
            Literal::SomeIn {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key) = key {
                    validate_expr_calls(compiler, package, key)?;
                }
                validate_expr_calls(compiler, package, value)?;
                validate_expr_calls(compiler, package, collection)?;
            }
            Literal::Expr { expr, .. } | Literal::NotExpr { expr, .. } => {
                validate_expr_calls(compiler, package, expr)?;
            }
            Literal::Every {
                domain,
                query: every_query,
                ..
            } => {
                validate_expr_calls(compiler, package, domain)?;
                validate_query_calls(compiler, package, every_query)?;
            }
        }
        for modifier in &statement.with_mods {
            validate_expr_calls(compiler, package, &modifier.refr)?;
            validate_expr_calls(compiler, package, &modifier.r#as)?;
        }
    }
    Ok(())
}

fn validate_expr_calls(compiler: &Compiler<'_>, package: &str, expr: &ExprRef) -> Result<()> {
    if let Expr::Call {
        fcn, params, span, ..
    } = expr.as_ref()
    {
        if let Ok(resolved) = compiler.resolve_call_identity(fcn, package, span) {
            let disabled_name = match resolved.identity {
                CallIdentity::Builtin { name }
                | CallIdentity::RegisteredHostAwait { identifier: name } => Some(name),
                CallIdentity::ExplicitHostAwait => params
                    .get(1)
                    .and_then(string_literal)
                    .map(ToString::to_string),
                CallIdentity::UserDefined { .. } | CallIdentity::Unknown { .. } => None,
            };
            if let Some(name) = disabled_name {
                if compiler.builtin_policy.is_disabled(&name) {
                    return Err(CompilerError::BuiltinDisabled { name }.at(span));
                }
            }
        }

        validate_expr_calls(compiler, package, fcn)?;
        for param in params {
            validate_expr_calls(compiler, package, param)?;
        }
        return Ok(());
    }

    match expr.as_ref() {
        Expr::Array { items, .. } | Expr::Set { items, .. } => {
            for item in items {
                validate_expr_calls(compiler, package, item)?;
            }
        }
        Expr::Object { fields, .. } => {
            for (_, key, value) in fields {
                validate_expr_calls(compiler, package, key)?;
                validate_expr_calls(compiler, package, value)?;
            }
        }
        Expr::ArrayCompr { term, query, .. } | Expr::SetCompr { term, query, .. } => {
            validate_expr_calls(compiler, package, term)?;
            validate_query_calls(compiler, package, query)?;
        }
        Expr::ObjectCompr {
            key, value, query, ..
        } => {
            validate_expr_calls(compiler, package, key)?;
            validate_expr_calls(compiler, package, value)?;
            validate_query_calls(compiler, package, query)?;
        }
        Expr::UnaryExpr { expr, .. } => validate_expr_calls(compiler, package, expr)?,
        Expr::RefDot { refr, .. } => validate_expr_calls(compiler, package, refr)?,
        Expr::RefBrack { refr, index, .. } => {
            validate_expr_calls(compiler, package, refr)?;
            validate_expr_calls(compiler, package, index)?;
        }
        Expr::BinExpr { lhs, rhs, .. }
        | Expr::BoolExpr { lhs, rhs, .. }
        | Expr::ArithExpr { lhs, rhs, .. }
        | Expr::AssignExpr { lhs, rhs, .. } => {
            validate_expr_calls(compiler, package, lhs)?;
            validate_expr_calls(compiler, package, rhs)?;
        }
        Expr::Membership {
            key,
            value,
            collection,
            ..
        } => {
            if let Some(key) = key {
                validate_expr_calls(compiler, package, key)?;
            }
            validate_expr_calls(compiler, package, value)?;
            validate_expr_calls(compiler, package, collection)?;
        }
        Expr::String { .. }
        | Expr::RawString { .. }
        | Expr::Number { .. }
        | Expr::Bool { .. }
        | Expr::Null { .. }
        | Expr::Var { .. } => {}
        #[cfg(feature = "rego-extensions")]
        Expr::OrExpr { lhs, rhs, .. } => {
            validate_expr_calls(compiler, package, lhs)?;
            validate_expr_calls(compiler, package, rhs)?;
        }
        Expr::Call { .. } => {}
    }
    Ok(())
}

fn string_literal(expr: &ExprRef) -> Option<&str> {
    match expr.as_ref() {
        Expr::String {
            value: Value::String(value),
            ..
        }
        | Expr::RawString {
            value: Value::String(value),
            ..
        } => Some(value.as_ref()),
        _ => None,
    }
}
