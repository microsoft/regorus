// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::unwrap_used,
    clippy::shadow_unrelated,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

use super::{
    CompilationContext, Compiler, CompilerError, CompilerOptions, ContextType, PrivateRuleKind,
    Result, Scope, WorklistEntry,
};
use crate::ast::{Expr, ExprRef, Rule, RuleHead};
use crate::compiler::destructuring_planner::plans::BindingPlan;
use crate::lexer::Span;
use crate::parser::Parser;
use crate::rvm::instructions::{ArrayCreateParams, FunctionCallParams, GuardMode};
use crate::rvm::program::{Program, RuleType};
use crate::rvm::Instruction;
use crate::utils::{format_string_path, get_path_string};
use crate::Map;
use crate::{CompiledPolicy, Value};
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::convert::TryFrom as _;

type CallableDefaultFunction = (crate::ast::NodeRef<Rule>, Vec<ExprRef>, ExprRef);

fn collect_callable_default_function_paths(policy: &CompiledPolicy) -> Result<BTreeSet<String>> {
    let mut paths = BTreeSet::new();
    if policy.inner.default_rules.is_empty() {
        return Ok(paths);
    }

    for module in policy.get_modules() {
        let mut module_path = None;
        for rule in &module.policy {
            if let Rule::Default { refr, args, .. } = rule.as_ref() {
                if args.is_empty() {
                    continue;
                }

                if module_path.is_none() {
                    module_path = Some(
                        get_path_string(&module.package.refr, Some("data")).map_err(|error| {
                            CompilerError::General {
                                message: format!("Failed to get package path for module: {error}"),
                            }
                            .at(module.package.refr.span())
                        })?,
                    );
                }
                let Some(module_path) = module_path.as_deref() else {
                    return Err(CompilerError::General {
                        message: "Failed to prepare module path for default function".to_string(),
                    }
                    .at(refr.span()));
                };
                let path = get_path_string(refr, Some(module_path)).map_err(|error| {
                    CompilerError::General {
                        message: format!("Failed to get default function path: {error}"),
                    }
                    .at(refr.span())
                })?;
                paths.insert(path);
            }
        }
    }
    Ok(paths)
}

impl<'a> Compiler<'a> {
    /// Extract a compile-time constant `Value` from an optional expression.
    /// Returns `Some(Value::Bool(true))` for the implicit-true case (`expr_ref`
    /// is `None`), delegates to `try_eval_const` for actual expressions.
    fn static_value_of_expr(expr_ref: &Option<ExprRef>) -> Option<Value> {
        match expr_ref {
            None => Some(Value::Bool(true)),
            Some(expr) => super::expressions::try_eval_const(expr.as_ref()),
        }
    }

    pub(super) fn compute_rule_type(&self, rule_path: &str) -> Result<RuleType> {
        let Some(definitions) = self.policy.inner.rules.get(rule_path) else {
            // Default-only rules (e.g., `default deny := true`) have no regular definitions
            // in the `rules` map — they only exist in `default_rules`. Treat them as Complete.
            if self.policy.inner.default_rules.contains_key(rule_path) {
                return Ok(RuleType::Complete);
            }
            return Err(CompilerError::General {
                message: format!("no definitions found for rule path '{}'", rule_path),
            }
            .into());
        };

        let rule_types: BTreeSet<RuleType> = definitions
            .iter()
            .map(|def| {
                if let Rule::Spec { head, .. } = def.as_ref() {
                    match head {
                        RuleHead::Set { .. } => RuleType::PartialSet,
                        RuleHead::Compr { refr, assign, .. } => match refr.as_ref() {
                            crate::ast::Expr::RefBrack { .. } if assign.is_some() => {
                                RuleType::PartialObject
                            }
                            crate::ast::Expr::RefBrack { .. } => RuleType::PartialObject,
                            _ => RuleType::Complete,
                        },
                        _ => RuleType::Complete,
                    }
                } else {
                    RuleType::Complete
                }
            })
            .collect();

        if rule_types.len() > 1 {
            return Err(CompilerError::General {
                message: format!(
                    "internal: rule '{}' has multiple types: {:?}",
                    rule_path, rule_types
                ),
            }
            .into());
        }

        rule_types.into_iter().next().ok_or_else(|| {
            CompilerError::RuleTypeNotFound {
                rule_path: rule_path.to_string(),
            }
            .into()
        })
    }

    fn validate_partial_object_shape(&self, refr: &ExprRef) -> Result<()> {
        let Expr::RefBrack {
            refr: prefix,
            index,
            ..
        } = refr.as_ref()
        else {
            return Ok(());
        };

        if Self::has_unsupported_bracket_prefix(prefix) {
            return Err(CompilerError::PartialObjectNestedKeyUnsupported.at(refr.span()));
        }

        if Self::is_simple_literal(index) {
            return Err(CompilerError::PartialObjectConstantKeyUnsupported.at(index.span()));
        }

        Ok(())
    }

    fn has_unsupported_bracket_prefix(expr: &ExprRef) -> bool {
        match expr.as_ref() {
            Expr::RefBrack { refr, index, .. } => {
                !Self::is_string_literal(index) || Self::has_unsupported_bracket_prefix(refr)
            }
            Expr::RefDot { refr, .. } => Self::has_unsupported_bracket_prefix(refr),
            _ => false,
        }
    }

    fn is_string_literal(expr: &ExprRef) -> bool {
        matches!(expr.as_ref(), Expr::String { .. } | Expr::RawString { .. })
    }

    fn is_simple_literal(expr: &ExprRef) -> bool {
        match expr.as_ref() {
            Expr::String { .. }
            | Expr::RawString { .. }
            | Expr::Number { .. }
            | Expr::Bool { .. }
            | Expr::Null { .. } => true,
            // Unary expressions like `-1` are constant literals too.
            Expr::UnaryExpr { expr, .. } => Self::is_simple_literal(expr),
            _ => false,
        }
    }

    fn ensure_rule_slot(&mut self, index: u16) {
        let index = usize::from(index);
        while self.rule_definitions.len() <= index {
            self.rule_definitions.push(Vec::new());
        }
        while self.rule_definition_function_params.len() <= index {
            self.rule_definition_function_params.push(Vec::new());
        }
        while self.rule_definition_destructuring_patterns.len() <= index {
            self.rule_definition_destructuring_patterns.push(Vec::new());
        }
        while self.rule_definition_else_bodies.len() <= index {
            self.rule_definition_else_bodies.push(Vec::new());
        }
        while self.rule_definition_static_values.len() <= index {
            self.rule_definition_static_values.push(Vec::new());
        }
        while self.rule_types.len() <= index {
            self.rule_types.push(RuleType::Complete);
        }
        while self.rule_function_param_count.len() <= index {
            self.rule_function_param_count.push(None);
        }
        while self.rule_result_registers.len() <= index {
            self.rule_result_registers.push(0);
        }
        while self.rule_num_registers.len() <= index {
            self.rule_num_registers.push(0);
        }
        while self.rule_default_literal_indices.len() <= index {
            self.rule_default_literal_indices.push(None);
        }
    }

    fn allocate_rule_index(&mut self) -> Result<u16> {
        let index = u16::try_from(self.next_rule_index).map_err(|_| CompilerError::General {
            message: "RVM program contains too many rules".to_string(),
        })?;
        self.next_rule_index =
            self.next_rule_index
                .checked_add(1)
                .ok_or_else(|| CompilerError::General {
                    message: "RVM rule index allocation overflow".to_string(),
                })?;
        self.ensure_rule_slot(index);
        Ok(index)
    }

    fn allocate_private_rule(
        &mut self,
        role: &str,
        kind: PrivateRuleKind,
        param_count: usize,
    ) -> Result<(String, u16)> {
        let mut suffix = self.next_rule_index;
        let path = loop {
            let candidate = format!("__regorus_internal_default_{role}_{suffix}");
            if !self.rule_index_map.contains_key(&candidate)
                && !self.policy.inner.rules.contains_key(&candidate)
                && !self.policy.inner.default_rules.contains_key(&candidate)
                && !self.policy.inner.functions.contains_key(&candidate)
            {
                break candidate;
            }
            suffix = suffix
                .checked_add(1)
                .ok_or_else(|| CompilerError::General {
                    message: "private RVM rule name allocation overflow".to_string(),
                })?;
        };
        let index = self.allocate_rule_index()?;
        self.rule_index_map.insert(path.clone(), index);
        self.private_rule_kinds.insert(path.clone(), kind);
        self.rule_function_param_count[usize::from(index)] = Some(param_count);
        self.rule_worklist.push(WorklistEntry::new(
            path.clone(),
            self.current_call_stack.clone(),
        ));
        Ok((path, index))
    }

    pub(super) fn callable_default_function(
        &self,
        rule_path: &str,
    ) -> Result<Option<CallableDefaultFunction>> {
        for (rule, _) in self.exact_default_rules(rule_path)? {
            if let Rule::Default { args, value, .. } = rule.as_ref() {
                if !args.is_empty() {
                    return Ok(Some((rule.clone(), args.clone(), value.clone())));
                }
            }
        }

        Ok(None)
    }

    pub(super) fn exact_default_rules(
        &self,
        rule_path: &str,
    ) -> Result<Vec<(crate::ast::NodeRef<Rule>, Option<String>)>> {
        let Some(default_rules) = self.policy.inner.default_rules.get(rule_path) else {
            return Ok(Vec::new());
        };
        let mut exact_rules = Vec::new();

        for (rule, index) in default_rules {
            if let Rule::Default { refr, args, .. } = rule.as_ref() {
                let (module_package, _) = self.find_module_package_for_rule_ref(rule)?;
                let registration_refr = if args.is_empty() {
                    match (index, refr.as_ref()) {
                        (Some(_), Expr::RefBrack { refr, .. }) => refr,
                        (Some(_), _) => {
                            return Err(CompilerError::General {
                                message: "indexed default rule has no bracket reference"
                                    .to_string(),
                            }
                            .at(refr.span()));
                        }
                        (None, _) => refr,
                    }
                } else {
                    refr
                };
                let default_path = get_path_string(registration_refr, Some(&module_package))
                    .map_err(|error| {
                        CompilerError::General {
                            message: format!("Failed to get default rule path: {error}"),
                        }
                        .at(registration_refr.span())
                    })?;
                if default_path == rule_path {
                    exact_rules.push((rule.clone(), index.clone()));
                }
            }
        }

        Ok(exact_rules)
    }

    fn find_module_package_for_rule_ref(
        &self,
        rule_ref: &crate::ast::NodeRef<Rule>,
    ) -> Result<(String, u32)> {
        let module_index = self.find_module_index_for_rule(rule_ref)?;
        let module = self
            .policy
            .get_modules()
            .get(usize::try_from(module_index).unwrap_or(usize::MAX))
            .ok_or_else(|| CompilerError::General {
                message: "default function rule has no owning module".to_string(),
            })?;
        let package = get_path_string(&module.package.refr, Some("data")).map_err(|error| {
            CompilerError::General {
                message: format!("Failed to get package path for default function: {error}"),
            }
        })?;
        Ok((package, module_index))
    }

    fn set_single_function_definition(
        &mut self,
        rule_index: u16,
        param_names: Vec<String>,
        body_entry_points: Vec<u32>,
        else_bodies: Vec<bool>,
        num_registers: u8,
    ) {
        let index = usize::from(rule_index);
        self.ensure_rule_slot(rule_index);
        self.rule_types[index] = RuleType::Complete;
        self.rule_function_param_count[index] = Some(param_names.len());
        self.rule_result_registers[index] = 0;
        self.rule_num_registers[index] = num_registers;
        self.rule_definitions[index].push(body_entry_points);
        self.rule_definition_function_params[index].push(Some(param_names));
        self.rule_definition_destructuring_patterns[index].push(None);
        self.rule_definition_else_bodies[index].push(else_bodies);
        self.rule_definition_static_values[index].push(None);
    }

    fn compile_runtime_default_body<F>(
        &mut self,
        rule_index: u16,
        default_rule: &crate::ast::NodeRef<Rule>,
        param_count: usize,
        before_value: F,
    ) -> Result<(u32, u8)>
    where
        F: FnOnce(&mut Self) -> Result<()>,
    {
        if param_count > 8 {
            return Err(CompilerError::General {
                message: format!(
                    "RVM function calls support at most 8 parameters, got {param_count}"
                ),
            }
            .into());
        }
        let Rule::Default { value, .. } = default_rule.as_ref() else {
            return Err(CompilerError::General {
                message: "callable default metadata does not refer to a default rule".to_string(),
            }
            .into());
        };
        let value = value.clone();
        let span = value.span().clone();
        let (module_package, module_index) = self.find_module_package_for_rule_ref(default_rule)?;

        let saved_package = core::mem::replace(&mut self.current_package, module_package);
        let saved_module_index = core::mem::replace(&mut self.current_module_index, module_index);
        let saved_register_counter = core::mem::replace(&mut self.register_counter, 0);
        let saved_scopes = core::mem::replace(&mut self.scopes, vec![Scope::default()]);
        let saved_context_stack = core::mem::take(&mut self.context_stack);
        let saved_loop_expr_register_map = core::mem::take(&mut self.loop_expr_register_map);
        let saved_input_register = self.current_input_register.take();
        let saved_data_register = self.current_data_register.take();

        let result = (|| {
            let parameter_registers =
                u8::try_from(param_count).map_err(|_| CompilerError::General {
                    message: format!(
                        "callable default has too many parameters to compile: {param_count}"
                    ),
                })?;
            self.register_counter =
                1_u8.checked_add(parameter_registers)
                    .ok_or_else(|| CompilerError::General {
                        message: "callable default parameter register overflow".to_string(),
                    })?;

            let body_entry_point =
                u32::try_from(self.program.instructions.len()).map_err(|_| {
                    CompilerError::General {
                        message: "RVM program contains too many instructions".to_string(),
                    }
                })?;
            self.reset_rule_definition_registers();
            self.push_context(CompilationContext {
                dest_register: 0,
                context_type: ContextType::Rule(RuleType::Complete),
                key_expr: None,
                value_expr: Some(value.clone()),
                span: span.clone(),
                key_value_loops_hoisted: false,
            });
            self.emit_instruction(
                Instruction::RuleInit {
                    result_reg: 0,
                    rule_index,
                },
                &span,
            );
            before_value(self)?;
            let value_register = self.compile_rego_expr(&value)?;
            self.emit_instruction(
                Instruction::Move {
                    dest: 0,
                    src: value_register,
                },
                &span,
            );
            self.emit_instruction(Instruction::RuleReturn {}, &span);
            Ok((body_entry_point, self.register_counter))
        })();

        self.current_package = saved_package;
        self.current_module_index = saved_module_index;
        self.register_counter = saved_register_counter;
        self.scopes = saved_scopes;
        self.context_stack = saved_context_stack;
        self.loop_expr_register_map = saved_loop_expr_register_map;
        self.current_input_register = saved_input_register;
        self.current_data_register = saved_data_register;

        result
    }

    fn compile_dynamic_default_function(
        &mut self,
        rule_path: &str,
        default_rule: crate::ast::NodeRef<Rule>,
        args: Vec<ExprRef>,
    ) -> Result<()> {
        let Some(&rule_index) = self.rule_index_map.get(rule_path) else {
            return Err(CompilerError::General {
                message: format!("Rule index not found for '{rule_path}'"),
            }
            .into());
        };
        let body_entry_points =
            self.compile_runtime_default_body(rule_index, &default_rule, args.len(), |_| Ok(()))?;
        let param_names = (0..args.len())
            .map(|index| format!("param_{index}"))
            .collect();
        self.set_single_function_definition(
            rule_index,
            param_names,
            vec![body_entry_points.0],
            vec![false],
            body_entry_points.1,
        );
        Ok(())
    }

    fn emit_function_call(
        &mut self,
        dest: u8,
        rule_index: u16,
        argument_registers: &[u8],
        span: &Span,
    ) -> Result<()> {
        if argument_registers.len() > 8 {
            return Err(CompilerError::General {
                message: format!(
                    "RVM function call supports at most 8 arguments, got {}",
                    argument_registers.len()
                ),
            }
            .at(span));
        }
        let num_args = u8::try_from(argument_registers.len()).map_err(|_| {
            CompilerError::General {
                message: "RVM function argument count overflow".to_string(),
            }
            .at(span)
        })?;
        let mut args = [0_u8; 8];
        for (index, &register) in argument_registers.iter().enumerate() {
            args[index] = register;
        }
        let params_index = self.program.add_function_call_params(FunctionCallParams {
            func_rule_index: rule_index,
            dest,
            num_args,
            args,
        });
        self.emit_instruction(Instruction::FunctionCall { params_index }, span);
        Ok(())
    }

    fn wrap_private_ordinary_result(&mut self, rule_path: &str, result_register: u8, span: &Span) {
        if !matches!(
            self.private_rule_kinds.get(rule_path),
            Some(PrivateRuleKind::OrdinaryResult { .. })
        ) {
            return;
        }
        let params_index =
            self.program
                .instruction_data
                .add_array_create_params(ArrayCreateParams {
                    dest: result_register,
                    elements: vec![result_register],
                });
        self.emit_instruction(Instruction::ArrayCreate { params_index }, span);
    }

    fn compile_dynamic_default_wrapper(
        &mut self,
        rule_path: &str,
        default_rule: crate::ast::NodeRef<Rule>,
        default_args: Vec<ExprRef>,
    ) -> Result<()> {
        let Some(&rule_index) = self.rule_index_map.get(rule_path) else {
            return Err(CompilerError::General {
                message: format!("Rule index not found for '{rule_path}'"),
            }
            .into());
        };
        let param_count = self
            .policy
            .inner
            .functions
            .get(rule_path)
            .map(|(_, arity, _)| *arity as usize)
            .unwrap_or(default_args.len());
        if default_args.len() != param_count {
            return Err(CompilerError::General {
                message: format!(
                    "default function '{rule_path}' has {} parameters but the ordinary function has {param_count}",
                    default_args.len()
                ),
            }
            .into());
        }

        let saved_register_counter = core::mem::replace(&mut self.register_counter, 0);
        let result = (|| {
            let (_, helper_index) = self.allocate_private_rule(
                "ordinary_result",
                PrivateRuleKind::OrdinaryResult {
                    source_path: rule_path.to_string(),
                },
                param_count,
            )?;
            let (_, selector_index) = self.allocate_private_rule(
                "selector",
                PrivateRuleKind::DefaultSelector {
                    source_path: rule_path.to_string(),
                },
                1,
            )?;

            let empty_literal_index = self.add_literal(Value::new_array());
            self.rule_default_literal_indices[usize::from(helper_index)] =
                Some(empty_literal_index);

            let param_names: Vec<String> = (0..param_count)
                .map(|index| format!("param_{index}"))
                .collect();
            let body_entry_point =
                u32::try_from(self.program.instructions.len()).map_err(|_| {
                    CompilerError::General {
                        message: "RVM program contains too many instructions".to_string(),
                    }
                })?;
            let parameter_registers =
                u8::try_from(param_count).map_err(|_| CompilerError::General {
                    message: format!("function '{rule_path}' has too many parameters"),
                })?;
            self.register_counter =
                1_u8.checked_add(parameter_registers)
                    .ok_or_else(|| CompilerError::General {
                        message: "function parameter register overflow".to_string(),
                    })?;
            let ordinary_result_register = self.alloc_register();
            let call_arguments: Vec<u8> = (0..param_count)
                .map(|index| {
                    u8::try_from(index + 1).map_err(|_| CompilerError::General {
                        message: "function argument register overflow".to_string(),
                    })
                })
                .collect::<core::result::Result<_, _>>()?;
            self.emit_instruction(
                Instruction::RuleInit {
                    result_reg: 0,
                    rule_index,
                },
                default_rule.span(),
            );
            self.emit_function_call(
                ordinary_result_register,
                helper_index,
                &call_arguments,
                default_rule.span(),
            )?;
            self.emit_function_call(
                0,
                selector_index,
                &[ordinary_result_register],
                default_rule.span(),
            )?;
            self.emit_instruction(Instruction::RuleReturn {}, default_rule.span());
            let num_registers = self.register_counter;
            self.set_single_function_definition(
                rule_index,
                param_names,
                vec![body_entry_point],
                vec![false],
                num_registers,
            );
            Ok(())
        })();
        self.register_counter = saved_register_counter;
        result
    }

    fn compile_default_selector(&mut self, rule_path: &str, source_path: &str) -> Result<()> {
        let Some((default_rule, _args, _value)) = self.callable_default_function(source_path)?
        else {
            return Err(CompilerError::General {
                message: format!("missing callable default for '{source_path}'"),
            }
            .into());
        };
        let Some(&rule_index) = self.rule_index_map.get(rule_path) else {
            return Err(CompilerError::General {
                message: format!("Rule index not found for '{rule_path}'"),
            }
            .into());
        };

        let saved_register_counter = core::mem::replace(&mut self.register_counter, 0);
        let result =
            (|| {
                let first_body_entry_point = u32::try_from(self.program.instructions.len())
                    .map_err(|_| CompilerError::General {
                        message: "RVM program contains too many instructions".to_string(),
                    })?;
                self.register_counter = 2;
                let index_register = self.alloc_register();
                let zero_literal_index = self.add_literal(Value::from(0));
                self.emit_instruction(
                    Instruction::RuleInit {
                        result_reg: 0,
                        rule_index,
                    },
                    default_rule.span(),
                );
                self.emit_instruction(
                    Instruction::IndexLiteral {
                        dest: index_register,
                        container: 1,
                        literal_idx: zero_literal_index,
                    },
                    default_rule.span(),
                );
                self.emit_instruction(
                    Instruction::Guard {
                        register: index_register,
                        mode: GuardMode::NotUndefined,
                    },
                    default_rule.span(),
                );
                self.emit_instruction(
                    Instruction::Move {
                        dest: 0,
                        src: index_register,
                    },
                    default_rule.span(),
                );
                self.emit_instruction(Instruction::RuleReturn {}, default_rule.span());
                let first_body_registers = self.register_counter;

                let empty_literal_index = self.add_literal(Value::new_array());
                let second_body =
                    self.compile_runtime_default_body(rule_index, &default_rule, 1, |compiler| {
                        let empty_register = compiler.alloc_register();
                        compiler.emit_instruction(
                            Instruction::Load {
                                dest: empty_register,
                                literal_idx: empty_literal_index,
                            },
                            default_rule.span(),
                        );
                        compiler.emit_instruction(
                            Instruction::AssertEq {
                                left: 1,
                                right: empty_register,
                            },
                            default_rule.span(),
                        );
                        Ok(())
                    })?;
                let num_registers = core::cmp::max(first_body_registers, second_body.1);
                self.set_single_function_definition(
                    rule_index,
                    vec!["result".to_string()],
                    vec![first_body_entry_point, second_body.0],
                    vec![false, true],
                    num_registers,
                );
                Ok(())
            })();
        self.register_counter = saved_register_counter;
        result
    }

    pub(super) fn get_or_assign_rule_index(&mut self, rule_path: &str) -> Result<u16> {
        if let Some(&index) = self.rule_index_map.get(rule_path) {
            return Ok(index);
        }

        let rule_type = self.compute_rule_type(rule_path)?;
        let index = self.allocate_rule_index()?;

        self.rule_index_map.insert(rule_path.to_string(), index);
        self.rule_types[usize::from(index)] = rule_type;
        let entry = WorklistEntry::new(rule_path.to_string(), self.current_call_stack.clone());
        self.rule_worklist.push(entry);

        if !self.policy.inner.rules.contains_key(rule_path) {
            let default_function_param_count = self
                .callable_default_function(rule_path)?
                .map(|(_, args, _)| args.len());
            if let Some(param_count) = default_function_param_count {
                self.rule_function_param_count[usize::from(index)] = Some(param_count);
            }
        }

        Ok(index)
    }

    fn find_module_index_for_rule(&self, rule_ref: &crate::ast::NodeRef<Rule>) -> Result<u32> {
        let rule = rule_ref.as_ref();

        for (module_idx, module) in self.policy.get_modules().iter().enumerate() {
            for policy_rule in &module.policy {
                if core::ptr::eq(policy_rule.as_ref(), rule) {
                    return Ok(module_idx as u32);
                }
            }
        }

        Ok(0)
    }

    fn find_module_package_and_index_for_rule(
        &self,
        rule_path: &str,
        rules: &Map<String, Vec<crate::ast::NodeRef<Rule>>>,
    ) -> Result<(String, u32)> {
        if let Some(rule_definitions) = rules.get(rule_path) {
            if let Some(first_rule_ref) = rule_definitions.first() {
                let rule = first_rule_ref.as_ref();

                for (module_index, module) in self.policy.get_modules().iter().enumerate() {
                    for policy_rule in &module.policy {
                        if core::ptr::eq(policy_rule.as_ref(), rule) {
                            let package_path =
                                match get_path_string(&module.package.refr, Some("data")) {
                                    Ok(path) => path,
                                    Err(e) => {
                                        return Err(CompilerError::General {
                                            message: format!(
                                                "Failed to get package path for module: {}",
                                                e
                                            ),
                                        }
                                        .into());
                                    }
                                };
                            return Ok((package_path, module_index as u32));
                        }
                    }
                }
            }
        }

        let package_components = self
            .policy
            .inner
            .rule_path_components
            .get(rule_path)
            .ok_or_else(|| CompilerError::General {
                message: format!("missing components for registered rule path '{rule_path}'"),
            })?;
        let (_, package_parts) =
            package_components
                .split_last()
                .ok_or_else(|| CompilerError::General {
                    message: format!("invalid registered rule path '{rule_path}'"),
                })?;
        let package_refs: Vec<&str> = package_parts.iter().map(String::as_str).collect();
        let package =
            format_string_path(&package_refs).map_err(|error| CompilerError::General {
                message: format!("failed to format package path for '{rule_path}': {error}"),
            })?;
        Ok((package, 0))
    }

    /// Compile from a CompiledPolicy to RVM Program.
    ///
    /// Entry-point names are canonical Rego rule paths. Use bracketed string
    /// components for literal keys that are not identifiers, such as
    /// `data.graph.defUniqueName["1.0.0"].deny`.
    pub fn compile_from_policy(
        policy: &CompiledPolicy,
        entry_points: &[&str],
    ) -> Result<Arc<Program>> {
        Self::compile_from_policy_with_host_await(policy, entry_points, &[])
    }

    /// Compile from a CompiledPolicy to RVM Program with registered host-awaitable builtins.
    pub fn compile_from_policy_with_host_await(
        policy: &CompiledPolicy,
        entry_points: &[&str],
        host_await_builtins: &[(&str, usize)],
    ) -> Result<Arc<Program>> {
        let options = CompilerOptions {
            host_await_builtins: host_await_builtins
                .iter()
                .map(|(name, arg_count)| ((*name).to_string(), *arg_count))
                .collect(),
            builtin_policy: crate::rvm::BuiltinPolicy::default(),
        };
        Self::compile_from_policy_with_options(policy, entry_points, &options)
    }

    /// Compile from a CompiledPolicy with host-await registrations and a builtin policy.
    pub fn compile_from_policy_with_options(
        policy: &CompiledPolicy,
        entry_points: &[&str],
        options: &CompilerOptions,
    ) -> Result<Arc<Program>> {
        let mut compiler = Compiler::with_policy(policy);
        for (name, arg_count) in &options.host_await_builtins {
            compiler.register_host_await_builtin(name, *arg_count)?;
        }
        compiler.builtin_policy = options.builtin_policy.clone();
        compiler.default_function_paths = collect_callable_default_function_paths(policy)?;
        if !compiler.builtin_policy.disabled_names().is_empty() {
            super::function_calls::validate_all_modules(&compiler)?;
        }
        compiler.current_rule_path = "".to_string();
        let rules = policy.get_rules();
        let max_components = policy
            .inner
            .rule_path_components
            .values()
            .map(Vec::len)
            .max()
            .unwrap_or_default();

        for &entry_point_name in entry_points {
            compiler.reset_rule_definition_registers();
            let instruction_index = compiler.program.instructions.len();
            let rule_path = if policy.inner.rule_paths.contains(entry_point_name) {
                entry_point_name.to_string()
            } else {
                let components =
                    Parser::parse_static_path_components(entry_point_name, max_components)
                        .map_err(|error| CompilerError::General {
                            message: error.to_string(),
                        })?;
                let component_refs: Vec<&str> = components.iter().map(String::as_str).collect();
                let canonical_path = format_string_path(&component_refs).map_err(|error| {
                    CompilerError::General {
                        message: error.to_string(),
                    }
                })?;
                if policy.inner.rule_paths.contains(&canonical_path) {
                    canonical_path
                } else {
                    entry_point_name.to_string()
                }
            };

            let result_reg = if compiler.is_parameterized_user_function(&rule_path) {
                let span = policy
                    .get_modules()
                    .first()
                    .map(|module| module.package.refr.span())
                    .ok_or_else(|| CompilerError::General {
                        message: format!(
                            "parameterized entrypoint '{entry_point_name}' has no source module"
                        ),
                    })?;
                compiler.compile_parameterized_function_document_path(&rule_path, &[], span)?
            } else {
                let result_reg = compiler.alloc_register();
                let rule_idx = compiler.get_or_assign_rule_index(&rule_path)?;
                compiler.emit_call_rule(result_reg, rule_idx);
                result_reg
            };

            compiler
                .entry_points
                .insert(entry_point_name.to_string(), instruction_index);
            compiler.emit_return(result_reg);
        }

        compiler.compile_worklist_rules(rules)?;

        let program = Arc::new(compiler.finish()?);
        Ok(program)
    }

    fn compile_worklist_rules(
        &mut self,
        rules: &Map<String, Vec<crate::ast::NodeRef<Rule>>>,
    ) -> Result<()> {
        let mut compiled_rules = BTreeSet::new();
        let mut call_stack = Vec::new();

        while !self.rule_worklist.is_empty() {
            let entry = self.rule_worklist.remove(0);

            if let Some(&target_rule_index) = self.rule_index_map.get(&entry.rule_path) {
                if entry.call_stack.contains(&target_rule_index) {
                    let mut chain = Vec::new();
                    let mut found_start = false;
                    for &rule_idx in &entry.call_stack {
                        if rule_idx == target_rule_index {
                            found_start = true;
                        }
                        if found_start {
                            if let Some((rule_path, _)) =
                                self.rule_index_map.iter().find(|(_, &idx)| idx == rule_idx)
                            {
                                chain.push(rule_path.clone());
                            }
                        }
                    }
                    chain.push(entry.rule_path.clone());

                    return Err(CompilerError::General {
                        message: format!(
                            "Compile-time recursion detected in rule call chain: {}",
                            chain.join(" -> ")
                        ),
                    }
                    .into());
                }
            }

            if compiled_rules.contains(&entry.rule_path) {
                continue;
            }

            let rule_index = if let Some(&index) = self.rule_index_map.get(&entry.rule_path) {
                index
            } else {
                return Err(CompilerError::General {
                    message: format!("Rule index not found for '{}'", entry.rule_path),
                }
                .into());
            };

            call_stack.push(entry.rule_path.clone());

            let old_rule_path = self.current_rule_path.clone();
            let old_call_stack = self.current_call_stack.clone();
            self.current_rule_path = entry.rule_path.clone();
            self.current_call_stack = entry.call_stack.clone();
            self.current_call_stack.push(rule_index);

            let result = self.compile_worklist_rule(&entry.rule_path, rules);

            self.current_rule_path = old_rule_path;
            self.current_call_stack = old_call_stack;

            call_stack.pop();

            result?;
            compiled_rules.insert(entry.rule_path);
        }
        Ok(())
    }

    fn compile_worklist_rule(
        &mut self,
        rule_path: &str,
        rules: &Map<String, Vec<crate::ast::NodeRef<Rule>>>,
    ) -> Result<()> {
        if let Some(PrivateRuleKind::DefaultSelector { source_path }) =
            self.private_rule_kinds.get(rule_path).cloned()
        {
            return self.compile_default_selector(rule_path, &source_path);
        }

        let source_rule_path = match self.private_rule_kinds.get(rule_path) {
            Some(PrivateRuleKind::OrdinaryResult { source_path }) => source_path.as_str(),
            _ => rule_path,
        };
        let is_private_result_helper = matches!(
            self.private_rule_kinds.get(rule_path),
            Some(PrivateRuleKind::OrdinaryResult { .. })
        );

        if let Some((default_rule, args, value)) = self.callable_default_function(rule_path)? {
            if super::expressions::try_eval_const(value.as_ref()).is_none() {
                if rules.contains_key(rule_path) {
                    return self.compile_dynamic_default_wrapper(rule_path, default_rule, args);
                }
                return self.compile_dynamic_default_function(rule_path, default_rule, args);
            }
        }

        let (module_package, module_index) =
            self.find_module_package_and_index_for_rule(source_rule_path, rules)?;

        let saved_package = self.current_package.clone();
        let saved_module_index = self.current_module_index;
        self.current_package = module_package.clone();
        self.current_module_index = module_index;

        let saved_register_counter = self.register_counter;
        if let Some(rule_definitions) = rules.get(source_rule_path) {
            let Some(rule_index) = self.rule_index_map.get(rule_path).copied() else {
                return Err(CompilerError::General {
                    message: format!(
                        "Rule '{}' not found in rule index map during compilation",
                        rule_path
                    ),
                }
                .into());
            };
            let rule_type = self.rule_types[rule_index as usize].clone();

            let result_register = 0;

            while self.rule_result_registers.len() <= rule_index as usize {
                self.rule_result_registers.push(0);
            }
            self.rule_result_registers[rule_index as usize] = result_register;

            while self.rule_definitions.len() <= rule_index as usize {
                self.rule_definitions.push(Vec::new());
            }

            while self.rule_definition_function_params.len() <= rule_index as usize {
                self.rule_definition_function_params.push(Vec::new());
            }

            while self.rule_definition_destructuring_patterns.len() <= rule_index as usize {
                self.rule_definition_destructuring_patterns.push(Vec::new());
            }

            while self.rule_definition_else_bodies.len() <= rule_index as usize {
                self.rule_definition_else_bodies.push(Vec::new());
            }

            while self.rule_definition_static_values.len() <= rule_index as usize {
                self.rule_definition_static_values.push(Vec::new());
            }

            let mut num_registers_used = 0;
            let mut rule_param_count: Option<usize> = None;

            for (def_idx, rule_ref) in rule_definitions.iter().enumerate() {
                ::core::convert::identity(def_idx);
                if let Rule::Spec { head, bodies, span } = rule_ref.as_ref() {
                    self.push_scope();
                    self.register_counter = 0;

                    let result_register = self.alloc_register();

                    self.current_module_index = self.find_module_index_for_rule(rule_ref)?;

                    let (key_expr, value_expr) = match head {
                        RuleHead::Compr { refr, assign, .. } => {
                            if rule_type == RuleType::PartialObject {
                                self.validate_partial_object_shape(refr)?;
                            }

                            self.rule_definition_function_params[rule_index as usize].push(None);
                            self.rule_definition_destructuring_patterns[rule_index as usize]
                                .push(None);

                            let output_expr = assign.as_ref().map(|assign| assign.value.clone());
                            let key_expr = match refr.as_ref() {
                                Expr::RefBrack { index, .. } => Some(index.clone()),
                                _ => None,
                            };
                            (key_expr, output_expr)
                        }
                        RuleHead::Set { key, .. } => {
                            self.rule_definition_function_params[rule_index as usize].push(None);
                            self.rule_definition_destructuring_patterns[rule_index as usize]
                                .push(None);

                            (None, key.clone())
                        }
                        RuleHead::Func { assign, args, .. } => {
                            let mut param_names = Vec::new();
                            let mut last_param_span: Option<Span> = None;

                            let destructuring_entry = if args.is_empty() {
                                None
                            } else {
                                Some(self.program.instructions.len())
                            };

                            let param_base_register = self.register_counter;
                            self.register_counter =
                                self.register_counter.saturating_add(args.len() as u8);

                            for (arg_idx, arg) in args.iter().enumerate() {
                                let param_reg = param_base_register + arg_idx as u8;

                                let param_name = match arg.as_ref() {
                                    Expr::Var {
                                        value: Value::String(name),
                                        ..
                                    } => name.to_string(),
                                    _ => format!("__param_{}", arg_idx),
                                };
                                param_names.push(param_name);

                                let context_desc = format!("function parameter {arg_idx}");
                                let binding_plan =
                                    self.expect_binding_plan_for_expr(arg, &context_desc)?;

                                if let BindingPlan::Parameter { .. } = &binding_plan {
                                    let _ = self
                                        .apply_binding_plan(&binding_plan, param_reg, arg.span())
                                        .map_err(|e| CompilerError::from(e).at(arg.span()))?;
                                } else {
                                    return Err(CompilerError::UnexpectedBindingPlan {
                                        context: context_desc,
                                        found: format!("{binding_plan:?}"),
                                    }
                                    .at(arg.span()));
                                }

                                last_param_span = Some(arg.span().clone());
                            }

                            self.rule_definition_function_params[rule_index as usize]
                                .push(Some(param_names.clone()));

                            if let Some(entry) = destructuring_entry {
                                let success_span = last_param_span.as_ref().unwrap_or(span);
                                self.emit_instruction(
                                    crate::rvm::instructions::Instruction::DestructuringSuccess {},
                                    success_span,
                                );
                                self.rule_definition_destructuring_patterns[rule_index as usize]
                                    .push(Some(entry as u32));
                            } else {
                                self.rule_definition_destructuring_patterns[rule_index as usize]
                                    .push(None);
                            }

                            match rule_param_count {
                                None => {
                                    rule_param_count = Some(param_names.len());
                                }
                                Some(expected_count) => {
                                    if param_names.len() != expected_count {
                                        return Err(CompilerError::General {
                                            message: format!(
												"Function rule '{}' definition {} has {} parameters but expected {} parameters",
												rule_path, def_idx, param_names.len(), expected_count
											),
                                        }
                                        .at(span));
                                    }
                                }
                            }

                            match assign {
                                Some(assignment) => (None, Some(assignment.value.clone())),
                                None => (None, None),
                            }
                        }
                    };

                    let span = match (&key_expr, &value_expr) {
                        (_, Some(expr)) => expr.span().clone(),
                        (Some(expr), _) => expr.span().clone(),
                        _ => span.clone(),
                    };

                    let context = CompilationContext {
                        dest_register: result_register,
                        context_type: ContextType::Rule(rule_type.clone()),
                        key_expr,
                        value_expr,
                        span,
                        key_value_loops_hoisted: false,
                    };
                    self.push_context(context);
                    let mut body_entry_points = Vec::new();
                    let mut body_is_else = Vec::new();

                    if bodies.is_empty() {
                        let value_expr_opt = self.context_stack.last().unwrap().value_expr.clone();
                        if let Some(value_expr) = value_expr_opt {
                            let body_entry_point = self.program.instructions.len() as u32;
                            body_entry_points.push(body_entry_point);

                            self.push_scope();
                            self.reset_rule_definition_registers();

                            self.emit_instruction(
                                Instruction::RuleInit {
                                    result_reg: result_register,
                                    rule_index,
                                },
                                value_expr.span(),
                            );

                            self.emit_context_yield()?;

                            self.wrap_private_ordinary_result(
                                rule_path,
                                result_register,
                                value_expr.span(),
                            );
                            self.emit_instruction(Instruction::RuleReturn {}, value_expr.span());
                            self.pop_scope();
                        }
                    } else {
                        for (body_idx, body) in bodies.iter().enumerate() {
                            self.push_scope();
                            self.reset_rule_definition_registers();

                            let body_entry_point = self.program.instructions.len() as u32;
                            body_entry_points.push(body_entry_point);
                            body_is_else.push(body.is_else);

                            ::core::convert::identity(body_idx);

                            let previous_value_expr = self
                                .context_stack
                                .last()
                                .and_then(|ctx| ctx.value_expr.clone());
                            let mut body_value_expr =
                                body.assign.as_ref().map(|assign| assign.value.clone());
                            if body_value_expr.is_none()
                                && (body_idx == 0
                                    || matches!(
                                        rule_type,
                                        RuleType::PartialSet | RuleType::PartialObject
                                    ))
                            {
                                body_value_expr = previous_value_expr.clone();
                            }

                            if let Some(context) = self.context_stack.last_mut() {
                                context.value_expr = body_value_expr.clone();
                            }

                            self.emit_instruction(
                                Instruction::RuleInit {
                                    result_reg: result_register,
                                    rule_index,
                                },
                                &body.span,
                            );

                            if !body.query.stmts.is_empty() {
                                self.compile_query(&body.query)?;
                            } else if let Some(value_expr) = body_value_expr.clone() {
                                let value_reg = self.compile_rego_expr(&value_expr)?;
                                self.emit_instruction(
                                    Instruction::Move {
                                        dest: result_register,
                                        src: value_reg,
                                    },
                                    value_expr.span(),
                                );
                            }

                            self.wrap_private_ordinary_result(
                                rule_path,
                                result_register,
                                &body.span,
                            );
                            self.emit_instruction(Instruction::RuleReturn {}, &body.span);

                            if let Some(context) = self.context_stack.last_mut() {
                                context.value_expr = previous_value_expr;
                            }

                            self.pop_scope();
                        }
                    }

                    self.pop_scope();

                    // Compute this definition's static value for early-exit analysis.
                    // A definition has a known static value if every body (including
                    // else-branches) would produce the same literal.
                    let def_static_value = if bodies.is_empty() {
                        let head_value = self
                            .context_stack
                            .last()
                            .and_then(|ctx| ctx.value_expr.clone());
                        Self::static_value_of_expr(&head_value)
                    } else {
                        let head_value = self
                            .context_stack
                            .last()
                            .and_then(|ctx| ctx.value_expr.clone());
                        let mut consistent: Option<Value> = None;
                        let mut all_same = true;
                        for (bi, b) in bodies.iter().enumerate() {
                            let mut bve: Option<ExprRef> =
                                b.assign.as_ref().map(|a| a.value.clone());
                            if bve.is_none()
                                && (bi == 0
                                    || matches!(
                                        rule_type,
                                        RuleType::PartialSet | RuleType::PartialObject
                                    ))
                            {
                                bve = head_value.clone();
                            }
                            match Self::static_value_of_expr(&bve) {
                                Some(v) => match &consistent {
                                    None => consistent = Some(v),
                                    Some(prev) => {
                                        if *prev != v {
                                            all_same = false;
                                            break;
                                        }
                                    }
                                },
                                None => {
                                    all_same = false;
                                    break;
                                }
                            }
                        }
                        if all_same {
                            consistent
                        } else {
                            None
                        }
                    };
                    let def_static_value = if is_private_result_helper {
                        def_static_value.map(|value| Value::from_array(vec![value]))
                    } else {
                        def_static_value
                    };
                    self.rule_definition_static_values[rule_index as usize].push(def_static_value);

                    self.rule_definitions[rule_index as usize].push(body_entry_points);
                    self.rule_definition_else_bodies[rule_index as usize].push(body_is_else);

                    if self.register_counter > num_registers_used {
                        num_registers_used = self.register_counter;
                    }
                }
            }

            while self.rule_num_registers.len() <= rule_index as usize {
                self.rule_num_registers.push(0);
            }
            self.rule_num_registers[rule_index as usize] = num_registers_used;

            self.rule_function_param_count[rule_index as usize] = rule_param_count;

            if rule_param_count.is_none() {
                let components = self
                    .policy
                    .inner
                    .rule_path_components
                    .get(rule_path)
                    .ok_or_else(|| CompilerError::General {
                        message: format!(
                            "missing components for registered rule path '{rule_path}'"
                        ),
                    })?;
                let (rule_name, package_parts) =
                    components
                        .split_last()
                        .ok_or_else(|| CompilerError::General {
                            message: format!("invalid registered rule path '{rule_path}'"),
                        })?;
                let package_path = package_parts.to_vec();
                let _ =
                    self.program
                        .add_rule_to_tree(&package_path, rule_name, rule_index as usize);
            }

            self.register_counter = saved_register_counter;
            self.current_package = saved_package;
            self.current_module_index = saved_module_index;
        } else {
            // Default-only rule — no body definitions to compile.
            // Ensure rule_num_registers is sized so finish() won't panic.
            if let Some(&rule_index) = self.rule_index_map.get(rule_path) {
                while self.rule_num_registers.len() <= rule_index as usize {
                    self.rule_num_registers.push(0);
                }

                let is_value_rule = self
                    .rule_function_param_count
                    .get(usize::from(rule_index))
                    .ok_or_else(|| CompilerError::General {
                        message: format!(
                            "missing function arity metadata for default-only rule '{rule_path}'"
                        ),
                    })?
                    .is_none();
                if is_value_rule {
                    let components = self
                        .policy
                        .inner
                        .rule_path_components
                        .get(rule_path)
                        .ok_or_else(|| CompilerError::General {
                            message: format!(
                                "missing components for registered rule path '{rule_path}'"
                            ),
                        })?;
                    let (rule_name, package_parts) =
                        components
                            .split_last()
                            .ok_or_else(|| CompilerError::General {
                                message: format!("invalid registered rule path '{rule_path}'"),
                            })?;
                    let package_path = package_parts.to_vec();
                    let _ = self.program.add_rule_to_tree(
                        &package_path,
                        rule_name,
                        usize::from(rule_index),
                    );
                }
            }

            self.register_counter = saved_register_counter;
            self.current_package = saved_package;
            self.current_module_index = saved_module_index;
        }

        Ok(())
    }
}
