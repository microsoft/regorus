// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

use super::{Compiler, CompilerError, Result};
use crate::ast::{Expr, Literal, Query, Rule};
use crate::builtins;
use crate::compiler::context::ScopeContext;
use crate::interpreter::Interpreter;
use crate::lexer::Source;
use crate::rvm::program::{Program, RuleType, SpanInfo};
use crate::rvm::Instruction;
use crate::utils::get_path_string;
use crate::Rc;
use crate::Value;
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;
use anyhow::anyhow;

impl<'a> Compiler<'a> {
    pub(super) fn emit_return(&mut self, result_reg: super::Register) {
        self.program
            .instructions
            .push(Instruction::Return { value: result_reg });
        self.spans.push(SpanInfo::new(0, 0, 0, 0));
    }

    pub(super) fn emit_call_rule(&mut self, dest: super::Register, rule_index: u16) {
        self.program
            .instructions
            .push(Instruction::CallRule { dest, rule_index });
        self.spans.push(SpanInfo::new(0, 0, 0, 0));
    }

    pub(super) fn finish(mut self) -> Result<Program> {
        self.program.main_entry_point = 0;

        self.program.max_rule_window_size =
            self.rule_num_registers.iter().cloned().max().unwrap_or(0);
        self.program.dispatch_window_size = self.register_counter;

        let mut rule_infos_map = BTreeMap::new();

        let function_rule_indices: Vec<u16> = self
            .rule_index_map
            .values()
            .copied()
            .filter(|&rule_index| self.rule_function_param_count[rule_index as usize].is_some())
            .collect();

        let mut all_destructuring_blocks = BTreeMap::new();
        for rule_index in function_rule_indices {
            let destructuring_blocks = self.extract_destructuring_blocks(rule_index);
            all_destructuring_blocks.insert(rule_index, destructuring_blocks);
        }

        for (rule_path, &rule_index) in &self.rule_index_map {
            let definitions = self.rule_definitions[rule_index as usize].clone();
            let rule_type = self.rule_types[rule_index as usize].clone();
            let function_param_count = &self.rule_function_param_count[rule_index as usize];
            let result_register = self.rule_result_registers[rule_index as usize];
            let num_registers = self.rule_num_registers[rule_index as usize];

            let destructuring_blocks = all_destructuring_blocks
                .get(&rule_index)
                .cloned()
                .unwrap_or_else(|| vec![None; definitions.len()]);

            let mut rule_info = match function_param_count {
                Some(param_count) => {
                    let definition_params =
                        &self.rule_definition_function_params[rule_index as usize];
                    let param_names =
                        if let Some(Some(first_def_params)) = definition_params.first() {
                            first_def_params.clone()
                        } else {
                            (0..*param_count).map(|i| format!("param_{}", i)).collect()
                        };

                    crate::rvm::program::RuleInfo::new_function(
                        rule_path.clone(),
                        rule_type,
                        Rc::new(definitions),
                        param_names,
                        result_register,
                        num_registers,
                    )
                }
                None => crate::rvm::program::RuleInfo::new(
                    rule_path.clone(),
                    rule_type,
                    Rc::new(definitions),
                    result_register,
                    num_registers,
                ),
            };

            rule_info.destructuring_blocks = destructuring_blocks;
            rule_info.else_bodies = self
                .rule_definition_else_bodies
                .get(rule_index as usize)
                .cloned()
                .unwrap_or_else(|| {
                    rule_info
                        .definitions
                        .iter()
                        .map(|b| vec![false; b.len()])
                        .collect()
                });

            // Compute early_exit_on_first_success: if every definition has
            // the same static value, the VM can stop after the first success.
            // Only relevant for Complete rules and function rules with ≥2 defs.
            let static_values = self.rule_definition_static_values.get(rule_index as usize);
            if let Some(svs) = static_values {
                if svs.len() >= 2 {
                    // Check that all definitions have a known static value and
                    // that they are all equal.
                    let mut all_same = true;
                    let mut reference: Option<&Value> = None;
                    for sv in svs {
                        match sv {
                            Some(v) => match reference {
                                None => reference = Some(v),
                                Some(r) => {
                                    if r != v {
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
                    rule_info.early_exit_on_first_success = all_same && reference.is_some();
                }
            }

            rule_infos_map.insert(rule_index as usize, rule_info);
        }

        for rule_path in self.rule_index_map.keys() {
            if let Some(span) = self.default_function_span(
                rule_path,
                self.policy.inner.rule_paths.contains(rule_path),
            )? {
                return Err(CompilerError::FunctionDefaultsUnsupported.at(span));
            }
        }

        let rule_paths_to_evaluate: Vec<(String, usize)> = self
            .rule_index_map
            .iter()
            .filter_map(|(rule_path, &rule_index)| {
                let rule_type = &self.rule_types[rule_index as usize];
                if *rule_type == RuleType::Complete {
                    Some((rule_path.clone(), rule_index as usize))
                } else {
                    None
                }
            })
            .collect();

        for (rule_path, rule_index) in rule_paths_to_evaluate {
            if let Some(default_literal_index) = self.evaluate_default_rule(&rule_path)? {
                if let Some(rule_info) = rule_infos_map.get_mut(&rule_index) {
                    rule_info.set_default_literal_index(default_literal_index);
                }
            }
        }

        self.program.rule_infos = rule_infos_map.into_values().collect();

        // Spans refer to sources by the index assigned on first use, so the
        // sources that spans refer to come first, in that order.
        let mut referenced: Vec<(usize, &Source)> = self
            .source_to_index
            .iter()
            .map(|(source, &index)| (index, source))
            .collect();
        referenced.sort_unstable_by_key(|&(index, _)| index);
        let modules = self.policy.get_modules();
        let unreferenced = modules
            .iter()
            .map(|module| &module.package.refr.span().source)
            .filter(|source| !self.source_to_index.contains_key(*source));
        let sources: Vec<(String, String)> = referenced
            .into_iter()
            .map(|(_, source)| source)
            .chain(unreferenced)
            .map(|source| {
                (
                    source.get_path().to_string(),
                    source.get_contents().to_string(),
                )
            })
            .collect();
        for (source_path, source_content) in sources {
            self.program.add_source(source_path, source_content);
        }

        self.program.instruction_spans = self.spans.into_iter().map(Some).collect();
        self.program.entry_points = self.entry_points;

        if !self.program.builtin_info_table.is_empty() {
            self.program
                .initialize_resolved_builtins()
                .map_err(CompilerError::from)?;
        }

        self.program
            .validate_limits()
            .map_err(|e| CompilerError::from(anyhow!(e)))?;

        Ok(self.program)
    }

    fn evaluate_default_rule(&mut self, rule_path: &str) -> Result<Option<u16>> {
        let Some(defaults) = self.policy.inner.default_rules.get(rule_path) else {
            return Ok(None);
        };
        let mut selected_defaults = Vec::new();
        for (rule, index) in defaults {
            if let Rule::Default { refr, value, .. } = rule.as_ref() {
                let (module_index, module) = self.default_rule_module(rule)?;
                let package = get_path_string(&module.package.refr, Some("data"))
                    .map_err(CompilerError::from)?;
                let registered_head = match (refr.as_ref(), index) {
                    (Expr::RefBrack { refr, .. }, Some(_)) => refr,
                    _ => refr,
                };
                if self.policy.inner.rule_paths.contains(rule_path)
                    && get_path_string(registered_head, Some(&package))
                        .map_err(CompilerError::from)?
                        != rule_path
                {
                    continue;
                }
                self.validate_default_value(value, module_index, &package, None)?;
                selected_defaults.push(rule.clone());
            }
        }
        if selected_defaults.is_empty() {
            return Ok(None);
        }

        let mut interpreter = Interpreter::new_from_compiled_policy(self.policy.inner.clone());
        let computed_value = interpreter
            .eval_default_rule_for_compiler(rule_path, &selected_defaults)
            .map_err(CompilerError::from)?;
        Ok((computed_value != Value::Undefined).then(|| self.add_literal(computed_value)))
    }

    fn validate_default_value(
        &self,
        expr: &Expr,
        module_index: u32,
        package: &str,
        scope: Option<&ScopeContext>,
    ) -> Result<()> {
        let validate =
            |child: &Expr| self.validate_default_value(child, module_index, package, scope);
        match expr {
            Expr::String { .. }
            | Expr::RawString { .. }
            | Expr::Number { .. }
            | Expr::Bool { .. }
            | Expr::Null { .. } => {}
            Expr::Var { value, .. } => {
                let name = value.as_string().map_err(CompilerError::from)?;
                if matches!(name.as_ref(), "input" | "data")
                    || !scope.is_some_and(|scope| {
                        name.as_ref() == "_"
                            || scope.bound_vars.contains(name.as_ref())
                            || scope.local_vars.contains(name.as_ref())
                            || scope.unbound_vars.contains(name.as_ref())
                    })
                {
                    return Err(CompilerError::RuntimeDependentDefaultUnsupported.at(expr.span()));
                }
            }
            Expr::Array { items, .. } | Expr::Set { items, .. } => {
                for item in items {
                    validate(item)?;
                }
            }
            Expr::Object { fields, .. } => {
                for (_, key, value) in fields {
                    validate(key)?;
                    validate(value)?;
                }
            }
            Expr::ArrayCompr { term, query, .. } | Expr::SetCompr { term, query, .. } => {
                let query_scope = self.validate_default_query(query, module_index, package)?;
                self.validate_default_value(term, module_index, package, Some(query_scope))?;
            }
            Expr::ObjectCompr {
                key, value, query, ..
            } => {
                let query_scope = self.validate_default_query(query, module_index, package)?;
                self.validate_default_value(key, module_index, package, Some(query_scope))?;
                self.validate_default_value(value, module_index, package, Some(query_scope))?;
            }
            Expr::Call { fcn, params, .. } => {
                let name = get_path_string(fcn, None).map_err(CompilerError::from)?;
                let local_name =
                    get_path_string(fcn, Some(package)).map_err(CompilerError::from)?;
                let imported = self
                    .resolve_fcn_path_through_imports(&name, package)?
                    .is_some();
                if !builtins::BUILTINS.contains_key(name.as_str())
                    || builtins::must_cache(&name).is_some()
                    || self.policy.inner.functions.contains_key(&local_name)
                    || self.default_function_span(&local_name, true)?.is_some()
                    || imported
                    || self.host_await_builtins.contains_key(&name)
                    || self.policy.inner.extensions.contains_key(&name)
                {
                    return Err(CompilerError::RuntimeDependentDefaultUnsupported.at(expr.span()));
                }
                for param in params {
                    validate(param)?;
                }
            }
            Expr::RefDot { refr, .. } => validate(refr)?,
            Expr::RefBrack { refr, index, .. } => {
                validate(refr)?;
                validate(index)?;
            }
            Expr::UnaryExpr { expr, .. } => validate(expr)?,
            Expr::BinExpr { lhs, rhs, .. }
            | Expr::BoolExpr { lhs, rhs, .. }
            | Expr::ArithExpr { lhs, rhs, .. }
            | Expr::AssignExpr { lhs, rhs, .. } => {
                validate(lhs)?;
                validate(rhs)?;
            }
            Expr::Membership {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key) = key {
                    validate(key)?;
                }
                validate(value)?;
                validate(collection)?;
            }
            #[cfg(feature = "rego-extensions")]
            Expr::OrExpr { lhs, rhs, .. } => {
                validate(lhs)?;
                validate(rhs)?;
            }
        }
        Ok(())
    }

    fn validate_default_query(
        &self,
        query: &Query,
        module_index: u32,
        package: &str,
    ) -> Result<&ScopeContext> {
        let scope = self
            .policy
            .inner
            .loop_hoisting_table
            .get_query_context(module_index, query.qidx)
            .map_err(|error| CompilerError::General {
                message: format!("default query context lookup failed: {error}"),
            })?
            .ok_or_else(|| {
                CompilerError::General {
                    message: "missing default query context".to_string(),
                }
                .at(&query.span)
            })?;
        let validate =
            |expr: &Expr| self.validate_default_value(expr, module_index, package, Some(scope));
        for stmt in &query.stmts {
            if let Some(modifier) = stmt.with_mods.first() {
                return Err(CompilerError::WithKeywordUnsupported.at(&modifier.span));
            }
            match &stmt.literal {
                Literal::SomeVars { .. } => {}
                Literal::Expr { expr, .. } | Literal::NotExpr { expr, .. } => validate(expr)?,
                Literal::SomeIn {
                    key,
                    value,
                    collection,
                    ..
                } => {
                    if let Some(key) = key {
                        validate(key)?;
                    }
                    validate(value)?;
                    validate(collection)?;
                }
                Literal::Every {
                    domain,
                    query: body,
                    ..
                } => {
                    validate(domain)?;
                    self.validate_default_query(body, module_index, package)?;
                }
            }
        }
        Ok(scope)
    }

    fn extract_destructuring_blocks(&self, rule_index: u16) -> Vec<Option<u32>> {
        self.rule_definition_destructuring_patterns[rule_index as usize].clone()
    }
}
