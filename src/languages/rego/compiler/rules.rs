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

use super::{CompilationContext, Compiler, CompilerError, ContextType, Result, WorklistEntry};
use crate::ast::{Expr, Rule, RuleHead};
use crate::compiler::destructuring_planner::plans::BindingPlan;
use crate::lexer::Span;
use crate::rvm::program::{Program, RuleType};
use crate::rvm::Instruction;
use crate::utils::get_path_string;
use crate::Map;
use crate::{CompiledPolicy, Value};
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::sync::Arc;
use alloc::vec::Vec;

impl<'a> Compiler<'a> {
    pub(super) fn compute_rule_type(&self, rule_path: &str) -> Result<RuleType> {
        let Some(definitions) = self.policy.inner.rules.get(rule_path) else {
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
                            crate::ast::Expr::RefBrack { .. } => RuleType::PartialSet,
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

    pub(super) fn get_or_assign_rule_index(&mut self, rule_path: &str) -> Result<u16> {
        if let Some(&index) = self.rule_index_map.get(rule_path) {
            return Ok(index);
        }

        let rule_type = self.compute_rule_type(rule_path)?;
        let index = self.rule_index_map.len() as u16;

        self.rule_index_map.insert(rule_path.to_string(), index);
        let entry = WorklistEntry::new(rule_path.to_string(), self.current_call_stack.clone());
        self.rule_worklist.push(entry);

        while self.rule_definitions.len() <= index as usize {
            self.rule_definitions.push(Vec::new());
        }

        while self.rule_types.len() <= index as usize {
            self.rule_types.push(RuleType::Complete);
        }
        self.rule_types[index as usize] = rule_type;

        while self.rule_definition_function_params.len() <= index as usize {
            self.rule_definition_function_params.push(Vec::new());
        }

        while self.rule_definition_destructuring_patterns.len() <= index as usize {
            self.rule_definition_destructuring_patterns.push(Vec::new());
        }

        while self.rule_function_param_count.len() <= index as usize {
            self.rule_function_param_count.push(None);
        }

        while self.rule_result_registers.len() <= index as usize {
            self.rule_result_registers.push(0);
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

        let package = if let Some(last_dot) = rule_path.rfind('.') {
            rule_path[..last_dot].to_string()
        } else {
            "data".to_string()
        };
        Ok((package, 0))
    }

    /// Compile from a CompiledPolicy to RVM Program
    pub fn compile_from_policy(
        policy: &CompiledPolicy,
        entry_points: &[&str],
    ) -> Result<Arc<Program>> {
        let mut compiler = Compiler::with_policy(policy);
        compiler.current_rule_path = "".to_string();
        let rules = policy.get_rules();

        for &entry_point_name in entry_points {
            let instruction_index = compiler.program.instructions.len();
            let result_reg = compiler.alloc_register();
            let rule_idx = compiler.get_or_assign_rule_index(entry_point_name)?;
            compiler
                .entry_points
                .insert(entry_point_name.to_string(), instruction_index);
            compiler.emit_call_rule(result_reg, rule_idx);

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
        let (module_package, module_index) =
            self.find_module_package_and_index_for_rule(rule_path, rules)?;

        let saved_package = self.current_package.clone();
        let saved_module_index = self.current_module_index;
        self.current_package = module_package.clone();
        self.current_module_index = module_index;

        let saved_register_counter = self.register_counter;
        if let Some(rule_definitions) = rules.get(rule_path) {
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

                            self.emit_instruction(Instruction::RuleReturn {}, value_expr.span());
                            self.pop_scope();
                        }
                    } else {
                        for (body_idx, body) in bodies.iter().enumerate() {
                            self.push_scope();
                            self.reset_rule_definition_registers();

                            let body_entry_point = self.program.instructions.len() as u32;
                            body_entry_points.push(body_entry_point);

                            ::core::convert::identity(body_idx);

                            let previous_value_expr = self
                                .context_stack
                                .last()
                                .and_then(|ctx| ctx.value_expr.clone());
                            let mut body_value_expr =
                                body.assign.as_ref().map(|assign| assign.value.clone());
                            if body_value_expr.is_none() && body_idx == 0 {
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

                            self.emit_instruction(Instruction::RuleReturn {}, &body.span);

                            if let Some(context) = self.context_stack.last_mut() {
                                context.value_expr = previous_value_expr;
                            }

                            self.pop_scope();
                        }
                    }

                    self.pop_scope();

                    self.rule_definitions[rule_index as usize].push(body_entry_points);

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
                let rule_path_parts: Vec<&str> = rule_path.split('.').collect();
                if let Some((rule_name, package_parts)) = rule_path_parts.split_last() {
                    let package_path: Vec<String> =
                        package_parts.iter().map(|s| s.to_string()).collect();

                    let _ = self.program.add_rule_to_tree(
                        &package_path,
                        rule_name,
                        rule_index as usize,
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
