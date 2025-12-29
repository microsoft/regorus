// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

use super::{Compiler, CompilerError, Result};
use crate::interpreter::Interpreter;
use crate::rvm::program::{Program, RuleType, SpanInfo};
use crate::rvm::Instruction;
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
            rule_infos_map.insert(rule_index as usize, rule_info);
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
            if let Some(default_literal_index) = self.evaluate_default_rule(&rule_path) {
                if let Some(rule_info) = rule_infos_map.get_mut(&rule_index) {
                    rule_info.set_default_literal_index(default_literal_index);
                }
            }
        }

        self.program.rule_infos = rule_infos_map.into_values().collect();

        for module in self.policy.get_modules().iter() {
            let source = &module.package.refr.span().source;
            let source_path = source.get_path().to_string();
            let source_content = source.get_contents().to_string();
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

    fn evaluate_default_rule(&mut self, rule_path: &str) -> Option<u16> {
        if !self.policy.inner.default_rules.contains_key(rule_path) {
            return None;
        }

        let mut interpreter = Interpreter::new_from_compiled_policy(self.policy.inner.clone());

        match interpreter.eval_default_rule_for_compiler(rule_path) {
            Ok(computed_value) => {
                if computed_value != Value::Undefined {
                    let literal_index = self.add_literal(computed_value);
                    return Some(literal_index);
                }
            }
            Err(_e) => {}
        }

        None
    }

    fn extract_destructuring_blocks(&self, rule_index: u16) -> Vec<Option<u32>> {
        self.rule_definition_destructuring_patterns[rule_index as usize].clone()
    }
}
