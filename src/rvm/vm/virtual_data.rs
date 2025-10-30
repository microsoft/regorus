// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::LiteralOrRegister;
use crate::value::Value;
use alloc::vec::Vec;

use super::errors::{Result, VmError};
use super::machine::RegoVM;

impl RegoVM {
    pub(super) fn execute_virtual_data_document_lookup_subobject(
        &mut self,
        path_components: &[LiteralOrRegister],
        rule_tree_subobject: &Value,
    ) -> Result<Value> {
        let mut root_path = Vec::new();
        for component in path_components {
            let key_value = match component {
                LiteralOrRegister::Literal(idx) => self
                    .program
                    .literals
                    .get(*idx as usize)
                    .ok_or(VmError::LiteralIndexOutOfBounds {
                        index: *idx as usize,
                    })?
                    .clone(),
                LiteralOrRegister::Register(reg) => self.registers[*reg as usize].clone(),
            };
            root_path.push(key_value);
        }

        let mut data_subobject = self.data.clone();
        for path_component in &root_path {
            data_subobject = data_subobject[path_component].clone();
        }

        let mut result_subobject = match data_subobject {
            Value::Undefined => Value::new_object(),
            _ => data_subobject,
        };

        self.traverse_rule_tree_subobject(rule_tree_subobject, &mut result_subobject, &root_path)?;

        Ok(result_subobject)
    }

    fn set_nested_value(&self, target: &mut Value, path: &[Value], value: Value) -> Result<()> {
        Self::set_nested_value_static(target, path, value)
    }

    fn set_nested_value_static(target: &mut Value, path: &[Value], value: Value) -> Result<()> {
        if path.is_empty() {
            *target = value;
            return Ok(());
        }

        if *target == Value::Undefined {
            *target = Value::new_object();
        }

        if let Value::Object(ref mut map) = target {
            let key = &path[0];

            if !map.contains_key(key) {
                crate::Rc::make_mut(map).insert(key.clone(), Value::Undefined);
            }

            if let Some(next_target) = crate::Rc::make_mut(map).get_mut(key) {
                Self::set_nested_value_static(next_target, &path[1..], value)?;
            }
        } else {
            return Err(VmError::InvalidRuleTreeEntry {
                value: target.clone(),
            });
        }

        Ok(())
    }

    fn traverse_rule_tree_subobject(
        &mut self,
        rule_tree_node: &Value,
        result_subobject: &mut Value,
        root_path: &[Value],
    ) -> Result<()> {
        self.traverse_rule_tree_subobject_with_path(
            rule_tree_node,
            result_subobject,
            root_path,
            &[],
        )
    }

    fn traverse_rule_tree_subobject_with_path(
        &mut self,
        rule_tree_node: &Value,
        result_subobject: &mut Value,
        root_path: &[Value],
        relative_path: &[Value],
    ) -> Result<()> {
        match rule_tree_node {
            Value::Number(rule_idx) => {
                if let Some(rule_index) = rule_idx.as_u64() {
                    let mut full_cache_path = root_path.to_vec();
                    full_cache_path.extend_from_slice(relative_path);

                    let cached_result = {
                        let mut cache_lookup = &self.evaluated;
                        let mut path_exists = true;

                        for path_component in &full_cache_path {
                            if let Value::Object(ref map) = cache_lookup {
                                if let Some(next_value) = map.get(path_component) {
                                    cache_lookup = next_value;
                                } else {
                                    path_exists = false;
                                    break;
                                }
                            } else {
                                path_exists = false;
                                break;
                            }
                        }

                        if path_exists {
                            if let Value::Object(ref map) = cache_lookup {
                                map.get(&Value::Undefined).cloned()
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    };

                    let rule_result = if let Some(cached) = cached_result {
                        self.cache_hits += 1;
                        cached
                    } else {
                        let temp_reg = self.registers.len() as u8;
                        self.registers.push(Value::Undefined);
                        self.execute_call_rule_common(temp_reg, rule_index as u16, None)?;
                        let result = self.registers.pop().unwrap();

                        let mut cache_path = full_cache_path.clone();
                        cache_path.push(Value::Undefined);
                        Self::set_nested_value_static(
                            &mut self.evaluated,
                            &cache_path,
                            result.clone(),
                        )?;

                        result
                    };

                    self.set_nested_value(result_subobject, relative_path, rule_result)?;
                } else {
                    return Err(VmError::InvalidRuleIndex {
                        rule_index: Value::Number(rule_idx.clone()),
                    });
                }
            }
            Value::Object(obj) => {
                for (key, value) in obj.iter() {
                    let mut new_relative_path = relative_path.to_vec();
                    new_relative_path.push(key.clone());
                    self.traverse_rule_tree_subobject_with_path(
                        value,
                        result_subobject,
                        root_path,
                        &new_relative_path,
                    )?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    pub(super) fn execute_virtual_data_document_lookup(&mut self, params_index: u16) -> Result<()> {
        let params = self
            .program
            .instruction_data
            .get_virtual_data_document_lookup_params(params_index)
            .ok_or(VmError::InvalidVirtualDataDocumentLookupParams {
                index: params_index,
            })?
            .clone();

        let mut current_node = &self.program.rule_tree["data"];
        let mut components_consumed = 0;

        for (i, component) in params.path_components.iter().enumerate() {
            let key_value = match component {
                LiteralOrRegister::Literal(idx) => self
                    .program
                    .literals
                    .get(*idx as usize)
                    .ok_or(VmError::LiteralIndexOutOfBounds {
                        index: *idx as usize,
                    })?
                    .clone(),
                LiteralOrRegister::Register(reg) => self.registers[*reg as usize].clone(),
            };

            current_node = &current_node[&key_value];
            components_consumed = i + 1;

            match current_node {
                Value::Undefined | Value::Number(_) => break,
                _ => {}
            }
        }

        match current_node {
            Value::Number(rule_index_value) => {
                if let Some(rule_index) = rule_index_value.as_u64() {
                    let rule_index = rule_index as u16;

                    self.execute_call_rule_common(params.dest, rule_index, None)?;

                    if components_consumed < params.path_components.len() {
                        let mut rule_result = self.registers[params.dest as usize].clone();

                        for component in &params.path_components[components_consumed..] {
                            let key_value = match component {
                                LiteralOrRegister::Literal(idx) => self
                                    .program
                                    .literals
                                    .get(*idx as usize)
                                    .ok_or(VmError::LiteralIndexOutOfBounds {
                                        index: *idx as usize,
                                    })?
                                    .clone(),
                                LiteralOrRegister::Register(reg) => {
                                    self.registers[*reg as usize].clone()
                                }
                            };

                            rule_result = rule_result[&key_value].clone();
                        }

                        self.registers[params.dest as usize] = rule_result;
                    }
                } else {
                    return Err(VmError::InvalidRuleIndex {
                        rule_index: Value::Number(rule_index_value.clone()),
                    });
                }
            }
            Value::Undefined | Value::Object(_)
                if components_consumed != params.path_components.len() =>
            {
                let mut result = self.data.clone();

                for component in &params.path_components {
                    let key_value = match component {
                        LiteralOrRegister::Literal(idx) => self
                            .program
                            .literals
                            .get(*idx as usize)
                            .ok_or(VmError::LiteralIndexOutOfBounds {
                                index: *idx as usize,
                            })?
                            .clone(),
                        LiteralOrRegister::Register(reg) => self.registers[*reg as usize].clone(),
                    };

                    result = result[&key_value].clone();
                }

                self.registers[params.dest as usize] = result;
            }
            Value::Object(_) => {
                let rule_tree_subobject = current_node.clone();

                let result = self.execute_virtual_data_document_lookup_subobject(
                    &params.path_components,
                    &rule_tree_subobject,
                )?;
                self.registers[params.dest as usize] = result;
            }
            _ => {
                return Err(VmError::InvalidRuleTreeEntry {
                    value: current_node.clone(),
                });
            }
        }

        Ok(())
    }
}
