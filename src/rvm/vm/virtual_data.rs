// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::LiteralOrRegister;
use crate::value::Value;
use alloc::vec::Vec;
use core::convert::TryFrom as _;

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
            let key_value = self.literal_or_register_value(component)?;
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

    fn set_nested_value(target: &mut Value, path: &[Value], value: Value) -> Result<()> {
        Self::set_nested_value_static(target, path, value)
    }

    fn set_nested_value_static(target: &mut Value, path: &[Value], value: Value) -> Result<()> {
        let Some((head, tail)) = path.split_first() else {
            *target = value;
            return Ok(());
        };

        if *target == Value::Undefined {
            *target = Value::new_object();
        }

        if let Value::Object(ref mut map) = *target {
            if !map.contains_key(head) {
                crate::Rc::make_mut(map).insert(head.clone(), Value::Undefined);
            }

            if let Some(next_target) = crate::Rc::make_mut(map).get_mut(head) {
                Self::set_nested_value_static(next_target, tail, value)?;
            }
        } else {
            return Err(VmError::InvalidRuleTreeEntry {
                value: target.clone(),
                pc: 0,
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
        match *rule_tree_node {
            Value::Number(ref rule_idx) => {
                if let Some(rule_index) = rule_idx.as_u64() {
                    let mut full_cache_path = root_path.to_vec();
                    full_cache_path.extend_from_slice(relative_path);

                    let cached_result = {
                        let mut cache_lookup = &self.evaluated;
                        let mut path_exists = true;

                        for path_component in &full_cache_path {
                            if let Value::Object(ref map) = *cache_lookup {
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
                            if let Value::Object(ref map) = *cache_lookup {
                                map.get(&Value::Undefined).cloned()
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    };

                    let rule_result = if let Some(cached) = cached_result {
                        self.cache_hits =
                            self.checked_add_one(self.cache_hits, "cache hits counter")?;
                        cached
                    } else {
                        let temp_reg = u8::try_from(self.registers.len()).map_err(|_| {
                            VmError::RegisterIndexOutOfBounds {
                                index: u8::MAX,
                                pc: self.pc,
                                register_count: self.registers.len(),
                            }
                        })?;
                        self.registers.push(Value::Undefined);
                        let rule_index_u16 =
                            u16::try_from(rule_index).map_err(|_| VmError::InvalidRuleIndex {
                                rule_index: Value::Number(rule_idx.clone()),
                                pc: self.pc,
                            })?;
                        self.execute_call_rule_common(temp_reg, rule_index_u16, None)?;
                        let register_count = self.registers.len();
                        let result =
                            self.registers
                                .pop()
                                .ok_or(VmError::RegisterIndexOutOfBounds {
                                    index: temp_reg,
                                    pc: self.pc,
                                    register_count,
                                })?;

                        let mut cache_path = full_cache_path.clone();
                        cache_path.push(Value::Undefined);
                        Self::set_nested_value_static(
                            &mut self.evaluated,
                            &cache_path,
                            result.clone(),
                        )?;

                        result
                    };

                    Self::set_nested_value(result_subobject, relative_path, rule_result)?;
                } else {
                    return Err(VmError::InvalidRuleIndex {
                        rule_index: Value::Number(rule_idx.clone()),
                        pc: self.pc,
                    });
                }
            }
            Value::Object(ref obj) => {
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
                pc: self.pc,
                available: self
                    .program
                    .instruction_data
                    .virtual_data_document_lookup_params
                    .len(),
            })?
            .clone();

        let mut current_node = &self.program.rule_tree["data"];
        let mut components_consumed = 0;

        for (i, component) in params.path_components.iter().enumerate() {
            let key_value = self.literal_or_register_value(component)?;

            current_node = &current_node[&key_value];
            components_consumed = self.checked_add_one(i, "path components traversed")?;

            match *current_node {
                Value::Undefined | Value::Number(_) => break,
                _ => {}
            }
        }

        match *current_node {
            Value::Number(ref rule_index_value) => {
                if let Some(rule_index) = rule_index_value.as_u64() {
                    let rule_index =
                        u16::try_from(rule_index).map_err(|_| VmError::InvalidRuleIndex {
                            rule_index: Value::Number(rule_index_value.clone()),
                            pc: self.pc,
                        })?;

                    self.execute_call_rule_common(params.dest, rule_index, None)?;

                    if components_consumed < params.path_components.len() {
                        let mut rule_result = self.get_register(params.dest)?.clone();

                        for component in params.path_components.iter().skip(components_consumed) {
                            let key_value = self.literal_or_register_value(component)?;

                            rule_result = rule_result[&key_value].clone();
                        }

                        self.set_register(params.dest, rule_result)?;
                    }
                } else {
                    return Err(VmError::InvalidRuleIndex {
                        rule_index: Value::Number(rule_index_value.clone()),
                        pc: self.pc,
                    });
                }
            }
            Value::Undefined | Value::Object(_)
                if components_consumed != params.path_components.len() =>
            {
                let mut result = self.data.clone();

                for component in &params.path_components {
                    let key_value = self.literal_or_register_value(component)?;

                    result = result[&key_value].clone();
                }

                self.set_register(params.dest, result)?;
            }
            Value::Object(_) => {
                let rule_tree_subobject = current_node.clone();

                let result = self.execute_virtual_data_document_lookup_subobject(
                    &params.path_components,
                    &rule_tree_subobject,
                )?;
                self.set_register(params.dest, result)?;
            }
            _ => {
                return Err(VmError::InvalidRuleTreeEntry {
                    value: current_node.clone(),
                    pc: self.pc,
                });
            }
        }

        Ok(())
    }

    fn literal_or_register_value(&self, source: &LiteralOrRegister) -> Result<Value> {
        let value = match *source {
            LiteralOrRegister::Literal(ref idx) => self
                .program
                .literals
                .get(usize::from(*idx))
                .ok_or(VmError::LiteralIndexOutOfBounds {
                    index: *idx,
                    pc: self.pc,
                })?
                .clone(),
            LiteralOrRegister::Register(ref reg) => self.get_register(*reg)?.clone(),
        };

        Ok(value)
    }
}
