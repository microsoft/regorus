// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::LiteralOrRegister;
use crate::value::Value;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::convert::TryFrom as _;

use super::errors::{Result, VmError};
use super::execution_model::{
    ExecutionFrame, ExecutionMode, ExecutionState, FrameKind, VirtualDataLookupFrameData,
};
use super::machine::RegoVM;

impl RegoVM {
    pub(super) fn execute_virtual_data_document_lookup_subobject(
        &mut self,
        path_components: &[LiteralOrRegister],
        string_fallback_indices: &[usize],
        data_subobject: Value,
        rule_tree_subobject: &Value,
    ) -> Result<Value> {
        let mut root_path = Vec::new();
        let mut fallback_indices = string_fallback_indices.iter().copied().peekable();
        for (index, component) in path_components.iter().enumerate() {
            let mut key_value = self.literal_or_register_value(component)?;
            if fallback_indices
                .peek()
                .is_some_and(|fallback_index| *fallback_index == index)
            {
                let _ = fallback_indices.next();
                key_value = Value::from(key_value.to_string());
            }
            root_path.push(key_value);
        }

        let mut result_subobject = match data_subobject {
            Value::Undefined => Value::new_object(),
            subobject => subobject,
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
                value: target.clone().into(),
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
        let mut relative_path = Vec::new();
        enum Action<'a, I> {
            Visit(&'a Value),
            Children(I),
            Leave,
        }
        let mut pending = alloc::vec![Action::Visit(rule_tree_node)];
        while let Some(action) = pending.pop() {
            self.memory_check()?;
            match action {
                Action::Visit(node) => match *node {
                    Value::Number(ref rule_idx) => {
                        if let Some(rule_index) = rule_idx.as_u64() {
                            // Walk the evaluated cache using root_path then relative_path,
                            // without allocating a combined full_cache_path Vec.
                            let cached_result =
                                self.cached_virtual_rule_result(root_path, &relative_path);

                            let rule_result = if let Some(cached) = cached_result {
                                self.cache_hits =
                                    self.checked_add_one(self.cache_hits, "cache hits counter")?;
                                cached
                            } else {
                                let temp_reg =
                                    u8::try_from(self.registers.len()).map_err(|_| {
                                        VmError::RegisterIndexOutOfBounds {
                                            index: u8::MAX,
                                            pc: self.pc,
                                            register_count: self.registers.len(),
                                        }
                                    })?;
                                self.registers.push(Value::Undefined);
                                let rule_index_u16 = u16::try_from(rule_index).map_err(|_| {
                                    VmError::InvalidRuleIndex {
                                        rule_index: Value::Number(rule_idx.clone()).into(),
                                        pc: self.pc,
                                    }
                                })?;
                                self.execute_call_rule_common(temp_reg, rule_index_u16, None)?;
                                let register_count = self.registers.len();
                                let result = self.registers.pop().ok_or(
                                    VmError::RegisterIndexOutOfBounds {
                                        index: temp_reg,
                                        pc: self.pc,
                                        register_count,
                                    },
                                )?;

                                // Build cache_path from root_path + relative_path + Undefined sentinel.
                                let mut cache_path: Vec<Value> = Vec::with_capacity(
                                    root_path
                                        .len()
                                        .saturating_add(relative_path.len())
                                        .saturating_add(1),
                                );
                                cache_path.extend_from_slice(root_path);
                                cache_path.extend_from_slice(&relative_path);
                                cache_path.push(Value::Undefined);
                                Self::set_nested_value_static(
                                    &mut self.evaluated,
                                    &cache_path,
                                    result.clone(),
                                )?;

                                result
                            };

                            Self::set_nested_value(result_subobject, &relative_path, rule_result)?;
                        } else {
                            return Err(VmError::InvalidRuleIndex {
                                rule_index: Value::Number(rule_idx.clone()).into(),
                                pc: self.pc,
                            });
                        }
                    }
                    Value::Object(ref obj) => {
                        pending.push(Action::Children(obj.iter()));
                    }
                    _ => {}
                },
                Action::Children(mut children) => {
                    if let Some((key, value)) = children.next() {
                        relative_path.push(key.clone());
                        pending.push(Action::Children(children));
                        pending.push(Action::Leave);
                        pending.push(Action::Visit(value));
                    }
                }
                Action::Leave => {
                    relative_path.pop();
                }
            }
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
        let mut data_ref = &self.data;
        let mut string_fallback_indices = Vec::new();
        let mut components_consumed = 0;

        for (i, component) in params.path_components.iter().enumerate() {
            let mut key_value = self.literal_or_register_value(component)?;

            let mut rule_child = &current_node[&key_value];
            let mut data_child = &data_ref[&key_value];
            if *rule_child == Value::Undefined
                && *data_child == Value::Undefined
                && matches!(key_value, Value::Number(_))
            {
                string_fallback_indices.push(i);
                key_value = Value::from(key_value.to_string());
                rule_child = &current_node[&key_value];
                data_child = &data_ref[&key_value];
            }
            current_node = rule_child;
            data_ref = data_child;
            components_consumed = self.checked_add_one(i, "path components traversed")?;

            match *current_node {
                Value::Undefined | Value::Number(_) => break,
                _ => {}
            }
        }

        if matches!(self.execution_mode, ExecutionMode::Suspendable)
            && (matches!(current_node, Value::Number(_))
                || (matches!(current_node, Value::Object(_))
                    && components_consumed == params.path_components.len()))
        {
            let mut root_path = Vec::new();
            for (index, component) in params
                .path_components
                .iter()
                .take(components_consumed)
                .enumerate()
            {
                let key = self.literal_or_register_value(component)?;
                root_path.push(if string_fallback_indices.contains(&index) {
                    Value::from(key.to_string())
                } else {
                    key
                });
            }
            let remaining_path = params
                .path_components
                .iter()
                .skip(components_consumed)
                .map(|component| self.literal_or_register_value(component))
                .collect::<Result<Vec<_>>>()?;
            let result = if matches!(current_node, Value::Object(_)) {
                match *data_ref {
                    Value::Undefined => Value::new_object(),
                    _ => data_ref.clone(),
                }
            } else {
                Value::Undefined
            };
            self.execution_stack.push(ExecutionFrame::new(
                self.pc,
                FrameKind::VirtualDataLookup(VirtualDataLookupFrameData {
                    return_pc: self.pc,
                    dest_reg: params.dest,
                    root_path,
                    remaining_path,
                    pending: alloc::vec![(current_node.clone(), Vec::new())],
                    current_path: None,
                    result,
                }),
            ));
            return Ok(());
        }

        match *current_node {
            Value::Number(ref rule_index_value) => {
                if let Some(rule_index) = rule_index_value.as_u64() {
                    let rule_index =
                        u16::try_from(rule_index).map_err(|_| VmError::InvalidRuleIndex {
                            rule_index: Value::Number(rule_index_value.clone()).into(),
                            pc: self.pc,
                        })?;

                    self.execute_call_rule_common(params.dest, rule_index, None)?;

                    if components_consumed < params.path_components.len() {
                        // Walk remaining path by reference, clone only the leaf.
                        let mut ref_val = self.get_register(params.dest)?;

                        for component in params.path_components.iter().skip(components_consumed) {
                            let key_value = self.literal_or_register_value(component)?;
                            ref_val = &ref_val[&key_value];
                        }

                        let leaf = ref_val.clone();
                        self.set_register(params.dest, leaf)?;
                    }
                } else {
                    return Err(VmError::InvalidRuleIndex {
                        rule_index: Value::Number(rule_index_value.clone()).into(),
                        pc: self.pc,
                    });
                }
            }
            Value::Undefined => {
                let mut result_ref = data_ref;
                for component in params.path_components.iter().skip(components_consumed) {
                    let key_value = self.literal_or_register_value(component)?;
                    let mut child = &result_ref[&key_value];
                    if *child == Value::Undefined && matches!(key_value, Value::Number(_)) {
                        let string_key = Value::from(key_value.to_string());
                        child = &result_ref[&string_key];
                    }
                    result_ref = child;
                }
                self.set_register(params.dest, result_ref.clone())?;
            }
            Value::Object(_) if components_consumed != params.path_components.len() => {
                // Walk data tree by reference, clone only the leaf.
                let mut result_data_ref = &self.data;

                for component in &params.path_components {
                    let key_value = self.literal_or_register_value(component)?;
                    let mut child = &result_data_ref[&key_value];
                    if *child == Value::Undefined && matches!(key_value, Value::Number(_)) {
                        let string_key = Value::from(key_value.to_string());
                        child = &result_data_ref[&string_key];
                    }
                    result_data_ref = child;
                }

                let result = result_data_ref.clone();
                self.set_register(params.dest, result)?;
            }
            Value::Object(_) => {
                let rule_tree_subobject = current_node.clone();
                let data_subobject = data_ref.clone();
                let result = self.execute_virtual_data_document_lookup_subobject(
                    &params.path_components,
                    &string_fallback_indices,
                    data_subobject,
                    &rule_tree_subobject,
                )?;
                self.set_register(params.dest, result)?;
            }
            _ => {
                return Err(VmError::InvalidRuleTreeEntry {
                    value: current_node.clone().into(),
                    pc: self.pc,
                });
            }
        }

        Ok(())
    }

    fn cached_virtual_rule_result(
        &self,
        root_path: &[Value],
        relative_path: &[Value],
    ) -> Option<Value> {
        let mut node = &self.evaluated;
        for key in root_path.iter().chain(relative_path) {
            node = match *node {
                Value::Object(ref map) => map.get(key)?,
                _ => return None,
            };
        }
        match *node {
            Value::Object(ref map) => map.get(&Value::Undefined).cloned(),
            _ => None,
        }
    }

    pub(super) fn resume_virtual_data_lookup(
        &mut self,
        mut data: VirtualDataLookupFrameData,
    ) -> Result<()> {
        self.pc = data.return_pc;
        if let Some(path) = data.current_path.take() {
            let result = self.get_register(data.dest_reg)?.clone();
            Self::set_nested_value(&mut data.result, &path, result.clone())?;
            let mut cache_path = data.root_path.clone();
            cache_path.extend_from_slice(&path);
            cache_path.push(Value::Undefined);
            Self::set_nested_value_static(&mut self.evaluated, &cache_path, result)?;
        }
        while let Some((node, path)) = data.pending.pop() {
            self.charge_virtual_lookup_work()?;
            match node {
                Value::Object(map) => {
                    let mut children = Vec::new();
                    for (key, child) in map.iter() {
                        self.charge_virtual_lookup_work()?;
                        let mut child_path = path.clone();
                        child_path.push(key.clone());
                        children.push((child.clone(), child_path));
                    }
                    children.reverse();
                    data.pending.extend(children);
                }
                Value::Number(index) => {
                    let rule_index = index
                        .as_u64()
                        .and_then(|value| u16::try_from(value).ok())
                        .ok_or_else(|| VmError::InvalidRuleIndex {
                            rule_index: Value::Number(index),
                            pc: self.pc,
                        })?;
                    if let Some(cached) = self.cached_virtual_rule_result(&data.root_path, &path) {
                        self.cache_hits =
                            self.checked_add_one(self.cache_hits, "cache hits counter")?;
                        Self::set_nested_value(&mut data.result, &path, cached)?;
                    } else {
                        let dest = data.dest_reg;
                        data.current_path = Some(path);
                        self.execution_stack.push(ExecutionFrame::new(
                            self.pc,
                            FrameKind::VirtualDataLookup(data),
                        ));
                        return self.execute_call_rule_suspendable(dest, rule_index, None);
                    }
                }
                _ => {}
            }
        }
        let mut leaf = &data.result;
        for key in &data.remaining_path {
            leaf = &leaf[key];
        }
        self.set_register(data.dest_reg, leaf.clone())?;
        if let Some(parent) = self.execution_stack.last_mut() {
            parent.pc = data.return_pc.saturating_add(1);
        }
        Ok(())
    }

    fn charge_virtual_lookup_work(&mut self) -> Result<()> {
        if self.executed_instructions >= self.max_instructions {
            let error = VmError::InstructionLimitExceeded {
                limit: self.max_instructions,
                executed: self.executed_instructions,
                pc: self.pc,
            };
            self.execution_state = ExecutionState::Error {
                error: error.clone(),
            };
            return Err(error);
        }
        self.executed_instructions = self.executed_instructions.saturating_add(1);
        self.execution_timer_tick(1)?;
        self.memory_check()
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
