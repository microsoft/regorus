// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::LiteralOrRegister;
use crate::value::Value;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::convert::TryFrom as _;

use super::errors::{Result, VmError};
use super::execution_model::{
    ExecutionFrame, ExecutionMode, FrameKind, VirtualDataLookupFrame, VirtualDataLookupKind,
    VirtualDataLookupPending, VirtualDataLookupTraversal,
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
                value: target.clone(),
                pc: 0,
            });
        }

        Ok(())
    }

    fn ensure_nested_object(target: &mut Value, path: &[Value]) -> Result<()> {
        let Some((head, tail)) = path.split_first() else {
            if *target == Value::Undefined {
                *target = Value::new_object();
            }
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
                Self::ensure_nested_object(next_target, tail)?;
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
        let mut relative_path = Vec::new();
        self.traverse_rule_tree_subobject_with_path(
            rule_tree_node,
            result_subobject,
            root_path,
            &mut relative_path,
        )
    }

    fn traverse_rule_tree_subobject_with_path(
        &mut self,
        rule_tree_node: &Value,
        result_subobject: &mut Value,
        root_path: &[Value],
        relative_path: &mut Vec<Value>,
    ) -> Result<()> {
        match *rule_tree_node {
            Value::Number(ref rule_idx) => {
                if let Some(rule_index) = rule_idx.as_u64() {
                    // Walk the evaluated cache using root_path then relative_path,
                    // without allocating a combined full_cache_path Vec.
                    let cached_result = {
                        let mut cache_lookup = &self.evaluated;
                        let mut path_exists = true;

                        for path_component in root_path.iter().chain(relative_path.iter()) {
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

                        // Build cache_path from root_path + relative_path + Undefined sentinel.
                        let mut cache_path: Vec<Value> = Vec::with_capacity(
                            root_path
                                .len()
                                .saturating_add(relative_path.len())
                                .saturating_add(1),
                        );
                        cache_path.extend_from_slice(root_path);
                        cache_path.extend_from_slice(relative_path);
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
                // A package with no document descendants is still a namespace object.
                if obj.is_empty() {
                    Self::ensure_nested_object(result_subobject, relative_path)?;
                }
                for (key, value) in obj.iter() {
                    relative_path.push(key.clone());
                    self.traverse_rule_tree_subobject_with_path(
                        value,
                        result_subobject,
                        root_path,
                        relative_path,
                    )?;
                    relative_path.pop();
                }
            }
            _ => {}
        }
        Ok(())
    }

    pub(super) fn begin_suspendable_virtual_data_document_lookup(
        &mut self,
        params_index: u16,
    ) -> Result<()> {
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

        // Evaluate every path register before a child rule can swap the active
        // register window. The adjusted values also preserve each numeric key's
        // numeric-to-string fallback decision across suspension.
        let mut path_values = Vec::with_capacity(params.path_components.len());
        for component in &params.path_components {
            path_values.push(self.literal_or_register_value(component)?);
        }

        let mut current_node = &self.program.rule_tree[&Value::from("data")];
        let mut data_ref = &self.data;
        let mut components_consumed = 0;

        for (index, key_value) in path_values.iter_mut().enumerate() {
            let mut rule_child = &current_node[&*key_value];
            let mut data_child = &data_ref[&*key_value];
            if *rule_child == Value::Undefined
                && *data_child == Value::Undefined
                && matches!(key_value, Value::Number(_))
            {
                *key_value = Value::from(key_value.to_string());
                rule_child = &current_node[&*key_value];
                data_child = &data_ref[&*key_value];
            }
            current_node = rule_child;
            data_ref = data_child;
            components_consumed = self.checked_add_one(index, "path components traversed")?;

            match *current_node {
                Value::Undefined | Value::Number(_) => break,
                _ => {}
            }
        }

        match *current_node {
            Value::Number(ref rule_index_value) => {
                let rule_index = rule_index_value
                    .as_u64()
                    .and_then(|index| u16::try_from(index).ok())
                    .ok_or(VmError::InvalidRuleIndex {
                        rule_index: Value::Number(rule_index_value.clone()),
                        pc: self.pc,
                    })?;
                let suffix = path_values.into_iter().skip(components_consumed).collect();
                self.execution_stack.push(ExecutionFrame::new(
                    self.pc,
                    FrameKind::VirtualDataLookup(VirtualDataLookupFrame {
                        lookup_pc: self.pc,
                        dest_reg: params.dest,
                        kind: VirtualDataLookupKind::Rule { rule_index, suffix },
                        pending: None,
                    }),
                ));
            }
            Value::Undefined => {
                let mut result_ref = data_ref;
                for key_value in path_values.iter().skip(components_consumed) {
                    let mut child = &result_ref[key_value];
                    if *child == Value::Undefined && matches!(key_value, Value::Number(_)) {
                        let string_key = Value::from(key_value.to_string());
                        child = &result_ref[&string_key];
                    }
                    result_ref = child;
                }
                self.set_register(params.dest, result_ref.clone())?;
            }
            Value::Object(_) if components_consumed != path_values.len() => {
                let mut result_data_ref = &self.data;
                for key_value in &path_values {
                    let mut child = &result_data_ref[key_value];
                    if *child == Value::Undefined && matches!(key_value, Value::Number(_)) {
                        let string_key = Value::from(key_value.to_string());
                        child = &result_data_ref[&string_key];
                    }
                    result_data_ref = child;
                }
                self.set_register(params.dest, result_data_ref.clone())?;
            }
            Value::Object(_) => {
                let rule_tree_subobject = current_node.clone();
                let result = match data_ref.clone() {
                    Value::Undefined => Value::new_object(),
                    value => value,
                };
                let traversal = match rule_tree_subobject {
                    Value::Object(ref object) => alloc::vec![VirtualDataLookupTraversal {
                        node: rule_tree_subobject.clone(),
                        cursor: object.cursor(),
                        path_len: 0,
                    }],
                    ref value => {
                        return Err(VmError::InvalidRuleTreeEntry {
                            value: value.clone(),
                            pc: self.pc,
                        });
                    }
                };
                self.execution_stack.push(ExecutionFrame::new(
                    self.pc,
                    FrameKind::VirtualDataLookup(VirtualDataLookupFrame {
                        lookup_pc: self.pc,
                        dest_reg: params.dest,
                        kind: VirtualDataLookupKind::Subtree {
                            root_path: path_values,
                            result,
                            relative_path: Vec::new(),
                            traversal,
                        },
                        pending: None,
                    }),
                ));
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

    /// Advance a private virtual-lookup frame until it schedules one rule child
    /// or completes. The returned child destination is a temporary register;
    /// the caller-visible destination is written only at completion.
    pub(super) fn advance_virtual_data_document_lookup(
        &mut self,
        frame: &mut VirtualDataLookupFrame,
    ) -> Result<Option<(u8, u16)>> {
        if let Some(pending) = frame.pending.take() {
            let register = match &pending {
                &VirtualDataLookupPending::Rule { register }
                | &VirtualDataLookupPending::Subtree { register, .. } => register,
            };
            let register_count = self.registers.len();
            if register_count != usize::from(register).saturating_add(1) {
                return Err(VmError::RegisterIndexOutOfBounds {
                    index: register,
                    pc: self.pc,
                    register_count,
                });
            }
            let completed_result =
                self.registers
                    .pop()
                    .ok_or(VmError::RegisterIndexOutOfBounds {
                        index: register,
                        pc: self.pc,
                        register_count,
                    })?;

            match (pending, &mut frame.kind) {
                (
                    VirtualDataLookupPending::Rule { .. },
                    &mut VirtualDataLookupKind::Rule { ref mut suffix, .. },
                ) => {
                    let mut result = completed_result;
                    for key in suffix {
                        result = result[&*key].clone();
                    }
                    self.set_register(frame.dest_reg, result)?;
                    return Ok(None);
                }
                (
                    VirtualDataLookupPending::Subtree {
                        parent_path_len, ..
                    },
                    &mut VirtualDataLookupKind::Subtree {
                        ref mut root_path,
                        ref mut result,
                        ref mut relative_path,
                        ..
                    },
                ) => {
                    let cache_capacity = root_path
                        .len()
                        .saturating_add(relative_path.len())
                        .saturating_add(1);
                    let mut cache_path = Vec::with_capacity(cache_capacity);
                    cache_path.extend_from_slice(root_path);
                    cache_path.extend_from_slice(relative_path);
                    cache_path.push(Value::Undefined);
                    Self::set_nested_value_static(
                        &mut self.evaluated,
                        &cache_path,
                        completed_result.clone(),
                    )?;
                    Self::set_nested_value_static(result, relative_path, completed_result)?;
                    relative_path.truncate(parent_path_len);
                }
                _ => {
                    return Err(VmError::Internal {
                        message: alloc::string::String::from(
                            "virtual data lookup pending child does not match its frame",
                        ),
                        pc: self.pc,
                    });
                }
            }
        }

        match frame.kind {
            VirtualDataLookupKind::Rule { rule_index, .. } => {
                let register = self.allocate_virtual_lookup_register()?;
                frame.pending = Some(VirtualDataLookupPending::Rule { register });
                Ok(Some((register, rule_index)))
            }
            VirtualDataLookupKind::Subtree {
                ref mut root_path,
                ref mut result,
                ref mut relative_path,
                ref mut traversal,
            } => loop {
                let next_entry = if let Some(cursor_frame) = traversal.last_mut() {
                    match cursor_frame.node {
                        Value::Object(ref object) => {
                            object.next(&mut cursor_frame.cursor).map(|(key, value)| {
                                (key.clone(), value.clone(), cursor_frame.path_len)
                            })
                        }
                        _ => None,
                    }
                } else {
                    self.set_register(frame.dest_reg, result.clone())?;
                    return Ok(None);
                };

                let Some((key, child, parent_path_len)) = next_entry else {
                    let completed = traversal.pop();
                    if let Some(completed) = completed {
                        relative_path.truncate(completed.path_len);
                    }
                    continue;
                };

                // The prior DFS child may have left the path at a deeper level.
                // Restore the entry's actual parent before visiting this sibling.
                relative_path.truncate(parent_path_len);
                relative_path.push(key);
                match child {
                    Value::Object(ref object) if object.is_empty() => {
                        Self::ensure_nested_object(result, relative_path)?;
                        relative_path.truncate(parent_path_len);
                    }
                    Value::Object(ref object) => {
                        let cursor = object.cursor();
                        traversal.push(VirtualDataLookupTraversal {
                            node: child,
                            cursor,
                            path_len: relative_path.len(),
                        });
                    }
                    Value::Number(ref rule_index_value) => {
                        let rule_index = rule_index_value
                            .as_u64()
                            .and_then(|index| u16::try_from(index).ok())
                            .ok_or(VmError::InvalidRuleIndex {
                                rule_index: Value::Number(rule_index_value.clone()),
                                pc: self.pc,
                            })?;
                        if let Some(cached_result) =
                            self.virtual_data_lookup_cached(root_path, relative_path)
                        {
                            self.cache_hits =
                                self.checked_add_one(self.cache_hits, "cache hits counter")?;
                            Self::set_nested_value_static(result, relative_path, cached_result)?;
                            relative_path.truncate(parent_path_len);
                            continue;
                        }

                        let register = self.allocate_virtual_lookup_register()?;
                        frame.pending = Some(VirtualDataLookupPending::Subtree {
                            register,
                            parent_path_len,
                        });
                        return Ok(Some((register, rule_index)));
                    }
                    _ => relative_path.truncate(parent_path_len),
                }
            },
        }
    }

    fn allocate_virtual_lookup_register(&mut self) -> Result<u8> {
        let register =
            u8::try_from(self.registers.len()).map_err(|_| VmError::RegisterIndexOutOfBounds {
                index: u8::MAX,
                pc: self.pc,
                register_count: self.registers.len(),
            })?;
        self.registers.push(Value::Undefined);
        Ok(register)
    }

    fn virtual_data_lookup_cached(
        &self,
        root_path: &[Value],
        relative_path: &[Value],
    ) -> Option<Value> {
        let mut cache_lookup = &self.evaluated;
        for path_component in root_path.iter().chain(relative_path.iter()) {
            if let Value::Object(ref map) = *cache_lookup {
                cache_lookup = map.get(path_component)?;
            } else {
                return None;
            }
        }
        if let Value::Object(ref map) = *cache_lookup {
            map.get(&Value::Undefined).cloned()
        } else {
            None
        }
    }

    pub(super) fn execute_virtual_data_document_lookup(&mut self, params_index: u16) -> Result<()> {
        if self.execution_mode == ExecutionMode::Suspendable {
            return self.begin_suspendable_virtual_data_document_lookup(params_index);
        }

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
                        rule_index: Value::Number(rule_index_value.clone()),
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
