// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::LiteralOrRegister;
use crate::value::{Object, ObjectCursor, Value};
use crate::Rc;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::convert::TryFrom as _;

use super::errors::{Result, VmError};
use super::execution_model::ExecutionMode;
use super::machine::RegoVM;

#[derive(Debug, Clone)]
pub(super) struct VirtualLookupContinuation {
    pc: usize,
    dest: u8,
    result: Value,
    nodes: Vec<(Rc<Object>, ObjectCursor)>,
    path: Vec<Value>,
    next_node: Option<Value>,
    pending_path: Option<Vec<Value>>,
    root_path: Option<Vec<Value>>,
    remainder: Vec<Value>,
}

impl RegoVM {
    pub(super) fn continue_virtual_data_lookup(&mut self) -> Result<()> {
        let mut lookup = self
            .execution_stack
            .last_mut()
            .and_then(|frame| frame.virtual_lookup.take())
            .ok_or(VmError::MissingExecutionFrame {
                context: "continuing virtual data lookup",
                pc: self.pc,
            })?;
        self.pc = lookup.pc;

        if let Some(path) = lookup.pending_path.take() {
            let value = self.get_register(lookup.dest)?.clone();
            Self::set_nested_value(&mut lookup.result, &path, value.clone())?;
            if let Some(ref root_path) = lookup.root_path {
                let mut cache_path = root_path.clone();
                cache_path.extend_from_slice(&path);
                cache_path.push(Value::Undefined);
                Self::set_nested_value(&mut self.evaluated, &cache_path, value)?;
            }
        }

        if let Some((path, rule_index)) = self.next_virtual_lookup_rule(&mut lookup)? {
            let dest = lookup.dest;
            let cached = lookup
                .root_path
                .as_ref()
                .and_then(|root| self.cached_virtual_rule(root, &path));
            lookup.pending_path = Some(path);
            self.save_virtual_lookup(lookup)?;
            if let Some(value) = cached {
                self.cache_hits = self.checked_add_one(self.cache_hits, "cache hits counter")?;
                self.set_register(dest, value)?;
            } else {
                self.execute_call_rule_suspendable(dest, rule_index, None)?;
            }
        } else {
            let mut result = &lookup.result;
            for key in &lookup.remainder {
                result = &result[key];
            }
            self.set_register(lookup.dest, result.clone())?;
        }
        Ok(())
    }

    fn next_virtual_lookup_rule(
        &mut self,
        lookup: &mut VirtualLookupContinuation,
    ) -> Result<Option<(Vec<Value>, u16)>> {
        loop {
            self.execution_timer_tick(1)?;
            self.memory_check()?;
            if let Some(node) = lookup.next_node.take() {
                match node {
                    Value::Number(index) => {
                        let rule_index = index
                            .as_u64()
                            .and_then(|index| u16::try_from(index).ok())
                            .ok_or(VmError::InvalidRuleIndex {
                                rule_index: Value::Number(index),
                                pc: self.pc,
                            })?;
                        let path = lookup.path.clone();
                        lookup.path.pop();
                        return Ok(Some((path, rule_index)));
                    }
                    Value::Object(object) => {
                        let cursor = object.cursor();
                        lookup.nodes.push((object, cursor));
                    }
                    _ => {
                        lookup.path.pop();
                    }
                }
            }
            let Some(&mut (ref object, ref mut cursor)) = lookup.nodes.last_mut() else {
                return Ok(None);
            };
            if let Some((key, child)) = object.next(cursor) {
                lookup.path.push(key.clone());
                lookup.next_node = Some(child.clone());
            } else {
                lookup.nodes.pop();
                lookup.path.pop();
            }
        }
    }

    fn save_virtual_lookup(&mut self, lookup: VirtualLookupContinuation) -> Result<()> {
        let frame = self
            .execution_stack
            .last_mut()
            .ok_or(VmError::MissingExecutionFrame {
                context: "saving virtual data lookup",
                pc: self.pc,
            })?;
        frame.virtual_lookup = Some(lookup);
        Ok(())
    }

    fn schedule_virtual_subobject(
        &mut self,
        dest: u8,
        root_path: Vec<Value>,
        data: Value,
        tree: Value,
    ) -> Result<()> {
        self.save_virtual_lookup(VirtualLookupContinuation {
            pc: self.pc,
            dest,
            result: if data == Value::Undefined {
                Value::new_object()
            } else {
                data
            },
            nodes: Vec::new(),
            path: Vec::new(),
            next_node: Some(tree),
            pending_path: None,
            root_path: Some(root_path),
            remainder: Vec::new(),
        })
    }

    fn cached_virtual_rule(&self, root_path: &[Value], relative_path: &[Value]) -> Option<Value> {
        let mut node = &self.evaluated;
        for key in root_path.iter().chain(relative_path) {
            node = node.as_object().ok()?.get(key)?;
        }
        node.as_object().ok()?.get(&Value::Undefined).cloned()
    }

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
                    let cached_result = self.cached_virtual_rule(root_path, relative_path);

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

        match *current_node {
            Value::Number(ref rule_index_value) => {
                if let Some(rule_index) = rule_index_value.as_u64() {
                    let rule_index =
                        u16::try_from(rule_index).map_err(|_| VmError::InvalidRuleIndex {
                            rule_index: Value::Number(rule_index_value.clone()),
                            pc: self.pc,
                        })?;

                    if self.execution_mode == ExecutionMode::Suspendable {
                        // Snapshot keys before a child rule can overwrite the destination.
                        let remainder = params
                            .path_components
                            .iter()
                            .skip(components_consumed)
                            .map(|component| self.literal_or_register_value(component))
                            .collect::<Result<Vec<_>>>()?;
                        return self.save_virtual_lookup(VirtualLookupContinuation {
                            pc: self.pc,
                            dest: params.dest,
                            result: Value::Undefined,
                            nodes: Vec::new(),
                            path: Vec::new(),
                            next_node: Some(Value::from(u64::from(rule_index))),
                            pending_path: None,
                            root_path: None,
                            remainder,
                        });
                    }
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
                if self.execution_mode == ExecutionMode::Suspendable {
                    let mut root_path = Vec::new();
                    for (index, component) in params.path_components.iter().enumerate() {
                        let mut key = self.literal_or_register_value(component)?;
                        if string_fallback_indices.contains(&index) {
                            key = Value::from(key.to_string());
                        }
                        root_path.push(key);
                    }
                    return self.schedule_virtual_subobject(
                        params.dest,
                        root_path,
                        data_subobject,
                        rule_tree_subobject,
                    );
                }
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

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::collections::BTreeMap;

    #[test]
    #[allow(clippy::panic_in_result_fn)]
    fn virtual_namespace_cursor_retains_only_active_path() -> Result<()> {
        let leaves = (0..4096)
            .map(|index| (Value::from(index), Value::from(0)))
            .collect::<BTreeMap<_, _>>();
        let mut tree = Value::from(leaves);
        for _ in 0..24 {
            tree = Value::from(
                [(Value::from("prefix"), tree)]
                    .into_iter()
                    .collect::<BTreeMap<_, _>>(),
            );
        }
        let mut lookup = VirtualLookupContinuation {
            pc: 0,
            dest: 0,
            result: Value::new_object(),
            nodes: Vec::new(),
            path: Vec::new(),
            next_node: Some(tree),
            pending_path: None,
            root_path: Some(Vec::new()),
            remainder: Vec::new(),
        };
        assert!(lookup.nodes.is_empty());
        let mut vm = RegoVM::new();
        let mut count = 0_usize;
        while let Some((path, rule_index)) = vm.next_virtual_lookup_rule(&mut lookup)? {
            assert_eq!(path.len(), 25);
            assert_eq!(rule_index, 0);
            assert!(lookup.nodes.len() <= 25);
            assert_eq!(lookup.path.len(), 24);
            count = count.saturating_add(1);
        }
        assert_eq!(count, 4096);
        assert!(lookup.nodes.is_empty());
        assert!(lookup.path.is_empty());
        Ok(())
    }
}
