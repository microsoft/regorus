// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! OPA-compatible edit tree used by `json.patch`.
//!
//! The design follows OPA's `internal/edittree`: patch operations update an
//! intermediate tree and the final `Value` is rendered once. Arrays use a
//! `VecDeque`, making repeated edits at either end cheap instead of cloning
//! and shifting the complete source array for every operation.

#![allow(clippy::pattern_type_mismatch)]

use super::utils::enforce_limit;
use crate::number::Number;
use crate::value::Object;
use crate::Value;
use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::string::ToString as _;
use alloc::vec::Vec;
use anyhow::{anyhow, bail, Result};

#[derive(Debug)]
enum EditNode {
    Scalar(Value),
    Object(BTreeMap<Value, EditNode>),
    Array(VecDeque<EditNode>),
    // Sets are content-addressed. The rendered member is kept as the key and
    // refreshed whenever a nested edit changes that member.
    Set(BTreeMap<Value, EditNode>),
}

impl EditNode {
    fn from_value(value: &Value) -> Result<Self> {
        enforce_limit()?;
        Ok(match value {
            Value::Object(object) => {
                let mut fields = BTreeMap::new();
                for (key, value) in object.iter() {
                    fields.insert(key.clone(), Self::from_value(value)?);
                    enforce_limit()?;
                }
                Self::Object(fields)
            }
            Value::Array(array) => {
                let mut items = VecDeque::with_capacity(array.len());
                for value in array.iter() {
                    items.push_back(Self::from_value(value)?);
                    enforce_limit()?;
                }
                Self::Array(items)
            }
            Value::Set(set) => {
                let mut members = BTreeMap::new();
                for value in set.iter() {
                    members.insert(value.clone(), Self::from_value(value)?);
                    enforce_limit()?;
                }
                Self::Set(members)
            }
            scalar => Self::Scalar(scalar.clone()),
        })
    }

    fn render(&self) -> Result<Value> {
        enforce_limit()?;
        Ok(match self {
            Self::Scalar(value) => value.clone(),
            Self::Object(fields) => {
                let mut object = Object::new();
                for (key, value) in fields {
                    object.insert(key.clone(), value.render()?);
                    enforce_limit()?;
                }
                Value::Object(crate::Rc::new(object))
            }
            Self::Array(items) => {
                let mut array = Vec::with_capacity(items.len());
                for value in items {
                    array.push(value.render()?);
                    enforce_limit()?;
                }
                Value::Array(crate::Rc::new(crate::value::Array::from(array)))
            }
            Self::Set(members) => {
                let mut set = BTreeSet::new();
                for value in members.values() {
                    set.insert(value.render()?);
                    enforce_limit()?;
                }
                Value::from_set(set)
            }
        })
    }

    fn get(&self, path: &[Value]) -> Result<&Self> {
        let Some((head, rest)) = path.split_first() else {
            return Ok(self);
        };
        match self {
            Self::Object(fields) => fields
                .get(head)
                .ok_or_else(|| anyhow!("path {head} does not exist in object"))?
                .get(rest),
            Self::Array(items) => {
                let index = array_index(items.len(), head, false)?;
                items
                    .get(index)
                    .ok_or_else(|| anyhow!("array index disappeared"))?
                    .get(rest)
            }
            Self::Set(members) => members
                .get(head)
                .ok_or_else(|| anyhow!("path {head} does not exist in set"))?
                .get(rest),
            Self::Scalar(value) => bail!("expected composite type, found value: {value}"),
        }
    }

    fn insert(&mut self, path: &[Value], value: EditNode) -> Result<()> {
        enforce_limit()?;
        let Some((head, rest)) = path.split_first() else {
            *self = value;
            return Ok(());
        };
        match self {
            Self::Object(fields) => {
                if rest.is_empty() {
                    fields.insert(head.clone(), value);
                } else {
                    fields
                        .get_mut(head)
                        .ok_or_else(|| anyhow!("path {head} does not exist in object"))?
                        .insert(rest, value)?;
                }
            }
            Self::Array(items) => {
                let index = array_index(items.len(), head, rest.is_empty())?;
                if rest.is_empty() {
                    items.insert(index, value);
                } else {
                    items
                        .get_mut(index)
                        .ok_or_else(|| anyhow!("array index disappeared"))?
                        .insert(rest, value)?;
                }
            }
            Self::Set(members) => {
                if rest.is_empty() {
                    let rendered = value.render()?;
                    if head != &rendered {
                        bail!("set key {head} does not equal value to be inserted {rendered}");
                    }
                    members.insert(rendered, value);
                } else {
                    let mut member = members
                        .remove(head)
                        .ok_or_else(|| anyhow!("path {head} does not exist in set"))?;
                    member.insert(rest, value)?;
                    let new_key = member.render()?;
                    members.insert(new_key, member);
                }
            }
            Self::Scalar(current) => {
                bail!("expected composite type, found value: {current}")
            }
        }
        enforce_limit()?;
        Ok(())
    }

    fn remove(&mut self, path: &[Value]) -> Result<EditNode> {
        enforce_limit()?;
        let (head, rest) = path
            .split_first()
            .ok_or_else(|| anyhow!("cannot remove node without a path"))?;
        let removed = match self {
            Self::Object(fields) => {
                if rest.is_empty() {
                    fields
                        .remove(head)
                        .ok_or_else(|| anyhow!("path {head} does not exist in object"))?
                } else {
                    fields
                        .get_mut(head)
                        .ok_or_else(|| anyhow!("path {head} does not exist in object"))?
                        .remove(rest)?
                }
            }
            Self::Array(items) => {
                let index = array_index(items.len(), head, false)?;
                if rest.is_empty() {
                    items
                        .remove(index)
                        .ok_or_else(|| anyhow!("array index disappeared"))?
                } else {
                    items
                        .get_mut(index)
                        .ok_or_else(|| anyhow!("array index disappeared"))?
                        .remove(rest)?
                }
            }
            Self::Set(members) => {
                if rest.is_empty() {
                    members
                        .remove(head)
                        .ok_or_else(|| anyhow!("path {head} does not exist in set"))?
                } else {
                    let mut member = members
                        .remove(head)
                        .ok_or_else(|| anyhow!("path {head} does not exist in set"))?;
                    let removed = member.remove(rest)?;
                    let new_key = member.render()?;
                    members.insert(new_key, member);
                    removed
                }
            }
            Self::Scalar(current) => {
                bail!("expected composite type, found value: {current}")
            }
        };
        enforce_limit()?;
        Ok(removed)
    }

    #[cfg(test)]
    fn replace(&mut self, path: &[Value], value: EditNode) -> Result<()> {
        enforce_limit()?;
        let Some((head, rest)) = path.split_first() else {
            *self = value;
            return Ok(());
        };
        match self {
            Self::Object(fields) => {
                if rest.is_empty() {
                    let slot = fields
                        .get_mut(head)
                        .ok_or_else(|| anyhow!("path {head} does not exist in object"))?;
                    *slot = value;
                } else {
                    fields
                        .get_mut(head)
                        .ok_or_else(|| anyhow!("path {head} does not exist in object"))?
                        .replace(rest, value)?;
                }
            }
            Self::Array(items) => {
                let index = array_index(items.len(), head, false)?;
                let slot = items
                    .get_mut(index)
                    .ok_or_else(|| anyhow!("array index disappeared"))?;
                if rest.is_empty() {
                    *slot = value;
                } else {
                    slot.replace(rest, value)?;
                }
            }
            Self::Set(members) => {
                let mut member = members
                    .remove(head)
                    .ok_or_else(|| anyhow!("path {head} does not exist in set"))?;
                if rest.is_empty() {
                    member = value;
                } else {
                    member.replace(rest, value)?;
                }
                let new_key = member.render()?;
                members.insert(new_key, member);
            }
            Self::Scalar(current) => {
                bail!("expected composite type, found value: {current}")
            }
        }
        enforce_limit()?;
        Ok(())
    }
}

struct EditTree {
    root: Option<EditNode>,
}

impl EditTree {
    fn new(value: &Value) -> Result<Self> {
        Ok(Self {
            root: Some(EditNode::from_value(value)?),
        })
    }

    fn root(&self) -> Result<&EditNode> {
        self.root
            .as_ref()
            .ok_or_else(|| anyhow!("path does not exist in deleted document"))
    }

    fn root_mut(&mut self) -> Result<&mut EditNode> {
        self.root
            .as_mut()
            .ok_or_else(|| anyhow!("path does not exist in deleted document"))
    }

    fn insert_value(&mut self, path: &[Value], value: &Value) -> Result<()> {
        let node = EditNode::from_value(value)?;
        if path.is_empty() {
            self.root = Some(node);
        } else {
            self.root_mut()?.insert(path, node)?;
        }
        Ok(())
    }

    fn insert_node(&mut self, path: &[Value], node: EditNode) -> Result<()> {
        if path.is_empty() {
            self.root = Some(node);
        } else {
            self.root_mut()?.insert(path, node)?;
        }
        Ok(())
    }

    fn remove(&mut self, path: &[Value]) -> Result<EditNode> {
        if path.is_empty() {
            self.root
                .take()
                .ok_or_else(|| anyhow!("root is already deleted"))
        } else {
            self.root_mut()?.remove(path)
        }
    }

    #[cfg(test)]
    fn replace_value(&mut self, path: &[Value], value: &Value) -> Result<()> {
        let node = EditNode::from_value(value)?;
        if path.is_empty() {
            self.root = Some(node);
        } else {
            self.root_mut()?.replace(path, node)?;
        }
        Ok(())
    }

    fn render(self) -> Result<Value> {
        match self.root {
            Some(root) => root.render(),
            None => Ok(Value::Undefined),
        }
    }
}

pub(super) fn apply(target: &Value, operations: &[Value]) -> Result<Value> {
    let mut tree = EditTree::new(target)?;
    for operation in operations {
        enforce_limit()?;
        let object = match operation {
            Value::Object(object) => object,
            _ => bail!(
                "must be an array of JSON-Patch objects, but at least one element is not an object"
            ),
        };
        let field = |name: &str| -> Result<&Value> {
            object
                .get(&Value::from(name))
                .ok_or_else(|| anyhow!("missing '{name}' attribute"))
        };
        let operation_name = match field("op")? {
            Value::String(name) => name.as_ref(),
            _ => bail!("attribute 'op' must be a string"),
        };

        match operation_name {
            "add" => {
                let path = parse_path(field("path")?)?;
                tree.insert_value(&path, field("value")?)?;
            }
            "remove" => {
                let path = parse_path(field("path")?)?;
                tree.remove(&path)?;
            }
            "replace" => {
                let path = parse_path(field("path")?)?;
                // OPA composes replace from delete + insert. This distinction
                // is observable for sets, whose keys must equal their values:
                // replacing member "a" at path ["a"] with "b" must fail
                // rather than silently changing the set's membership key.
                tree.remove(&path)?;
                tree.insert_value(&path, field("value")?)?;
            }
            "move" => {
                let from = parse_path(field("from")?)?;
                let path = parse_path(field("path")?)?;
                let node = tree.remove(&from)?;
                tree.insert_node(&path, node)?;
            }
            "copy" => {
                let from = parse_path(field("from")?)?;
                let path = parse_path(field("path")?)?;
                let value = tree.root()?.get(&from)?.render()?;
                tree.insert_value(&path, &value)?;
            }
            "test" => {
                let path = parse_path(field("path")?)?;
                let actual = tree.root()?.get(&path)?.render()?;
                let expected = field("value")?;
                if &actual != expected {
                    bail!(
                        "value from patch != expected value.\n\nExpected: {expected}\n\nFound: {actual}"
                    );
                }
            }
            other => bail!("unrecognized op '{other}'"),
        }
    }
    tree.render()
}

fn parse_path(path: &Value) -> Result<Vec<Value>> {
    match path {
        Value::String(path) if path.is_empty() => Ok(Vec::new()),
        Value::String(path) => Ok(path
            .trim_start_matches('/')
            .split('/')
            .map(|part| Value::from(part.replace("~1", "/").replace("~0", "~")))
            .collect()),
        Value::Array(parts) => Ok(parts.iter().cloned().collect()),
        _ => bail!("path must be a string or an array of path segments"),
    }
}

fn array_index(length: usize, segment: &Value, append_ok: bool) -> Result<usize> {
    let raw = match segment {
        Value::Number(Number::UInt(value)) => {
            i64::try_from(*value).map_err(|_| anyhow!("array index is too large"))?
        }
        Value::Number(Number::Int(value)) => *value,
        Value::Number(Number::BigInt(value)) => value
            .to_string()
            .parse::<i64>()
            .map_err(|_| anyhow!("array index is too large"))?,
        Value::Number(Number::Float(_)) => bail!("array index must be an integer"),
        Value::String(value) if value.as_ref() == "-" => {
            if !append_ok {
                bail!("'-' index is not valid here");
            }
            i64::try_from(length).map_err(|_| anyhow!("array too large to index"))?
        }
        Value::String(value) => {
            if value.as_ref() != "0" && value.starts_with('0') {
                bail!("leading zeros are not allowed in JSON paths");
            }
            value
                .parse::<i64>()
                .map_err(|_| anyhow!("invalid string for indexing"))?
        }
        _ => bail!("invalid type for indexing"),
    };
    let index = usize::try_from(raw).map_err(|_| anyhow!("negative index: {raw}"))?;
    let in_bounds = if append_ok {
        index <= length
    } else {
        index < length
    };
    if !in_bounds {
        bail!("index {index} out of bounds for length {length}");
    }
    Ok(index)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn operation(json: &str) -> Value {
        Value::from_json_str(json).expect("valid patch operation")
    }

    #[test]
    fn repeated_front_removals_do_not_rebuild_the_array() {
        const LENGTH: usize = 4096;
        const REMOVALS: usize = 2048;

        let target = Value::from_array((0..LENGTH).map(Value::from).collect());
        let remove_front = operation(r#"{"op":"remove","path":"/0"}"#);
        let operations = alloc::vec![remove_front; REMOVALS];

        let result = apply(&target, &operations).expect("patch must succeed");
        let array = result.as_array().expect("result must be an array");
        assert_eq!(array.len(), LENGTH - REMOVALS);
        assert_eq!(array.first(), Some(&Value::from(REMOVALS)));
        // The immutable input is not modified if applying a patch succeeds or
        // fails; the edit tree owns all intermediate state.
        assert_eq!(
            target.as_array().expect("input must be an array").len(),
            LENGTH
        );
    }

    #[test]
    fn failed_patch_does_not_modify_the_input() {
        let target = Value::from_json_str(r#"{"a":[1,2,3]}"#).expect("valid target");
        let original = target.clone();
        let operations = [
            operation(r#"{"op":"remove","path":"/a/0"}"#),
            operation(r#"{"op":"remove","path":"/missing"}"#),
        ];

        apply(&target, &operations).expect_err("patch must fail");
        assert_eq!(target, original);
    }

    #[test]
    fn move_uses_post_removal_array_indexes() {
        let target = Value::from_json_str(r#"["a","b","c","d"]"#).expect("valid target");
        let operations = [operation(r#"{"op":"move","from":"/1","path":"/3"}"#)];
        let expected = Value::from_json_str(r#"["a","c","d","b"]"#).expect("valid expected value");

        assert_eq!(
            apply(&target, &operations).expect("patch must succeed"),
            expected
        );
    }

    #[test]
    fn deep_paths_survive_edit_and_render() {
        const DEPTH: usize = 128;
        let key = Value::from("k");
        let mut target = Value::from(0);
        for _ in 0..DEPTH {
            let mut object = Object::new();
            object.insert(key.clone(), target);
            target = Value::Object(crate::Rc::new(object));
        }
        let path = alloc::vec![key; DEPTH];

        let mut tree = EditTree::new(&target).expect("tree construction must succeed");
        tree.replace_value(&path, &Value::from(9))
            .expect("replace must succeed");
        let rendered = tree.render().expect("render must succeed");

        let mut leaf = &rendered;
        for segment in &path {
            leaf = match leaf {
                Value::Object(object) => {
                    object.get(segment).expect("deep path must survive render")
                }
                other => panic!("expected object on deep path, found {other}"),
            };
        }
        assert_eq!(leaf, &Value::from(9));
    }
}
