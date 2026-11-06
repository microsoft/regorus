// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{enforce_limit, ensure_args_count, ensure_object};
use crate::lexer::Span;
use crate::value::Object;
use crate::value::Value;
use crate::*;

use alloc::collections::BTreeSet;

use anyhow::{bail, Result};

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("graph.reachable", (reachable, 2));
    m.insert("graph.reachable_paths", (reachable_paths, 2));
    m.insert("walk", (walk, 1));
}

fn reachable(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "graph.reachable";
    ensure_args_count(span, name, params, args, 2)?;

    let graph = ensure_object(name, &params[0], args[0].clone())?;
    let mut worklist = vec![];

    match &args[1] {
        Value::Array(arr) => {
            for node in arr.iter() {
                worklist.push(node.clone());
                // Guard worklist growth when seeding traversal from an array.
                enforce_limit()?;
            }
        }
        Value::Set(set) => {
            for node in set.iter() {
                worklist.push(node.clone());
                // Guard worklist growth when seeding traversal from a set.
                enforce_limit()?;
            }
        }
        _ if strict => bail!(params[1].span().error("initial vertices must be array/set")),
        _ => return Ok(Value::Undefined),
    }

    let mut reachable = BTreeSet::new();
    while let Some(v) = worklist.pop() {
        if reachable.contains(&v) {
            continue;
        }

        match graph.get(&v) {
            Some(Value::Array(arr)) => {
                for neighbor in arr.iter() {
                    worklist.push(neighbor.clone());
                    // Guard worklist growth when enqueuing array neighbors.
                    enforce_limit()?;
                }
            }
            Some(Value::Set(set)) => {
                for neighbor in set.iter() {
                    worklist.push(neighbor.clone());
                    // Guard worklist growth when enqueuing set neighbors.
                    enforce_limit()?;
                }
            }
            Some(_) => (),
            _ => continue,
        }

        reachable.insert(v);
        // Guard reachable set size as discovered vertices accumulate.
        enforce_limit()?;
    }

    Ok(Value::from_set(reachable))
}

fn visit(
    graph: &Object,
    visited: &mut BTreeSet<Value>,
    node: &Value,
    path: &mut Vec<Value>,
    paths: &mut BTreeSet<Value>,
) -> Result<()> {
    enum Frame<'a> {
        Node(&'a Value),
        Neighbors(Box<dyn Iterator<Item = &'a Value> + 'a>),
        Leave(&'a Value),
    }
    let mut pending = vec![Frame::Node(node)];
    while let Some(frame) = pending.pop() {
        enforce_limit()?;
        let node = match frame {
            Frame::Node(node) => node,
            Frame::Neighbors(mut neighbors) => {
                if let Some(node) = neighbors.next() {
                    pending.push(Frame::Neighbors(neighbors));
                    pending.push(Frame::Node(node));
                }
                continue;
            }
            Frame::Leave(node) => {
                visited.remove(node);
                path.pop();
                continue;
            }
        };
        if let Value::String(s) = node {
            if s.as_ref() == "" {
                if !path.is_empty() {
                    paths.insert(Value::from_array(path.clone()));
                    // Guard path result growth when terminating at empty edge.
                    enforce_limit()?;
                }
                continue;
            }
        }

        let neighbors = graph.get(node);
        if neighbors.is_none() {
            // Current node is not valid. Add path as is.
            if !path.is_empty() {
                paths.insert(Value::from_array(path.clone()));
                // Guard path set growth when encountering missing nodes.
                enforce_limit()?;
            }
            continue;
        }

        if visited.contains(node) {
            paths.insert(Value::from_array(path.clone()));
            // Guard path set growth when detecting a cycle.
            enforce_limit()?;
        } else {
            path.push(node.clone());
            // Guard path stack growth while descending the graph.
            enforce_limit()?;
            visited.insert(node.clone());
            // Guard visited set growth while marking nodes as seen.
            enforce_limit()?;
            let (empty, children): (bool, Box<dyn Iterator<Item = &Value>>) = match neighbors {
                Some(Value::Array(arr)) => (arr.is_empty(), Box::new(arr.iter().rev())),
                Some(Value::Set(set)) => (set.is_empty(), Box::new(set.iter().rev())),
                Some(&Value::Null) => (true, Box::new(core::iter::empty())),
                _ => bail!(format!("neighbors for node `{node}` must be array/set.")),
            };

            if empty {
                // Current node has no neighbors.
                if !path.is_empty() {
                    paths.insert(Value::from_array(path.clone()));
                    // Guard path set growth when recording leaf nodes.
                    enforce_limit()?;
                }
            }

            pending.push(Frame::Leave(node));
            pending.push(Frame::Neighbors(children));
        }
    }

    Ok(())
}

fn reachable_paths(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    strict: bool,
) -> Result<Value> {
    let name = "graph.reachable_paths";
    ensure_args_count(span, name, params, args, 2)?;

    let graph = ensure_object(name, &params[0], args[0].clone())?;
    let mut visited = BTreeSet::new();
    let mut path = vec![];
    let mut paths = BTreeSet::new();

    match &args[1] {
        Value::Array(arr) => {
            for node in arr.iter() {
                visit(&graph, &mut visited, node, &mut path, &mut paths)?;
            }
        }
        Value::Set(set) => {
            for node in set.iter() {
                visit(&graph, &mut visited, node, &mut path, &mut paths)?;
            }
        }
        _ if strict => bail!(params[1].span().error("initial vertices must be array/set")),
        _ => return Ok(Value::Undefined),
    }

    Ok(Value::from_set(paths))
}

fn walk_visit(path: &mut Vec<Value>, value: &Value, paths: &mut Vec<Value>) -> Result<()> {
    enum Frame<'a> {
        Value(&'a Value),
        Children(Box<dyn Iterator<Item = (Value, &'a Value)> + 'a>),
        Leave,
    }
    let mut pending = vec![Frame::Value(value)];
    while let Some(frame) = pending.pop() {
        enforce_limit()?;
        let value = match frame {
            Frame::Value(value) => value,
            Frame::Children(mut children) => {
                if let Some((key, value)) = children.next() {
                    pending.push(Frame::Children(children));
                    path.push(key);
                    pending.push(Frame::Leave);
                    pending.push(Frame::Value(value));
                }
                continue;
            }
            Frame::Leave => {
                path.pop();
                continue;
            }
        };
        {
            let path = Value::from_array(path.clone());
            paths.push(Value::from_array([path, value.clone()].into()));
            // Guard walk result growth when emitting a new path/value pair.
            enforce_limit()?;
        }
        let children: Box<dyn Iterator<Item = (Value, &Value)>> = match value {
            Value::Array(arr) => Box::new(
                arr.iter()
                    .enumerate()
                    .map(|(index, value)| (Value::from(index), value)),
            ),
            Value::Set(set) => Box::new(set.iter().map(|value| (value.clone(), value))),
            Value::Object(obj) => {
                Box::new(obj.iter_sorted().map(|(key, value)| (key.clone(), value)))
            }
            _ => Box::new(core::iter::empty()),
        };
        pending.push(Frame::Children(children));
    }
    Ok(())
}

fn walk(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "walk";
    ensure_args_count(span, name, params, args, 1)?;
    let mut paths = vec![];
    walk_visit(&mut vec![], &args[0], &mut paths)?;
    Ok(Value::from_array(paths))
}
