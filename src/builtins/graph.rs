// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{enforce_limit, ensure_args_count, ensure_object};
use crate::lexer::Span;
use crate::value::Value;
use crate::*;

use alloc::collections::{BTreeMap, BTreeSet};

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
    graph: &BTreeMap<Value, Value>,
    visited: &mut BTreeSet<Value>,
    node: &Value,
    path: &mut Vec<Value>,
    paths: &mut BTreeSet<Value>,
) -> Result<()> {
    if let Value::String(s) = node {
        if s.as_ref() == "" {
            if !path.is_empty() {
                paths.insert(Value::from_array(path.clone()));
                // Guard path result growth when terminating at empty edge.
                enforce_limit()?;
            }
            return Ok(());
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
        return Ok(());
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
        let n = match neighbors {
            Some(Value::Array(arr)) => {
                for n in arr.iter().rev() {
                    visit(graph, visited, n, path, paths)?;
                }
                arr.len()
            }
            Some(Value::Set(set)) => {
                for n in set.iter().rev() {
                    visit(graph, visited, n, path, paths)?;
                }
                set.len()
            }
            Some(&Value::Null) => 0,
            _ => bail!(format!("neighbors for node `{node}` must be array/set.")),
        };

        if n == 0 {
            // Current node has no neighbors.
            if !path.is_empty() {
                paths.insert(Value::from_array(path.clone()));
                // Guard path set growth when recording leaf nodes.
                enforce_limit()?;
            }
        }

        visited.remove(node);
        path.pop();
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
    {
        let path = Value::from_array(path.clone());
        paths.push(Value::from_array([path, value.clone()].into()));
        // Guard walk result growth when emitting a new path/value pair.
        enforce_limit()?;
    }
    match value {
        Value::Array(arr) => {
            for (idx, elem) in arr.iter().enumerate() {
                path.push(Value::from(idx));
                // Guard path stack growth while traversing array members.
                enforce_limit()?;
                walk_visit(path, elem, paths)?;
                path.pop();
            }
        }
        Value::Set(set) => {
            for elem in set.iter() {
                path.push(elem.clone());
                // Guard path stack growth while traversing set members.
                enforce_limit()?;
                walk_visit(path, elem, paths)?;
                path.pop();
            }
        }
        Value::Object(obj) => {
            for (key, value) in obj.iter() {
                path.push(key.clone());
                // Guard path stack growth while traversing object entries.
                enforce_limit()?;
                walk_visit(path, value, paths)?;
                path.pop();
            }
        }
        _ => (),
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
