// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_set};
use crate::lexer::Span;
use crate::value::Value;
use crate::*;

use alloc::collections::BTreeSet;

use anyhow::{bail, Result};

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("intersection", (intersection_of_set_of_sets, 1));
    m.insert("union", (union_of_set_of_sets, 1));
    m.insert("__builtin_sets.union", (binary_set_union, 2));
    m.insert("__builtin_sets.intersection", (binary_set_intersection, 2));
}

pub fn intersection(expr1: &Expr, expr2: &Expr, v1: Value, v2: Value) -> Result<Value> {
    let s1 = ensure_set("intersection", expr1, v1)?;
    let s2 = ensure_set("intersection", expr2, v2)?;
    Ok(Value::from_set(s1.intersection(&s2).cloned().collect()))
}

pub fn union(expr1: &Expr, expr2: &Expr, v1: Value, v2: Value) -> Result<Value> {
    let s1 = ensure_set("union", expr1, v1)?;
    let s2 = ensure_set("union", expr2, v2)?;
    Ok(Value::from_set(s1.union(&s2).cloned().collect()))
}

pub fn difference(expr1: &Expr, expr2: &Expr, v1: Value, v2: Value) -> Result<Value> {
    let s1 = ensure_set("difference", expr1, v1)?;
    let s2 = ensure_set("difference", expr2, v2)?;
    Ok(Value::from_set(s1.difference(&s2).cloned().collect()))
}

fn binary_set_union(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "__builtin_sets.union";
    ensure_args_count(span, name, params, args, 2)?;
    let left = ensure_set(name, &params[0], args[0].clone())?;
    let right = ensure_set(name, &params[1], args[1].clone())?;
    Ok(Value::from_set(left.union(&right).cloned().collect()))
}

fn binary_set_intersection(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "__builtin_sets.intersection";
    ensure_args_count(span, name, params, args, 2)?;
    let left = ensure_set(name, &params[0], args[0].clone())?;
    let right = ensure_set(name, &params[1], args[1].clone())?;
    Ok(Value::from_set(
        left.intersection(&right).cloned().collect(),
    ))
}

fn intersection_of_set_of_sets(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "intersection";
    ensure_args_count(span, name, params, args, 1)?;
    let set = ensure_set(name, &params[0], args[0].clone())?;

    let mut res = BTreeSet::new();
    let mut first = true;

    for s in set.iter() {
        let s = match s {
            Value::Set(s) => s,
            _ => bail!(
                span.error(format!("`{name}` expects set of sets. Got `{}`", args[0]).as_str())
            ),
        };

        if first {
            res.clone_from(s);
            first = false;
        } else {
            res = res.intersection(s).cloned().collect();
        }
    }

    Ok(Value::from_set(res))
}

fn union_of_set_of_sets(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "union";
    ensure_args_count(span, name, params, args, 1)?;
    let set = ensure_set(name, &params[0], args[0].clone())?;

    let mut res = BTreeSet::new();

    for s in set.iter() {
        let s = match s {
            Value::Set(s) => s,
            _ => bail!(
                span.error(format!("`{name}` expects set of sets. Got `{}`", args[0]).as_str())
            ),
        };

        res = res.union(s).cloned().collect();
    }

    Ok(Value::from_set(res))
}
