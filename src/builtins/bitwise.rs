// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_numeric};

use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::Result;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("bits.and", (and, 2));
    m.insert("bits.lsh", (lsh, 2));
    m.insert("bits.negate", (negate, 1));
    m.insert("bits.or", (or, 2));
    m.insert("bits.rsh", (rsh, 2));
    m.insert("bits.xor", (xor, 2));
}

fn and(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "bits.and";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_numeric(name, &params[0], &args[0])?;
    let v2 = ensure_numeric(name, &params[1], &args[1])?;

    Ok(match v1.and(&v2) {
        Some(v) => Value::from(v),
        _ => Value::Undefined,
    })
}

fn lsh(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "bits.lsh";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_numeric(name, &params[0], &args[0])?;
    let v2 = ensure_numeric(name, &params[1], &args[1])?;

    Ok(match v1.lsh(&v2) {
        Some(v) => Value::from(v),
        _ => Value::Undefined,
    })
}

fn negate(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "bits.negate";
    ensure_args_count(span, name, params, args, 1)?;

    let v = ensure_numeric(name, &params[0], &args[0])?;

    Ok(match v.neg() {
        Some(v) => Value::from(v),
        _ => Value::Undefined,
    })
}

fn or(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "bits.or";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_numeric(name, &params[0], &args[0])?;
    let v2 = ensure_numeric(name, &params[1], &args[1])?;

    Ok(match v1.or(&v2) {
        Some(v) => Value::from(v),
        _ => Value::Undefined,
    })
}

fn rsh(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "bits.rsh";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_numeric(name, &params[0], &args[0])?;
    let v2 = ensure_numeric(name, &params[1], &args[1])?;

    Ok(match v1.rsh(&v2) {
        Some(v) => Value::from(v),
        _ => Value::Undefined,
    })
}

fn xor(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "bits.xor";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_numeric(name, &params[0], &args[0])?;
    let v2 = ensure_numeric(name, &params[1], &args[1])?;

    Ok(match v1.xor(&v2) {
        Some(v) => Value::from(v),
        _ => Value::Undefined,
    })
}
