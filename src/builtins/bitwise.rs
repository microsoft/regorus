// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_numeric};

use crate::lexer::Span;
use crate::value::{Float, Value};

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

fn and(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "bits.and";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_numeric(name, &params[0], &args[0])?;
    let v2 = ensure_numeric(name, &params[1], &args[1])?;

    if v1 != v1.floor() || v2 != v2.floor() {
        return Ok(Value::Undefined);
    }

    // TODO: precision
    let v1 = v1 as i64;
    let v2 = v2 as i64;
    Ok(Value::from_float((v1 & v2) as Float))
}

fn lsh(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "bits.lsh";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_numeric(name, &params[0], &args[0])?;
    let v2 = ensure_numeric(name, &params[1], &args[1])?;

    if v1 != v1.floor() || v2 != v2.floor() {
        return Ok(Value::Undefined);
    }

    // TODO: precision
    let v1 = v1 as i64;
    let v2 = v2 as i64;

    if v2 <= 0 {
        return Ok(Value::Undefined);
    }

    Ok(Value::from_float((v1 << v2) as Float))
}

fn negate(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "bits.negate";
    ensure_args_count(span, name, params, args, 1)?;

    let v = ensure_numeric(name, &params[0], &args[0])?;

    if v != v.floor() {
        return Ok(Value::Undefined);
    }

    // TODO: precision
    let v = v as i64;
    Ok(Value::from_float((!v) as Float))
}

fn or(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "bits.or";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_numeric(name, &params[0], &args[0])?;
    let v2 = ensure_numeric(name, &params[1], &args[1])?;

    if v1 != v1.floor() || v2 != v2.floor() {
        return Ok(Value::Undefined);
    }

    // TODO: precision
    let v1 = v1 as i64;
    let v2 = v2 as i64;
    Ok(Value::from_float((v1 | v2) as Float))
}

fn rsh(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "bits.rsh";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_numeric(name, &params[0], &args[0])?;
    let v2 = ensure_numeric(name, &params[1], &args[1])?;

    if v1 != v1.floor() || v2 != v2.floor() {
        return Ok(Value::Undefined);
    }

    // TODO: precision
    let v1 = v1 as i64;
    let v2 = v2 as i64;

    if v2 < 0 {
        return Ok(Value::Undefined);
    }

    Ok(Value::from_float((v1 >> v2) as Float))
}

fn xor(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "bits.xor";
    ensure_args_count(span, name, params, args, 2)?;

    let v1 = ensure_numeric(name, &params[0], &args[0])?;
    let v2 = ensure_numeric(name, &params[1], &args[1])?;

    if v1 != v1.floor() || v2 != v2.floor() {
        return Ok(Value::Undefined);
    }

    // TODO: precision
    let v1 = v1 as i64;
    let v2 = v2 as i64;
    Ok(Value::from_float((v1 ^ v2) as Float))
}
