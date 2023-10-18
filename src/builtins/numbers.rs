// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{ArithOp, Expr};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_numeric, ensure_string};
use crate::lexer::Span;
use crate::value::{Float, Value};

use std::collections::HashMap;

use anyhow::Result;
use rand::{thread_rng, Rng};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("abs", (abs, 1));
    m.insert("ceil", (ceil, 1));
    m.insert("floor", (floor, 1));
    m.insert("numbers.range", (range, 2));
    m.insert("rand.intn", (intn, 2));
    m.insert("round", (round, 1));
}

pub fn arithmetic_operation(
    op: &ArithOp,
    expr1: &Expr,
    expr2: &Expr,
    v1: Value,
    v2: Value,
) -> Result<Value> {
    let op_name = format!("{:?}", op).to_lowercase();
    let v1 = ensure_numeric(op_name.as_str(), expr1, &v1)?;
    let v2 = ensure_numeric(op_name.as_str(), expr2, &v2)?;

    Ok(Value::from_float(match op {
        ArithOp::Add => v1 + v2,
        ArithOp::Sub => v1 - v2,
        ArithOp::Mul => v1 * v2,
        ArithOp::Div if v2 == 0.0 => return Ok(Value::Undefined),
        ArithOp::Div => v1 / v2,
        ArithOp::Mod if v2 == 0.0 => return Ok(Value::Undefined),
        ArithOp::Mod if v1.floor() != v1 => return Ok(Value::Undefined),
        ArithOp::Mod if v2.floor() != v2 => return Ok(Value::Undefined),
        ArithOp::Mod => v1 % v2,
    }))
}

fn abs(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "abs", params, args, 1)?;
    Ok(Value::from_float(
        ensure_numeric("abs", &params[0], &args[0])?.abs(),
    ))
}

fn ceil(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "ceil", params, args, 1)?;
    Ok(Value::from_float(
        ensure_numeric("ceil", &params[0], &args[0])?.ceil(),
    ))
}

fn floor(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "floor", params, args, 1)?;
    Ok(Value::from_float(
        ensure_numeric("floor", &params[0], &args[0])?.floor(),
    ))
}

fn range(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "numbers.range", params, args, 2)?;
    let v1 = ensure_numeric("numbers.range", &params[0], &args[0].clone())?;
    let v2 = ensure_numeric("numbers.range", &params[1], &args[1].clone())?;

    if v1 != v1.floor() || v2 != v2.floor() {
        // TODO: OPA returns undefined here.
        // Can we emit a warning?
        return Ok(Value::Undefined);
    }
    let incr = if v2 >= v1 { 1 } else { -1 } as Float;

    let mut values = vec![];
    values.reserve((v2 - v1).abs() as usize + 1);

    let mut v = v1;
    while v != v2 {
        values.push(Value::from_float(v));
        v += incr;
    }
    values.push(Value::from_float(v));
    Ok(Value::from_array(values))
}

fn round(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "round", params, args, 1)?;
    Ok(Value::from_float(
        ensure_numeric("round", &params[0], &args[0])?.round(),
    ))
}

fn intn(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let fcn = "rand.intn";
    ensure_args_count(span, fcn, params, args, 2)?;
    let _ = ensure_string(fcn, &params[0], &args[0])?;
    let n = ensure_numeric(fcn, &params[0], &args[1])?;
    if n != n.floor() || n < 0 as Float {
        return Ok(Value::Undefined);
    }

    if n == 0.0 {
        return Ok(Value::from_float(0 as Float));
    }

    // TODO: bounds checking; arbitrary precision
    let mut rng = thread_rng();
    let v = rng.gen_range(0..n as u64);
    Ok(Value::from_float(v as f64))
}
