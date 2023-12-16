// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{ArithOp, Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_numeric, ensure_string};
use crate::lexer::Span;
use crate::number::Number;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};
use rand::{thread_rng, Rng};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("abs", (abs, 1));
    m.insert("ceil", (ceil, 1));
    m.insert("floor", (floor, 1));
    m.insert("numbers.range", (range, 2));
    m.insert("numbers.range_step", (range_step, 3));
    m.insert("rand.intn", (intn, 2));
    m.insert("round", (round, 1));
}

pub fn arithmetic_operation(
    span: &Span,
    op: &ArithOp,
    expr1: &Expr,
    expr2: &Expr,
    v1: Value,
    v2: Value,
    strict: bool,
) -> Result<Value> {
    let op_name = format!("{:?}", op).to_lowercase();
    let v1 = ensure_numeric(op_name.as_str(), expr1, &v1)?;
    let v2 = ensure_numeric(op_name.as_str(), expr2, &v2)?;

    Ok(Value::from(match op {
        ArithOp::Add => v1.add(&v2)?,
        ArithOp::Sub => v1.sub(&v2)?,
        ArithOp::Mul => v1.mul(&v2)?,
        ArithOp::Div if strict && v2 == Number::from(0u64) => bail!(span.error("divide by zero")),
        ArithOp::Div if v2 == Number::from(0u64) => return Ok(Value::Undefined),
        ArithOp::Div => v1.divide(&v2)?,
        ArithOp::Mod if strict && v2 == Number::from(0u64) => bail!(span.error("modulo by zero")),
        ArithOp::Mod if v2 == Number::from(0u64) => return Ok(Value::Undefined),
        ArithOp::Mod if !v1.is_integer() || !v2.is_integer() => {
            bail!(span.error("modulo on floating-point number"))
        }
        ArithOp::Mod => v1.modulo(&v2)?,
    }))
}

fn abs(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "abs", params, args, 1)?;
    Ok(Value::from(
        ensure_numeric("abs", &params[0], &args[0])?.abs(),
    ))
}

fn ceil(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "ceil", params, args, 1)?;
    Ok(Value::from(
        ensure_numeric("ceil", &params[0], &args[0])?.ceil(),
    ))
}

fn floor(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "floor", params, args, 1)?;
    Ok(Value::from(
        ensure_numeric("floor", &params[0], &args[0])?.floor(),
    ))
}

fn range(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "numbers.range";
    ensure_args_count(span, name, params, args, 2)?;
    let v1 = ensure_numeric(name, &params[0], &args[0].clone())?;
    let v2 = ensure_numeric(name, &params[1], &args[1].clone())?;

    match v1.is_integer() {
        false if strict => bail!(params[0].span().error("operand must be integer")),
        false => return Ok(Value::Undefined),
        _ => (),
    }

    match v2.is_integer() {
        false if strict => bail!(params[1].span().error("operand must be integer")),
        false => return Ok(Value::Undefined),
        _ => (),
    }

    let (incr, num_elements) = match v2.sub(&v1)?.as_i64() {
        Some(v) if v >= 0 => (1i64, v as usize + 1),
        Some(v) => (-1i64, (-v + 1) as usize),
        _ => bail!(span.error("could not determine number of elements")),
    };

    let mut values = Vec::with_capacity(num_elements);
    let mut v = v1;
    let incr = Number::from(incr);
    while v != v2 {
        values.push(Value::from(v.clone()));
        v.add_assign(&incr)?;
    }
    values.push(Value::from(v));
    Ok(Value::from_array(values))
}

fn range_step(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "numbers.range_step";
    ensure_args_count(span, name, params, args, 3)?;
    let v1 = ensure_numeric(name, &params[0], &args[0].clone())?;
    let v2 = ensure_numeric(name, &params[1], &args[1].clone())?;
    let incr = ensure_numeric(name, &params[2], &args[2].clone())?;

    match v1.is_integer() {
        false if strict => bail!(params[0].span().error("operand must be integer")),
        false => return Ok(Value::Undefined),
        _ => (),
    }

    match v2.is_integer() {
        false if strict => bail!(params[1].span().error("operand must be integer")),
        false => return Ok(Value::Undefined),
        _ => (),
    }

    if strict && (!incr.is_integer() || incr <= Number::from(0u64)) {
        bail!(params[2].span().error("step must be a positive integer"))
    }

    let (incr, num_elements) = match (v2.sub(&v1)?.as_i64(), incr.as_i64()) {
        (Some(v), Some(incr)) if v >= 0 => (incr, v / incr + 1),
        (Some(v), Some(incr)) => (-incr, -v / incr + 1),
        _ => bail!(span.error("could not determine number of elements")),
    };

    let mut values = Vec::with_capacity(num_elements as usize);
    let incr = Number::from(incr);
    let mut v = v1;
    while (v <= v2 && incr.is_positive()) || (v >= v2 && !incr.is_positive()) {
        values.push(Value::from(v.clone()));
        v.add_assign(&incr)?;
    }

    Ok(Value::from_array(values))
}

fn round(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "round";
    ensure_args_count(span, name, params, args, 1)?;
    Ok(Value::from(
        ensure_numeric(name, &params[0], &args[0])?.round(),
    ))
}

fn intn(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let fcn = "rand.intn";
    ensure_args_count(span, fcn, params, args, 2)?;
    let _ = ensure_string(fcn, &params[0], &args[0])?;
    let n = ensure_numeric(fcn, &params[0], &args[1])?;

    Ok(match n.as_u64() {
        Some(0) => Value::from(0u64),
        Some(n) => {
            // TODO: bounds checking; arbitrary precision
            let mut rng = thread_rng();
            let v = rng.gen_range(0..n);
            Value::from(v)
        }
        _ => Value::Undefined,
    })
}
