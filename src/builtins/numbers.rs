// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{ArithOp, Expr};
use crate::lexer::Span;
use crate::value::{Float, Value};

use anyhow::{bail, Result};

fn ensure_args_count(
    span: &Span,
    fcn: &'static str,
    params: &[Expr],
    args: &[Value],
    expected: usize,
) -> Result<()> {
    if args.len() != expected {
        let span = match args.len() > expected {
            false => span,
            true => params[args.len() - 1].span(),
        };
        if expected == 1 {
            bail!(span.error(format!("`{fcn}` expects 1 argument").as_str()))
        } else {
            bail!(span.error(format!("`{fcn}` expects {expected} arguments").as_str()))
        }
    }
    Ok(())
}

fn ensure_numeric(fcn: &str, arg: &Expr, v: &Value) -> Result<Float> {
    Ok(match &v {
        Value::Number(n) => n.0 .0,
        _ => {
            let span = arg.span();
            bail!(
                span.error(format!("`{fcn}` expects numeric argument. Got `{v}` instead").as_str())
            )
        }
    })
}

pub fn abs(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "abs", params, args, 1)?;
    Ok(Value::from_float(
        ensure_numeric("abs", &params[0], &args[0])?.abs(),
    ))
}

pub fn ceil(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "ceil", params, args, 1)?;
    Ok(Value::from_float(
        ensure_numeric("ceil", &params[0], &args[0])?.ceil(),
    ))
}

pub fn floor(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "floor", params, args, 1)?;
    Ok(Value::from_float(
        ensure_numeric("floor", &params[0], &args[0])?.floor(),
    ))
}

pub fn range(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
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

pub fn round(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    ensure_args_count(span, "round", params, args, 1)?;
    Ok(Value::from_float(
        ensure_numeric("round", &params[0], &args[0])?.round(),
    ))
}

pub fn arithmetic_operation(
    op: &ArithOp,
    expr1: &Expr,
    expr2: &Expr,
    v1: Value,
    v2: Value,
) -> Result<Value> {
    if v1 == Value::Undefined || v2 == Value::Undefined {
        return Ok(Value::Undefined);
    }

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
        ArithOp::Mod => v1 % v2,
    }))
}
