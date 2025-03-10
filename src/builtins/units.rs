// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::number::Number;
use crate::value::Value;
use crate::*;

use anyhow::{bail, Result};

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("units.parse", (parse, 1));
    m.insert("units.parse_bytes", (parse_bytes, 1));
}

fn ten_exp(suffix: &str) -> Option<i32> {
    Some(match suffix {
        "E" | "e" => 18,
        "P" | "p" => 15,
        "T" | "t" => 12,
        "G" | "g" => 9,
        "M" => 6,
        "K" | "k" => 3,
        "m" => -3,

        // The following are not supported by OPA
        "Q" => 30,
        "R" => 27,
        "Y" => 24,
        "Z" => 21,
        "h" => 2,
        "da" => 1,
        "d" => -1,
        "c" => -2,

        "μ" => -6,
        "n" => -9,
        "f" => -15,
        "a" => -18,
        "z" => -21,
        "y" => -24,
        "r" => -27,
        "q" => -30,

        // No suffix specified.
        "" => 0,
        _ => return None,
    })
}

fn two_exp(suffix: &str) -> Option<i32> {
    Some(match suffix.to_ascii_lowercase().as_str() {
        "ki" => 10,
        "mi" => 20,
        "gi" => 30,
        "ti" => 40,
        "pi" => 50,
        "ei" => 60,
        "zi" => 70,
        "yi" => 80,
        _ => return None,
    })
}

fn parse(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "units.parse";
    ensure_args_count(span, name, params, args, 1)?;
    let string = ensure_string(name, &params[0], &args[0])?;
    let string = string.as_ref();

    // Remove quotes.
    let string = if string.starts_with('"') && string.ends_with('"') && string.len() >= 2 {
        &string[1..string.len() - 1]
    } else {
        string
    };

    // Disallow whitespace.
    if string.chars().any(char::is_whitespace) {
        bail!(span.error("spaces not allowed in resource strings"));
    }

    let (number_part, suffix) = match string.rfind(|c: char| c.is_ascii_digit()) {
        Some(p) => (&string[0..p + 1], &string[p + 1..]),
        _ => (string, ""),
    };

    // Propagating the underlying error is not useful here.
    let v: Value = if number_part.starts_with('.') {
        serde_json::from_str(format!("0{number_part}").as_str())
    } else {
        serde_json::from_str(number_part)
    }
    .map_err(|_| params[0].span().error("could not parse number"))?;

    let mut n = match v {
        Value::Number(n) => n.clone(),
        _ => bail!(span.error("could not parse number")),
    };

    if let Some(e) = ten_exp(suffix) {
        n.mul_assign(&Number::ten_pow(e)?)?;
        Ok(Value::from(n))
    } else if let Some(e) = two_exp(suffix) {
        n.mul_assign(&Number::two_pow(e)?)?;
        Ok(Value::from(n))
    } else {
        return Ok(Value::Undefined);
    }
}

fn twob_exp(suffix: &str) -> Option<i32> {
    Some(match suffix.to_ascii_lowercase().as_str() {
        "yi" | "yib" => 80,
        "zi" | "zib" => 70,
        "ei" | "eib" => 60,
        "pi" | "pib" => 50,
        "ti" | "tib" => 40,
        "gi" | "gib" => 30,
        "mi" | "mib" => 20,
        "ki" | "kib" => 10,
        "" => 0,
        _ => return None,
    })
}

fn tenb_exp(suffix: &str) -> Option<i32> {
    Some(match suffix.to_ascii_lowercase().as_str() {
        "q" | "qb" => 30,
        "r" | "rb" => 27,
        "y" | "yb" => 24,
        "z" | "zb" => 21,
        "e" | "eb" => 18,
        "p" | "pb" => 15,
        "t" | "tb" => 12,
        "g" | "gb" => 9,
        "m" | "mb" => 6,
        "k" | "kb" => 3,
        _ => return None,
    })
}

fn parse_bytes(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "units.parse_bytes";
    ensure_args_count(span, name, params, args, 1)?;
    let string = ensure_string(name, &params[0], &args[0])?;
    let string = string.as_ref();

    // Remove quotes.
    let string = if string.starts_with('"') && string.ends_with('"') && string.len() >= 2 {
        &string[1..string.len() - 1]
    } else {
        string
    };

    // Disallow whitespace.
    if string.chars().any(char::is_whitespace) {
        bail!(span.error("spaces not allowed in resource strings"));
    }

    let (number_part, suffix) = match string.rfind(|c: char| c.is_ascii_digit()) {
        Some(p) => (&string[0..p + 1], &string[p + 1..]),
        _ => (string, ""),
    };

    let v: Value = match if number_part.starts_with('.') {
        serde_json::from_str(format!("0{number_part}").as_str())
    } else {
        serde_json::from_str(number_part)
    } {
        Ok(v) => v,
        Err(_) if strict => bail!(span.error("could not parse number")),
        _ => return Ok(Value::Undefined),
    };

    let mut n = match v {
        Value::Number(n) => n.clone(),
        _ => bail!(span.error("could not parse number")),
    };

    if let Some(e) = twob_exp(suffix) {
        n.mul_assign(&Number::two_pow(e)?)?;
        Ok(Value::from(n.round()))
    } else if let Some(e) = tenb_exp(suffix) {
        n.mul_assign(&Number::ten_pow(e)?)?;
        Ok(Value::from(n.round()))
    } else {
        Ok(Value::Undefined)
    }
}
