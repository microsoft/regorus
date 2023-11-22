// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::{Float, Number, Value};

use std::collections::HashMap;

use anyhow::{bail, Context, Result};
use ordered_float::OrderedFloat;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("units.parse", (parse, 1));
    m.insert("units.parse_bytes", (parse_bytes, 1));
}

fn parse(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "units.parse";
    ensure_args_count(span, name, params, args, 1)?;
    let string = ensure_string(name, &params[0], &args[0])?;
    let string = string.as_str();

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

    let (number_part, suffix) = match string.find(|c: char| c.is_alphabetic()) {
        Some(p) => (&string[0..p], &string[p..]),
        _ => (string, ""),
    };

    let n: Float = if number_part.starts_with('.') {
        serde_json::from_str(format!("0{number_part}").as_str())
    } else {
        serde_json::from_str(number_part)
    }
    .with_context(|| span.error("could not parse number"))?;

    Ok(Value::Number(Number(OrderedFloat(
        n * 10f64.powf(match suffix {
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
            _ => {
                return Ok(Value::Number(Number(OrderedFloat(
                    n * 2f64.powf(match suffix.to_ascii_lowercase().as_str() {
                        "ki" => 10,
                        "mi" => 20,
                        "gi" => 30,
                        "ti" => 40,
                        "pi" => 50,
                        "ei" => 60,
                        "zi" => 70,
                        "yi" => 80,
                        _ => return Ok(Value::Undefined),
                    } as f64),
                ))));
            }
        } as f64),
    ))))
}

fn parse_bytes(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "units.parse_bytes";
    ensure_args_count(span, name, params, args, 1)?;
    let string = ensure_string(name, &params[0], &args[0])?;
    let string = string.as_str();

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

    let (number_part, suffix) = match string.find(|c: char| c.is_alphabetic()) {
        Some(p) => (&string[0..p], &string[p..]),
        _ => (string, ""),
    };

    let n: Float = if number_part.starts_with('.') {
        serde_json::from_str(format!("0{number_part}").as_str())
    } else {
        serde_json::from_str(number_part)
    }
    .with_context(|| span.error("could not parse number"))?;

    Ok(Value::Number(Number(OrderedFloat(f64::round(
        n * 2f64.powf(match suffix.to_ascii_lowercase().as_str() {
            "yi" | "yib" => 80,
            "zi" | "zib" => 70,
            "ei" | "eib" => 60,
            "pi" | "pib" => 50,
            "ti" | "tib" => 40,
            "gi" | "gib" => 30,
            "mi" | "mib" => 20,
            "ki" | "kib" => 10,
            "" => 0,
            _ => {
                return Ok(Value::Number(Number(OrderedFloat(
                    n * 10f64.powf(match suffix.to_ascii_lowercase().as_str() {
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
                        _ => {
                            return Ok(Value::Undefined);
                        }
                    } as f64),
                ))))
            }
        } as f64),
    )))))
}
