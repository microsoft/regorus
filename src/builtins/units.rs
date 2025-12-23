// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::unused_trait_names)]
use alloc::borrow::Cow;
use core::str::FromStr;

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

    // Canonicalize quirky literals (e.g. ".5", "-.1") so downstream parsing always sees
    // a stable representation that includes an explicit leading digit.
    let canonical_part = canonicalize_number_part(number_part);

    if let Some(e) = ten_exp(suffix) {
        let combined = combine_decimal_exponent(canonical_part.as_ref(), e)
            .ok_or_else(|| params[0].span().error("could not parse number"))?;
        let number = Number::from_str(&combined)
            .map_err(|_| params[0].span().error("could not parse number"))?;
        Ok(Value::from(number))
    } else if let Some(e) = two_exp(suffix) {
        let mut number = Number::from_str(canonical_part.as_ref())
            .map_err(|_| params[0].span().error("could not parse number"))?;
        number.mul_assign(&Number::two_pow(e)?)?;
        Ok(Value::from(number))
    } else {
        Ok(Value::Undefined)
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

    // Canonicalize quirky literals (e.g. ".5", "-.1") so downstream parsing always sees
    // a stable representation that includes an explicit leading digit.
    let canonical_part = canonicalize_number_part(number_part);

    if let Some(e) = twob_exp(suffix) {
        let mut number = match Number::from_str(canonical_part.as_ref()) {
            Ok(n) => n,
            Err(_) if strict => bail!(span.error("could not parse number")),
            Err(_) => return Ok(Value::Undefined),
        };
        number.mul_assign(&Number::two_pow(e)?)?;
        Ok(Value::from(number.round()))
    } else if let Some(e) = tenb_exp(suffix) {
        let combined = match combine_decimal_exponent(canonical_part.as_ref(), e) {
            Some(s) => s,
            None if strict => bail!(span.error("could not parse number")),
            None => return Ok(Value::Undefined),
        };
        let number = match Number::from_str(&combined) {
            Ok(n) => n,
            Err(_) if strict => bail!(span.error("could not parse number")),
            Err(_) => return Ok(Value::Undefined),
        };
        Ok(Value::from(number.round()))
    } else {
        Ok(Value::Undefined)
    }
}

// Normalizes numbers that start with a decimal point by injecting the implicit leading zero.
// This means inputs like ".5" and "-.1" become "0.5" / "-0.1", which Number::from_str accepts.
fn canonicalize_number_part(number_part: &str) -> Cow<'_, str> {
    if let Some(rest) = number_part.strip_prefix("-.") {
        Cow::Owned(format!("-0.{rest}"))
    } else if let Some(rest) = number_part.strip_prefix("+.") {
        Cow::Owned(format!("+0.{rest}"))
    } else if let Some(rest) = number_part.strip_prefix('.') {
        Cow::Owned(format!("0.{rest}"))
    } else {
        Cow::Borrowed(number_part)
    }
}

// Adds the unit-derived exponent (from suffix) to any exponent already present in the literal.
// Produces a canonical `mantissa eX` string or returns None when the combined exponent overflows.
fn combine_decimal_exponent(number: &str, suffix_exp: i32) -> Option<String> {
    if suffix_exp == 0 {
        return Some(number.to_string());
    }

    let (mantissa, base_exp) = match split_decimal_exponent(number) {
        Some(parts) => parts,
        None => (number, 0),
    };

    if mantissa.is_empty() {
        return None;
    }

    let combined_exp = base_exp.checked_add(suffix_exp)?;

    if combined_exp == 0 {
        Some(mantissa.to_string())
    } else {
        Some(format!("{}e{}", mantissa, combined_exp))
    }
}

// Splits scientific notation ("1.2e3") into mantissa/exponent so callers can adjust the exponent.
// Returns None when no exponent exists or the tail cannot be parsed into a 32-bit integer.
fn split_decimal_exponent(number: &str) -> Option<(&str, i32)> {
    let idx = number.find(['e', 'E'])?;
    let mantissa = &number[..idx];
    let exp_part = &number[idx + 1..];
    if exp_part.is_empty() {
        return None;
    }
    let exponent = exp_part.parse::<i32>().ok()?;
    Some((mantissa, exponent))
}
