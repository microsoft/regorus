// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! ARM template function builtins for Azure Policy expressions.
//!
//! Implements: split, empty, first, last, startsWith,
//! endsWith, int, string, bool, padLeft, ipRangeContains.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::languages::azure_policy::strings::case_fold;
use crate::lexer::Span;
use crate::value::Value;

use alloc::string::{String, ToString as _};
use anyhow::Result;
use core::net::IpAddr;
use ipnet::IpNet;

use super::helpers::{as_str, try_coerce_to_number};

/// Truncate `f64` to `i64` (saturating semantics since Rust 1.45).
///
/// The standard library provides no `TryFrom<f64>` for `i64`, so a raw `as`
/// cast is the only option.  Wrapping it in a named function keeps the rest
/// of the module free of `clippy::as_conversions` warnings.
#[expect(clippy::as_conversions, reason = "no TryFrom<f64> for i64 in std")]
const fn truncate_f64_to_i64(f: f64) -> i64 {
    f as i64
}

pub(super) fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("azure.policy.fn.split", (fn_split, 2));
    m.insert("azure.policy.fn.empty", (fn_empty, 1));
    m.insert("azure.policy.fn.first", (fn_first, 1));
    m.insert("azure.policy.fn.last", (fn_last, 1));
    m.insert("azure.policy.fn.starts_with", (fn_starts_with, 2));
    m.insert("azure.policy.fn.ends_with", (fn_ends_with, 2));
    m.insert("azure.policy.fn.int", (fn_int, 1));
    m.insert("azure.policy.fn.string", (fn_string, 1));
    m.insert("azure.policy.fn.bool", (fn_bool, 1));
    m.insert("azure.policy.fn.pad_left", (fn_pad_left, 3));
    m.insert(
        "azure.policy.fn.ip_range_contains",
        (fn_ip_range_contains, 2),
    );
}

/// `split(inputString, delimiter)` → array of strings.
fn fn_split(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [input_val, delim_val] = args
    else {
        return Ok(Value::Undefined);
    };

    let Some(input) = as_str(input_val) else {
        return Ok(Value::Undefined);
    };

    // The delimiter argument can be a single string or an array of strings.
    // When an array is provided, the input is split on ANY of the delimiters.
    match *delim_val {
        Value::String(ref delimiter) => {
            let parts: alloc::vec::Vec<Value> = input
                .split(delimiter.as_ref())
                .map(|s| Value::from(s.to_string()))
                .collect();
            Ok(Value::from(parts))
        }
        Value::Array(ref delimiters) => {
            // Collect all string delimiters from the array.
            let delims: alloc::vec::Vec<&str> = delimiters
                .iter()
                .filter_map(|v| match *v {
                    Value::String(ref s) => Some(s.as_ref()),
                    _ => None,
                })
                .collect();
            if delims.is_empty() {
                // No valid delimiters — return input as single-element array.
                return Ok(Value::from(alloc::vec![Value::from(input)]));
            }
            // Scan the input and split on any matching delimiter.
            // At each position, try delimiters longest-first to avoid
            // substring-overlap issues.
            let mut sorted_delims = delims.clone();
            sorted_delims.sort_by_key(|d| core::cmp::Reverse(d.len()));

            let mut parts = alloc::vec::Vec::new();
            let mut current = String::new();
            let bytes = input.as_bytes();
            let mut i = 0;
            while i < bytes.len() {
                let mut matched = false;
                for &d in &sorted_delims {
                    if !d.is_empty() && bytes.get(i..).is_some_and(|b| b.starts_with(d.as_bytes())) {
                        parts.push(Value::from(core::mem::take(&mut current)));
                        i = i.wrapping_add(d.len());
                        matched = true;
                        break;
                    }
                }
                if !matched {
                    // Safe: we iterate byte-by-byte only when no delimiter matched.
                    // For correctness with multi-byte UTF-8, advance one char.
                    if let Some(ch) = input.get(i..).and_then(|s| s.chars().next()) {
                        current.push(ch);
                        i = i.wrapping_add(ch.len_utf8());
                    } else {
                        i = i.wrapping_add(1);
                    }
                }
            }
            parts.push(Value::from(current));
            Ok(Value::from(parts))
        }
        _ => Ok(Value::Undefined),
    }
}

/// `empty(item)` → true if string/array/object is empty or value is null/undefined.
fn fn_empty(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(arg) = args.first() else {
        return Ok(Value::Bool(true));
    };
    let result = match *arg {
        Value::String(ref s) => s.is_empty(),
        Value::Array(ref a) => a.is_empty(),
        Value::Object(ref o) => o.is_empty(),
        Value::Null | Value::Undefined => true,
        _ => false,
    };
    Ok(Value::Bool(result))
}

/// `first(arg)` → first element of array or first character of string.
///
/// Azure semantics: first of an empty string returns empty string,
/// first of an empty array returns null.
fn fn_first(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(arg) = args.first() else {
        return Ok(Value::Undefined);
    };
    match *arg {
        Value::Array(ref a) => Ok(a.first().cloned().unwrap_or(Value::Null)),
        Value::String(ref s) => Ok(s
            .chars()
            .next()
            .map_or_else(|| Value::from(""), |ch| Value::from(ch.to_string()))),
        _ => Ok(Value::Undefined),
    }
}

/// `last(arg)` → last element of array or last character of string.
///
/// Azure semantics: last of an empty string returns empty string,
/// last of an empty array returns null.
fn fn_last(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(arg) = args.first() else {
        return Ok(Value::Undefined);
    };
    match *arg {
        Value::Array(ref a) => Ok(a.last().cloned().unwrap_or(Value::Null)),
        Value::String(ref s) => Ok(s
            .chars()
            .last()
            .map_or_else(|| Value::from(""), |ch| Value::from(ch.to_string()))),
        _ => Ok(Value::Undefined),
    }
}

/// `startsWith(stringToSearch, stringToFind)` → bool (case-insensitive).
///
/// Uses full Unicode case folding via ICU4X.
fn fn_starts_with(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [hay_val, needle_val] = args
    else {
        return Ok(Value::Bool(false));
    };
    let (Some(haystack), Some(needle)) = (as_str(hay_val), as_str(needle_val)) else {
        return Ok(Value::Bool(false));
    };
    let fh = case_fold::fold(haystack);
    let fn_ = case_fold::fold(needle);
    Ok(Value::Bool(fh.starts_with(&*fn_)))
}

/// `endsWith(stringToSearch, stringToFind)` → bool (case-insensitive).
///
/// Uses full Unicode case folding via ICU4X.
fn fn_ends_with(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [hay_val, needle_val] = args
    else {
        return Ok(Value::Bool(false));
    };
    let (Some(haystack), Some(needle)) = (as_str(hay_val), as_str(needle_val)) else {
        return Ok(Value::Bool(false));
    };
    let fh = case_fold::fold(haystack);
    let fn_ = case_fold::fold(needle);
    Ok(Value::Bool(fh.ends_with(&*fn_)))
}

/// `int(valueToConvert)` → integer number.
fn fn_int(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(arg) = args.first() else {
        return Ok(Value::Undefined);
    };
    match *arg {
        Value::Number(ref n) => {
            // Truncate to integer.
            n.as_i64()
                .map(Value::from)
                .or_else(|| n.as_f64().map(|f| Value::from(truncate_f64_to_i64(f))))
                .map_or(Ok(Value::Undefined), Ok)
        }
        Value::String(ref s) => try_coerce_to_number(s).map_or(Ok(Value::Undefined), |n| {
            n.as_i64()
                .map(Value::from)
                .or_else(|| n.as_f64().map(|f| Value::from(truncate_f64_to_i64(f))))
                .map_or(Ok(Value::Undefined), Ok)
        }),
        _ => Ok(Value::Undefined),
    }
}

/// `string(valueToConvert)` → string representation.
fn fn_string(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(arg) = args.first() else {
        return Ok(Value::Undefined);
    };
    match *arg {
        Value::String(_) => Ok(arg.clone()),
        Value::Bool(b) => Ok(Value::from(b.to_string())),
        Value::Number(ref n) => Ok(Value::from(n.format_decimal())),
        Value::Null => Ok(Value::from("null")),
        Value::Undefined => Ok(Value::Undefined),
        // For arrays and objects, produce JSON-style representation.
        _ => Ok(Value::from(arg.to_string())),
    }
}

/// `bool(value)` → boolean.
fn fn_bool(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(arg) = args.first() else {
        return Ok(Value::Undefined);
    };
    match *arg {
        Value::Bool(_) => Ok(arg.clone()),
        Value::String(ref s) => match s.to_lowercase().as_str() {
            "true" | "1" => Ok(Value::Bool(true)),
            "false" | "0" => Ok(Value::Bool(false)),
            _ => Ok(Value::Undefined),
        },
        Value::Number(ref n) => n
            .as_i64()
            .map(|i| Value::Bool(i != 0))
            .or_else(|| n.as_f64().map(|f| Value::Bool(f != 0.0)))
            .map_or(Ok(Value::Undefined), Ok),
        _ => Ok(Value::Undefined),
    }
}

/// `padLeft(value, totalWidth, padChar)` → left-padded string.
fn fn_pad_left(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    if args.len() < 2 || args.len() > 3 {
        return Ok(Value::Undefined);
    }

    let Some(value) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };

    let width = args.get(1).and_then(|width_val| match *width_val {
        Value::Number(ref n) => n
            .as_i64()
            .and_then(|x| usize::try_from(x).ok())
            .or_else(|| {
                n.as_f64()
                    .and_then(|x| usize::try_from(truncate_f64_to_i64(x)).ok())
            }),
        Value::String(ref s) => try_coerce_to_number(s).and_then(|n| {
            n.as_i64()
                .and_then(|x| usize::try_from(x).ok())
                .or_else(|| {
                    n.as_f64()
                        .and_then(|x| usize::try_from(truncate_f64_to_i64(x)).ok())
                })
        }),
        _ => None,
    });

    let Some(total_width) = width else {
        return Ok(Value::Undefined);
    };

    let pad_char = args
        .get(2)
        .and_then(as_str)
        .and_then(|s| s.chars().next())
        .unwrap_or(' ');

    let value_len = value.chars().count();
    if value_len >= total_width {
        return Ok(Value::from(value));
    }

    let pad_count = total_width.saturating_sub(value_len);
    let mut padded = String::with_capacity(total_width);
    for _ in 0..pad_count {
        padded.push(pad_char);
    }
    padded.push_str(value);

    Ok(Value::from(padded))
}

/// `ipRangeContains(range, targetRange)` → bool.
fn fn_ip_range_contains(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [range_val, target_val] = args
    else {
        return Ok(Value::Bool(false));
    };
    let (Some(range), Some(target)) = (as_str(range_val), as_str(target_val)) else {
        return Ok(Value::Bool(false));
    };

    let Ok(net) = range.parse::<IpNet>() else {
        return Ok(Value::Bool(false));
    };

    if target.contains('/') {
        let Ok(target_net) = target.parse::<IpNet>() else {
            return Ok(Value::Bool(false));
        };
        return Ok(Value::Bool(net.contains(&target_net)));
    }

    let Ok(target_ip) = target.parse::<IpAddr>() else {
        return Ok(Value::Bool(false));
    };
    Ok(Value::Bool(net.contains(&target_ip)))
}
