// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Shared helpers: type coercion, comparison, pattern matching, and path resolution.

#![deny(
    clippy::arithmetic_side_effects,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::panic,
    clippy::shadow_unrelated,
    clippy::unwrap_used,
    clippy::missing_const_for_fn,
    clippy::option_if_let_else,
    clippy::semicolon_if_nothing_returned,
    clippy::useless_let_if_seq
)]

use crate::languages::azure_policy::strings;
use crate::value::Value;

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

// ── Type helpers ──────────────────────────────────────────────────────

pub const fn is_true(value: &Value) -> bool {
    matches!(value, Value::Bool(true))
}

pub const fn is_undefined(value: &Value) -> bool {
    matches!(value, Value::Undefined)
}

pub fn as_string(value: &Value) -> Option<String> {
    match *value {
        Value::String(ref s) => Some(s.to_string()),
        _ => None,
    }
}

/// Borrow the inner string of a `Value::String` without cloning.
pub fn as_str(value: &Value) -> Option<&str> {
    match *value {
        Value::String(ref s) => Some(s),
        _ => None,
    }
}

/// Try to parse a string as a number for Azure Policy type coercion.
pub fn try_coerce_to_number(s: &str) -> Option<crate::number::Number> {
    use core::str::FromStr as _;
    // Try integer first, then float.
    i64::from_str(s.trim())
        .map(crate::number::Number::from)
        .ok()
        .or_else(|| {
            f64::from_str(s.trim())
                .map(crate::number::Number::from)
                .ok()
        })
}

// ── Path resolution ───────────────────────────────────────────────────

pub fn resolve_path(root: &Value, path: &str) -> Value {
    let segments = tokenize_path(path);
    let mut current = root.clone();

    for segment in segments {
        #[allow(clippy::pattern_type_mismatch)]
        match &current {
            Value::Object(map) => {
                let mut next = None;
                for (key, value) in map.iter() {
                    if let Value::String(ref key_str) = *key {
                        if strings::keys::eq(key_str, &segment) {
                            next = Some(value.clone());
                            break;
                        }
                    }
                }

                if let Some(value) = next {
                    current = value;
                } else {
                    return Value::Undefined;
                }
            }
            Value::Array(items) => {
                let Ok(index) = segment.parse::<usize>() else {
                    return Value::Undefined;
                };

                let Some(value) = items.get(index) else {
                    return Value::Undefined;
                };
                current = value.clone();
            }
            _ => return Value::Undefined,
        }
    }

    current
}

fn tokenize_path(path: &str) -> Vec<String> {
    let mut segments = Vec::new();
    let mut token = String::new();
    let mut bracket = String::new();
    let mut in_bracket = false;

    for ch in path.chars() {
        match ch {
            '.' if !in_bracket => {
                if !token.is_empty() {
                    segments.push(token.clone());
                    token.clear();
                }
            }
            '[' => {
                in_bracket = true;
                if !token.is_empty() {
                    segments.push(token.clone());
                    token.clear();
                }
            }
            ']' => {
                in_bracket = false;
                let cleaned = bracket.trim_matches('"').trim_matches('\'').to_string();
                if !cleaned.is_empty() {
                    segments.push(cleaned);
                }
                bracket.clear();
            }
            _ => {
                if in_bracket {
                    bracket.push(ch);
                } else {
                    token.push(ch);
                }
            }
        }
    }

    if !token.is_empty() {
        segments.push(token);
    }

    segments
}
