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

/// Coerce a value to its string representation for policy comparison operators.
///
/// Azure Policy coerces numbers and booleans to strings when used with string
/// operators (`like`, `match`, `contains`, `matchInsensitively`).  This is
/// needed when, for example, a count result (always a number) is compared
/// using a string operator: `count(...) like 2`.
pub fn coerce_to_string(value: &Value) -> Option<String> {
    match *value {
        Value::String(ref s) => Some(s.to_string()),
        Value::Number(ref n) => Some(n.format_decimal()),
        Value::Bool(b) => Some(if b { "true" } else { "false" }.to_string()),
        _ => None,
    }
}

pub fn coerce_to_string_ci(value: &Value) -> Option<String> {
    coerce_to_string(value).map(|s| strings::case_fold::fold(&s).into_owned())
}

// ── Collection helpers ────────────────────────────────────────────────

/// Check if an array or set contains a null sentinel.
pub fn collection_has_null(v: &Value) -> bool {
    match *v {
        Value::Array(ref items) => items.iter().any(|i| matches!(i, Value::Null)),
        Value::Set(ref items) => items.iter().any(|i| matches!(i, Value::Null)),
        _ => false,
    }
}

/// Check if any non-null element in a collection case-insensitively equals `target`.
/// Scalar RHS is treated as a single-element collection.
pub fn collection_any_ci_eq_excluding_null(collection: &Value, target: &Value) -> bool {
    match *collection {
        Value::Array(ref items) => items
            .iter()
            .filter(|i| !matches!(i, Value::Null))
            .any(|i| case_insensitive_equals(i, target)),
        Value::Set(ref items) => items
            .iter()
            .filter(|i| !matches!(i, Value::Null))
            .any(|i| case_insensitive_equals(i, target)),
        _ => case_insensitive_equals(collection, target),
    }
}

pub fn as_boolish(value: &Value) -> Option<bool> {
    match *value {
        Value::Bool(b) => Some(b),
        Value::String(ref s) => {
            if s.eq_ignore_ascii_case("true") {
                Some(true)
            } else if s.eq_ignore_ascii_case("false") {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    }
}

// ── Comparison and coercion ───────────────────────────────────────────

pub fn compare_values(left: &Value, right: &Value) -> Option<i8> {
    if is_undefined(left) || is_undefined(right) {
        return None;
    }

    #[allow(clippy::pattern_type_mismatch)]
    match (left, right) {
        (Value::String(a), Value::String(b)) => Some(match strings::case_fold::cmp(a, b) {
            core::cmp::Ordering::Less => -1,
            core::cmp::Ordering::Equal => 0,
            core::cmp::Ordering::Greater => 1,
        }),
        (Value::Number(a), Value::Number(b)) => Some(if a < b {
            -1
        } else if a > b {
            1
        } else {
            0
        }),
        (Value::Bool(a), Value::Bool(b)) => Some(if a == b {
            0
        } else if !a && *b {
            -1
        } else {
            1
        }),
        // String ↔ Number coercion
        (Value::String(s), Value::Number(n)) => try_coerce_to_number(s).map(|sn| {
            if &sn < n {
                -1
            } else if &sn > n {
                1
            } else {
                0
            }
        }),
        (Value::Number(n), Value::String(s)) => try_coerce_to_number(s).map(|sn| {
            if n < &sn {
                -1
            } else if n > &sn {
                1
            } else {
                0
            }
        }),
        _ => None,
    }
}

pub fn case_insensitive_equals(left: &Value, right: &Value) -> bool {
    if is_undefined(left) || is_undefined(right) {
        return false;
    }

    // Azure Policy treats an explicit null field value as "" (empty string)
    // for comparison purposes.  Missing fields are Undefined and caught above.
    #[allow(clippy::pattern_type_mismatch)]
    match (left, right) {
        (Value::Null, Value::Null) => true,
        (Value::Null, Value::String(b)) => strings::case_fold::eq("", b),
        (Value::String(a), Value::Null) => strings::case_fold::eq(a, ""),
        (Value::String(a), Value::String(b)) => strings::case_fold::eq(a, b),
        // String ↔ Number coercion
        (Value::String(s), Value::Number(_)) | (Value::Number(_), Value::String(s)) => {
            try_coerce_to_number(s).is_some_and(|n| {
                let num_val = Value::Number(n);
                let other = if matches!(left, Value::String(_)) {
                    right
                } else {
                    left
                };
                &num_val == other
            })
        }
        // String ↔ Bool coercion ("true"/"false" ↔ true/false)
        (Value::String(_), Value::Bool(b)) | (Value::Bool(b), Value::String(_)) => {
            as_boolish(if matches!(left, Value::String(_)) {
                left
            } else {
                right
            }) == Some(*b)
        }
        _ => left == right,
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

// ── Pattern matching ──────────────────────────────────────────────────

pub fn match_pattern(input_val: &Value, pattern_val: &Value, insensitive: bool) -> bool {
    let Some(mut input) = coerce_to_string(input_val) else {
        return false;
    };
    let Some(mut pattern) = coerce_to_string(pattern_val) else {
        return false;
    };

    if insensitive {
        input = strings::case_fold::fold(&input).into_owned();
        pattern = strings::case_fold::fold(&pattern).into_owned();
    }

    match_question_hash_pattern(&input, &pattern)
}

pub fn match_like_pattern_ci(input: &str, pattern: &str) -> bool {
    wildcard_match(input, pattern)
}

fn next_char(s: &str, index: usize) -> Option<(char, usize)> {
    s.get(index..)?
        .chars()
        .next()
        .map(|ch| (ch, index.saturating_add(ch.len_utf8())))
}

fn wildcard_match(input: &str, pattern: &str) -> bool {
    let (mut ii, mut pi) = (0_usize, 0_usize);
    let mut star_pat: Option<usize> = None;
    let mut star_inp = 0_usize;

    while ii < input.len() {
        let pat = next_char(pattern, pi);
        let inp = next_char(input, ii);

        if let (Some((pc, next_pi)), Some((ic, next_ii))) = (pat, inp) {
            if pc == '?' || pc == ic {
                pi = next_pi;
                ii = next_ii;
                continue;
            }
        }

        if matches!(pat, Some(('*', _))) {
            star_pat = Some(pi);
            star_inp = ii;
            pi = pi.saturating_add('*'.len_utf8());
        } else if let Some(saved_pi) = star_pat {
            pi = saved_pi.saturating_add('*'.len_utf8());
            if let Some((_, next_ii)) = next_char(input, star_inp) {
                star_inp = next_ii;
                ii = star_inp;
            } else {
                return false;
            }
        } else {
            return false;
        }
    }

    while matches!(next_char(pattern, pi), Some(('*', _))) {
        pi = pi.saturating_add('*'.len_utf8());
    }

    pi == pattern.len()
}

pub fn match_question_hash_pattern(input: &str, pattern: &str) -> bool {
    let mut input_chars = input.chars();
    let mut pattern_chars = pattern.chars();

    loop {
        match (input_chars.next(), pattern_chars.next()) {
            (None, None) => return true,
            (Some(_), None) | (None, Some(_)) => return false,
            (Some(input_char), Some(pattern_char)) => {
                if pattern_char == '.' {
                    // '.' matches any single character (letter, digit, or special).
                } else if pattern_char == '#' {
                    if !input_char.is_ascii_digit() {
                        return false;
                    }
                } else if pattern_char == '?' {
                    if !input_char.is_ascii_alphabetic() {
                        return false;
                    }
                } else if input_char != pattern_char {
                    return false;
                }
            }
        }
    }
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
