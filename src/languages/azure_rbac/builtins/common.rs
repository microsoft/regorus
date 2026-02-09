// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;
use alloc::format;
use alloc::string::ToString as _;

use super::evaluator::RbacBuiltinError;

// Ensure the value is a string and return a borrowed &str.
pub(super) fn ensure_string<'a>(
    value: &'a Value,
    name: &'static str,
) -> Result<&'a str, RbacBuiltinError> {
    match *value {
        // Borrow string contents without allocation.
        Value::String(ref s) => Ok(s.as_ref()),
        _ => Err(RbacBuiltinError::new(format!(
            "{} expects string arguments",
            name
        ))),
    }
}

// Extract a boolean value or return a typed builtin error.
pub(super) fn value_as_bool(value: &Value, name: &'static str) -> Result<bool, RbacBuiltinError> {
    match *value {
        Value::Bool(b) => Ok(b),
        _ => Err(RbacBuiltinError::new(format!(
            "{} expects boolean arguments",
            name
        ))),
    }
}

// Convert a value into a string for builtin comparisons.
// Accepts string values or numbers formatted as decimal text.
pub(super) fn value_as_string(
    value: &Value,
    name: &'static str,
) -> Result<alloc::string::String, RbacBuiltinError> {
    match *value {
        // Preserve strings verbatim and render numbers as decimals.
        Value::String(ref s) => Ok(s.as_ref().to_string()),
        Value::Number(ref n) => Ok(n.format_decimal()),
        _ => Err(RbacBuiltinError::new(format!(
            "{} expects string arguments",
            name
        ))),
    }
}

// Parse a value into an i64 for integer-based operations.
// Accepts integral numeric values or numeric strings.
pub(super) fn value_as_i64(value: &Value, name: &'static str) -> Result<i64, RbacBuiltinError> {
    match *value {
        // Accept only integral values for numeric builtins.
        Value::Number(ref n) => n
            .as_i64()
            .ok_or_else(|| RbacBuiltinError::new(format!("{} expects numeric arguments", name))),
        Value::String(ref s) => s
            .parse::<i64>()
            .map_err(|_| RbacBuiltinError::new(format!("{} expects numeric arguments", name))),
        _ => Err(RbacBuiltinError::new(format!(
            "{} expects numeric arguments",
            name
        ))),
    }
}

// Parse a two-element array or set into numeric bounds (start, end).
pub(super) fn range_bounds(
    value: &Value,
    name: &'static str,
) -> Result<(i64, i64), RbacBuiltinError> {
    match *value {
        Value::Array(ref list) => {
            // Require exactly two elements for range bounds.
            let mut iter = list.iter();
            let start = iter.next().ok_or_else(|| {
                RbacBuiltinError::new(format!("{} expects a 2-element list or set", name))
            })?;
            let end = iter.next().ok_or_else(|| {
                RbacBuiltinError::new(format!("{} expects a 2-element list or set", name))
            })?;
            if iter.next().is_some() {
                return Err(RbacBuiltinError::new(format!(
                    "{} expects a 2-element list or set",
                    name
                )));
            }
            Ok((value_as_i64(start, name)?, value_as_i64(end, name)?))
        }
        Value::Set(ref set) => {
            // Sets must contain exactly two elements (order is arbitrary).
            let mut iter = set.iter();
            let start = iter.next().ok_or_else(|| {
                RbacBuiltinError::new(format!("{} expects a 2-element list or set", name))
            })?;
            let end = iter.next().ok_or_else(|| {
                RbacBuiltinError::new(format!("{} expects a 2-element list or set", name))
            })?;
            if iter.next().is_some() {
                return Err(RbacBuiltinError::new(format!(
                    "{} expects a 2-element list or set",
                    name
                )));
            }
            Ok((value_as_i64(start, name)?, value_as_i64(end, name)?))
        }
        _ => Err(RbacBuiltinError::new(format!(
            "{} expects a 2-element list or set",
            name
        ))),
    }
}

// Parse HH:MM[:SS] into seconds since midnight.
pub(super) fn parse_time_of_day(value: &str) -> Result<u32, RbacBuiltinError> {
    // Parse HH:MM[:SS] into numeric components.
    let mut iter = value.split(':');
    let hours_str = iter
        .next()
        .ok_or_else(|| RbacBuiltinError::new("Invalid time format, expected HH:MM or HH:MM:SS"))?;
    let minutes_str = iter
        .next()
        .ok_or_else(|| RbacBuiltinError::new("Invalid time format, expected HH:MM or HH:MM:SS"))?;
    let seconds_str = iter.next();
    if iter.next().is_some() {
        return Err(RbacBuiltinError::new(
            "Invalid time format, expected HH:MM or HH:MM:SS",
        ));
    }

    let hours = hours_str
        .parse::<u32>()
        .map_err(|_| RbacBuiltinError::new("Invalid hour value"))?;
    let minutes = minutes_str
        .parse::<u32>()
        .map_err(|_| RbacBuiltinError::new("Invalid minute value"))?;
    let seconds = match seconds_str {
        Some(segment) => segment
            .parse::<u32>()
            .map_err(|_| RbacBuiltinError::new("Invalid second value"))?,
        None => 0,
    };

    if hours > 23 || minutes > 59 || seconds > 59 {
        return Err(RbacBuiltinError::new("Time value out of range"));
    }

    // Convert to seconds since midnight with overflow checks.
    let total = hours
        .checked_mul(3600)
        .and_then(|total| total.checked_add(minutes.checked_mul(60)?))
        .and_then(|total| total.checked_add(seconds))
        .ok_or_else(|| RbacBuiltinError::new("Time value out of range"))?;
    Ok(total)
}

// Match a value against a simple '*' wildcard pattern.
pub(super) fn simple_wildcard_match(pattern: &str, value: &str) -> bool {
    // Recursive matcher supporting '*' as multi-character wildcard.
    fn helper(pattern: &[u8], value: &[u8]) -> bool {
        match pattern.split_first() {
            None => value.is_empty(),
            Some((&b'*', rest)) => {
                if helper(rest, value) {
                    return true;
                }
                match value.split_first() {
                    None => false,
                    Some((_first, rest_value)) => helper(pattern, rest_value),
                }
            }
            Some((byte, rest)) => match value.split_first() {
                Some((value_byte, rest_value)) if *byte == *value_byte => helper(rest, rest_value),
                _ => false,
            },
        }
    }

    helper(pattern.as_bytes(), value.as_bytes())
}

// Return true if the value is an array or set.
pub(super) const fn is_collection(value: &Value) -> bool {
    matches!(value, Value::Array(_) | Value::Set(_))
}

// Check membership in an array or set.
pub(super) fn collection_contains(collection: &Value, needle: &Value) -> bool {
    match *collection {
        Value::Array(ref list) => list.contains(needle),
        Value::Set(ref set) => set.contains(needle),
        _ => false,
    }
}

// Case-insensitive membership check for string elements in arrays or sets.
pub(super) fn collection_contains_case_insensitive(collection: &Value, needle: &Value) -> bool {
    let needle_str = match *needle {
        Value::String(ref s) => s.to_ascii_lowercase(),
        _ => return false,
    };

    match *collection {
        Value::Array(ref list) => list.iter().any(|value| match *value {
            Value::String(ref s) => s.to_ascii_lowercase() == needle_str,
            _ => false,
        }),
        Value::Set(ref set) => set.iter().any(|value| match *value {
            Value::String(ref s) => s.to_ascii_lowercase() == needle_str,
            _ => false,
        }),
        _ => false,
    }
}
