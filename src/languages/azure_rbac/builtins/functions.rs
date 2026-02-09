// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::collections::BTreeSet;
use alloc::string::ToString as _;
use alloc::vec;

use crate::value::Value;

use super::actions;
use super::common;
use super::evaluator::{RbacBuiltinContext, RbacBuiltinError};

#[cfg(feature = "time")]
use chrono::{DateTime, Duration};

pub(super) fn to_lower(value: &Value) -> Result<Value, RbacBuiltinError> {
    // Normalize to ASCII lowercase for RBAC string semantics.
    let text = common::ensure_string(value, "ToLower")?;
    Ok(Value::String(text.to_ascii_lowercase().into()))
}

pub(super) fn to_upper(value: &Value) -> Result<Value, RbacBuiltinError> {
    // Normalize to ASCII uppercase for RBAC string semantics.
    let text = common::ensure_string(value, "ToUpper")?;
    Ok(Value::String(text.to_ascii_uppercase().into()))
}

pub(super) fn trim(value: &Value) -> Result<Value, RbacBuiltinError> {
    // Remove leading/trailing whitespace.
    let text = common::ensure_string(value, "Trim")?;
    Ok(Value::String(text.trim().to_string().into()))
}

// Normalize to a set; useful for equality and membership checks.
// Examples:
// - NormalizeSet(["a", "b", "a"]) => {"a", "b"}
// - NormalizeSet("a") => {"a"}
pub(super) fn normalize_set(value: &Value) -> Result<Value, RbacBuiltinError> {
    match *value {
        // Already a set; return as-is.
        Value::Set(_) => Ok(value.clone()),
        Value::Array(ref list) => {
            // Convert arrays to sets by de-duplicating elements.
            let set: BTreeSet<Value> = list.iter().cloned().collect();
            Ok(Value::from(set))
        }
        _ => {
            // Non-collections become singleton sets.
            let mut set = BTreeSet::new();
            set.insert(value.clone());
            Ok(Value::from(set))
        }
    }
}

// Normalize to a list while preserving element values.
// Examples:
// - NormalizeList({"a", "b"}) => ["a", "b"] (order not guaranteed)
// - NormalizeList("a") => ["a"]
pub(super) fn normalize_list(value: &Value) -> Result<Value, RbacBuiltinError> {
    match *value {
        // Already a list.
        Value::Array(ref list) => Ok(Value::Array(list.clone())),
        Value::Set(ref set) => Ok(Value::from(
            set.iter().cloned().collect::<alloc::vec::Vec<_>>(),
        )),
        // Non-collections become singleton lists.
        _ => Ok(Value::from(vec![value.clone()])),
    }
}

// Add days to an RFC3339 timestamp string.
// Examples:
// - AddDays("2024-02-28T10:00:00Z", 1) => "2024-02-29T10:00:00Z"
// - AddDays("2023-12-31T23:00:00Z", 1) => "2024-01-01T23:00:00Z"
pub(super) fn add_days(date_value: &Value, days_value: &Value) -> Result<Value, RbacBuiltinError> {
    // Parse arguments as RFC3339 and integer day count.
    let date_str = common::ensure_string(date_value, "AddDays")?;
    let days = common::value_as_i64(days_value, "AddDays")?;

    #[cfg(feature = "time")]
    {
        // Apply a checked day offset to avoid overflow.
        let dt = DateTime::parse_from_rfc3339(date_str)
            .map_err(|err| RbacBuiltinError::new(err.to_string()))?;
        let updated = dt
            .checked_add_signed(Duration::days(days))
            .ok_or_else(|| RbacBuiltinError::new("AddDays overflow"))?;
        Ok(Value::String(updated.to_rfc3339().into()))
    }

    #[cfg(not(feature = "time"))]
    {
        // Feature-gated builtin; return a descriptive error.
        let _ = (date_str, days);
        Err(RbacBuiltinError::new(
            "AddDays builtin has not been enabled",
        ))
    }
}

// Coerce a string into a time literal (validated elsewhere).
// Example: ToTime("12:30:15") => "12:30:15"
pub(super) fn to_time(value: &Value) -> Result<Value, RbacBuiltinError> {
    match *value {
        // Time literals are represented as strings in the AST.
        Value::String(_) => Ok(value.clone()),
        _ => Err(RbacBuiltinError::new("ToTime expects a string")),
    }
}

// Match an action against a wildcard pattern.
// - With 1 argument, the action comes from the evaluation context.
// - Matching is segment-based (split on '/'); '*' matches a single segment and the
//   action and pattern must have the same number of segments.
// Examples:
// - ActionMatches("Microsoft.Storage/storageAccounts/read") => uses context action
// - ActionMatches("Microsoft.Storage/storageAccounts/read", "Microsoft.Storage/*/read") => true
// - ActionMatches("Microsoft.Storage/storageAccounts/read", "Microsoft.Storage/storageAccounts") => false
pub(super) fn action_matches(
    args: &[Value],
    ctx: &RbacBuiltinContext<'_>,
) -> Result<Value, RbacBuiltinError> {
    // Either use context action (1 arg) or explicit action (2 args).
    let (action, pattern) = match args.len() {
        1 => (
            ctx.evaluation
                .action
                .as_deref()
                .ok_or_else(|| RbacBuiltinError::new("Missing action in context"))?,
            common::ensure_string(
                args.first().ok_or_else(|| {
                    RbacBuiltinError::new("ActionMatches expects 1 or 2 arguments")
                })?,
                "ActionMatches",
            )?,
        ),
        2 => (
            common::ensure_string(
                args.first().ok_or_else(|| {
                    RbacBuiltinError::new("ActionMatches expects 1 or 2 arguments")
                })?,
                "ActionMatches",
            )?,
            common::ensure_string(
                args.get(1).ok_or_else(|| {
                    RbacBuiltinError::new("ActionMatches expects 1 or 2 arguments")
                })?,
                "ActionMatches",
            )?,
        ),
        _ => {
            return Err(RbacBuiltinError::new(
                "ActionMatches expects 1 or 2 arguments",
            ))
        }
    };

    Ok(Value::Bool(actions::action_matches_pattern(
        action, pattern,
    )))
}

// Match a suboperation against a pattern.
// - With 1 argument, the suboperation comes from the evaluation context.
// - Matching is exact; no wildcard semantics are supported.
// Examples:
// - SubOperationMatches("sub/read") => uses context suboperation
// - SubOperationMatches("sub/read", "sub/read") => true
// - SubOperationMatches("sub/read", "sub/*") => false
pub(super) fn suboperation_matches(
    args: &[Value],
    ctx: &RbacBuiltinContext<'_>,
) -> Result<Value, RbacBuiltinError> {
    // Either use context suboperation (1 arg) or explicit suboperation (2 args).
    let (subop, pattern) = match args.len() {
        1 => (
            ctx.evaluation
                .suboperation
                .as_deref()
                .ok_or_else(|| RbacBuiltinError::new("Missing suboperation in context"))?,
            common::ensure_string(
                args.first().ok_or_else(|| {
                    RbacBuiltinError::new("SubOperationMatches expects 1 or 2 arguments")
                })?,
                "SubOperationMatches",
            )?,
        ),
        2 => (
            common::ensure_string(
                args.first().ok_or_else(|| {
                    RbacBuiltinError::new("SubOperationMatches expects 1 or 2 arguments")
                })?,
                "SubOperationMatches",
            )?,
            common::ensure_string(
                args.get(1).ok_or_else(|| {
                    RbacBuiltinError::new("SubOperationMatches expects 1 or 2 arguments")
                })?,
                "SubOperationMatches",
            )?,
        ),
        _ => {
            return Err(RbacBuiltinError::new(
                "SubOperationMatches expects 1 or 2 arguments",
            ))
        }
    };

    Ok(Value::Bool(subop == pattern))
}
