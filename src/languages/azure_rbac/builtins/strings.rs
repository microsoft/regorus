// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;
use alloc::string::ToString as _;

use super::common;
use super::evaluator::RbacBuiltinError;

#[cfg(feature = "regex")]
use regex::Regex;

// Equality check with collection containment semantics.
// If exactly one operand is a collection, checks whether it contains the other.
pub(super) fn string_equals(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    // If one side is a collection, perform containment instead of equality.
    if common::is_collection(right) && !common::is_collection(left) {
        return Ok(common::collection_contains(right, left));
    }
    if common::is_collection(left) && !common::is_collection(right) {
        return Ok(common::collection_contains(left, right));
    }
    Ok(left == right)
}

// Case-insensitive equality with collection containment semantics.
// If exactly one operand is a collection, checks whether it contains the other.
pub(super) fn string_equals_ignore_case(
    left: &Value,
    right: &Value,
) -> Result<bool, RbacBuiltinError> {
    // If one side is a collection, perform case-insensitive containment.
    if common::is_collection(right) && !common::is_collection(left) {
        return Ok(common::collection_contains_case_insensitive(right, left));
    }
    if common::is_collection(left) && !common::is_collection(right) {
        return Ok(common::collection_contains_case_insensitive(left, right));
    }

    let left_str = common::value_as_string(left, "StringEqualsIgnoreCase")?;
    let right_str = common::value_as_string(right, "StringEqualsIgnoreCase")?;
    Ok(left_str.eq_ignore_ascii_case(&right_str))
}

// Match with '*' and '?' wildcards.
pub(super) fn string_like(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    // Use simple wildcard matching for '*' and '?'.
    let value = common::value_as_string(left, "StringLike")?;
    let pattern = common::value_as_string(right, "StringLike")?;
    Ok(common::simple_wildcard_match(&pattern, &value))
}

// Check if the left string starts with the right string.
pub(super) fn string_starts_with(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    // Compare prefix match.
    let value = common::value_as_string(left, "StringStartsWith")?;
    let prefix = common::value_as_string(right, "StringStartsWith")?;
    Ok(value.starts_with(&prefix))
}

// Check if the left string ends with the right string.
pub(super) fn string_ends_with(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    // Compare suffix match.
    let value = common::value_as_string(left, "StringEndsWith")?;
    let suffix = common::value_as_string(right, "StringEndsWith")?;
    Ok(value.ends_with(&suffix))
}

// Check if the left string contains the right string.
pub(super) fn string_contains(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    // Check substring containment.
    let value = common::value_as_string(left, "StringContains")?;
    let needle = common::value_as_string(right, "StringContains")?;
    Ok(value.contains(&needle))
}

// Match using regex when the regex feature is enabled; otherwise uses exact match.
pub(super) fn string_matches(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    // Parse the pattern and apply regex matching when enabled.
    let value = common::value_as_string(left, "StringMatches")?;
    let pattern = common::value_as_string(right, "StringMatches")?;

    #[cfg(feature = "regex")]
    {
        // Compile regex each time to match RBAC semantics.
        let regex = Regex::new(&pattern).map_err(|err| RbacBuiltinError::new(err.to_string()))?;
        Ok(regex.is_match(&value))
    }

    #[cfg(not(feature = "regex"))]
    {
        // Without regex support, fall back to exact match.
        Ok(value == pattern)
    }
}

// Case-insensitive GUID equality.
pub(super) fn guid_equals(
    left: &Value,
    right: &Value,
    name: &'static str,
) -> Result<bool, RbacBuiltinError> {
    // GUID comparisons are case-insensitive.
    let lhs = common::value_as_string(left, name)?;
    let rhs = common::value_as_string(right, name)?;
    Ok(lhs.eq_ignore_ascii_case(&rhs))
}
