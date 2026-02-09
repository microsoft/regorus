// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;

use super::common;
use super::evaluator::RbacBuiltinError;

// Compare times of day using HH:MM[:SS] semantics.
pub(super) fn time_compare(
    left: &Value,
    right: &Value,
    op: &str,
    name: &'static str,
) -> Result<bool, RbacBuiltinError> {
    // Parse both operands as time-of-day strings and compare in seconds.
    let lhs = common::value_as_string(left, name)?;
    let rhs = common::value_as_string(right, name)?;
    let left_secs = common::parse_time_of_day(&lhs)?;
    let right_secs = common::parse_time_of_day(&rhs)?;
    Ok(match op {
        "==" => left_secs == right_secs,
        "<" => left_secs < right_secs,
        "<=" => left_secs <= right_secs,
        ">" => left_secs > right_secs,
        ">=" => left_secs >= right_secs,
        _ => false,
    })
}

// Check whether a time falls within a 2-element range (inclusive).
// If the right operand is not a 2-element list/set, falls back to equality.
// Examples:
// - TimeOfDayInRange("09:30", ["09:00", "10:00"]) => true
// - TimeOfDayInRange("23:30:00", {"22:00", "23:00"}) => false
// - TimeOfDayInRange("12:00", "12:00") => true
pub(super) fn time_in_range(
    left: &Value,
    right: &Value,
    name: &'static str,
) -> Result<bool, RbacBuiltinError> {
    // Parse the target time once to compare against range bounds.
    let value = common::value_as_string(left, name)?;
    let value_secs = common::parse_time_of_day(&value)?;

    match *right {
        Value::Array(ref list) => {
            // Arrays must contain exactly two bounds.
            let start = list.first().ok_or_else(|| {
                RbacBuiltinError::new("TimeOfDayInRange expects a 2-element array")
            })?;
            let end = list.get(1).ok_or_else(|| {
                RbacBuiltinError::new("TimeOfDayInRange expects a 2-element array")
            })?;
            if list.len() != 2 {
                return Err(RbacBuiltinError::new(
                    "TimeOfDayInRange expects a 2-element array",
                ));
            }
            // Compare inclusive bounds after parsing to seconds.
            let start = common::value_as_string(start, name)?;
            let end = common::value_as_string(end, name)?;
            let start_secs = common::parse_time_of_day(&start)?;
            let end_secs = common::parse_time_of_day(&end)?;
            Ok(value_secs >= start_secs && value_secs <= end_secs)
        }
        Value::Set(ref set) => {
            // Sets must contain exactly two bounds (order is arbitrary).
            let mut iter = set.iter();
            let start = iter
                .next()
                .ok_or_else(|| RbacBuiltinError::new("TimeOfDayInRange expects 2 values"))?;
            let end = iter
                .next()
                .ok_or_else(|| RbacBuiltinError::new("TimeOfDayInRange expects 2 values"))?;
            let start_secs = common::parse_time_of_day(&common::value_as_string(start, name)?)?;
            let end_secs = common::parse_time_of_day(&common::value_as_string(end, name)?)?;
            Ok(value_secs >= start_secs && value_secs <= end_secs)
        }
        // Non-collection RHS falls back to equality.
        _ => time_compare(left, right, "==", name),
    }
}
