// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;

use super::common;
use super::evaluator::RbacBuiltinError;

// Compare numeric values using integer semantics.
// Accepts numeric values or numeric strings that fit in i64.
// Spec: https://learn.microsoft.com/en-us/azure/role-based-access-control/conditions-format#numeric-comparison-operators
pub(super) fn numeric_compare(
    left: &Value,
    right: &Value,
    op: &str,
    name: &'static str,
) -> Result<bool, RbacBuiltinError> {
    // Convert both operands to i64 before comparing.
    let lhs = common::value_as_i64(left, name)?;
    let rhs = common::value_as_i64(right, name)?;
    Ok(match op {
        "==" => lhs == rhs,
        "!=" => lhs != rhs,
        "<" => lhs < rhs,
        "<=" => lhs <= rhs,
        ">" => lhs > rhs,
        ">=" => lhs >= rhs,
        _ => false,
    })
}

// Check whether a numeric value falls within a 2-element range (inclusive).
// Bounds are parsed as i64; values must fit in i64.
// Spec: https://learn.microsoft.com/en-us/azure/role-based-access-control/conditions-format#numeric-comparison-operators
pub(super) fn numeric_in_range(
    left: &Value,
    right: &Value,
    name: &'static str,
) -> Result<bool, RbacBuiltinError> {
    // Parse value and inclusive bounds as i64.
    let value = common::value_as_i64(left, name)?;
    let (start, end) = common::range_bounds(right, name)?;
    Ok(value >= start && value <= end)
}
