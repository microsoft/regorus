// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;

use super::common;
use super::evaluator::RbacBuiltinError;

// Compare two boolean values for equality.
pub(super) fn bool_equals(
    left: &Value,
    right: &Value,
    name: &'static str,
) -> Result<bool, RbacBuiltinError> {
    // Convert both sides to booleans using shared validation.
    let lhs = common::value_as_bool(left, name)?;
    let rhs = common::value_as_bool(right, name)?;
    // Exact boolean equality.
    Ok(lhs == rhs)
}
