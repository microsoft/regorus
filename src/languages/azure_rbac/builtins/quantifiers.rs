// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::vec;
use alloc::vec::Vec;

use crate::value::Value;

use super::evaluator::RbacBuiltinError;

// Cross-product operators over collections.
//
// The operators use value equality across elements. Non-collection values are
// treated as singleton collections.

pub(super) fn for_any_of_any_values(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    let left_values = collect_values(left);
    let right_values = collect_values(right);

    Ok(left_values
        .iter()
        .any(|left_value| right_values.contains(left_value)))
}

pub(super) fn for_all_of_any_values(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    let left_values = collect_values(left);
    let right_values = collect_values(right);

    Ok(left_values
        .iter()
        .all(|left_value| right_values.contains(left_value)))
}

pub(super) fn for_any_of_all_values(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    let left_values = collect_values(left);
    let right_values = collect_values(right);

    Ok(left_values.iter().any(|left_value| {
        right_values
            .iter()
            .all(|right_value| *left_value == *right_value)
    }))
}

pub(super) fn for_all_of_all_values(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    let left_values = collect_values(left);
    let right_values = collect_values(right);

    Ok(left_values.iter().all(|left_value| {
        right_values
            .iter()
            .all(|right_value| *left_value == *right_value)
    }))
}

fn collect_values(value: &Value) -> Vec<&Value> {
    match *value {
        Value::Array(ref list) => list.iter().collect(),
        Value::Set(ref set) => set.iter().collect(),
        _ => vec![value],
    }
}
