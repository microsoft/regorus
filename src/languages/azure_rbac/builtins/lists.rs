// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::collections::BTreeSet;

use crate::value::Value;

use super::evaluator::RbacBuiltinError;

// Check whether a list or set contains the provided element(s).
pub(super) fn list_contains(left: &Value, right: &Value) -> Result<bool, RbacBuiltinError> {
    match *left {
        // Lists and sets share containment semantics.
        Value::Array(ref list) => Ok(list_contains_values(list, right)),
        Value::Set(ref set) => Ok(set_contains_values(set, right)),
        _ => Ok(false),
    }
}

// For lists, treat a list/set needle as "all elements are contained".
fn list_contains_values(list: &[Value], needle: &Value) -> bool {
    match *needle {
        // For collection needles, require all elements to be present.
        Value::Array(ref right_list) => right_list.iter().all(|item| list.contains(item)),
        Value::Set(ref right_set) => right_set.iter().all(|item| list.contains(item)),
        _ => list.contains(needle),
    }
}

// For sets, treat a list/set needle as "all elements are contained".
fn set_contains_values(set: &BTreeSet<Value>, needle: &Value) -> bool {
    match *needle {
        // For collection needles, require all elements to be present.
        Value::Array(ref right_list) => right_list.iter().all(|item| set.contains(item)),
        Value::Set(ref right_set) => right_set.iter().all(|item| set.contains(item)),
        _ => set.contains(needle),
    }
}
