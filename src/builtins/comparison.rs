// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::BoolOp;
use crate::value::Value;

use anyhow::Result;

/// compare two values
///
/// When comparing values of different kinds, the following order is honored.
/// That is, null is less than all other kinds of values. bool is greater than
/// null, but less than other kinds of values, and so on.
///
///   1. null
///   2. bool
///   3. number
///   4. string
///   5. Array
///   6. Object
///   7. Set
///
/// Scalar types like null, bool, number, string follow ordering same as what is seen in other languages when compared with values of the same kind.
///
/// When comparing arrays, each item from the first array is compared with the corresponding item from the second array. The ordering is determined by
// the ordering of the first non-equal items. In case all the compared items
/// are equal, the ordering is determined by comparing the length of the first array
/// with the length of the second array. The smaller array is 'Less' than the larger array.
///
/// Sets compare similar to arrays.
///
/// When comparing objects, each entry (key, value) from the first object is compared with the corresponding
/// entry from the second object. The ordering is determined by the ordering of the first non-equal entries. In case all the compared entries are equal,
/// the ordering is determined by comparing the length of the first object with the length of the second object. The smaller object is 'Less' then the larger object.
///
/// Undefined values are a special case. Comparing an Undefined value with
/// any other value results in Undefined.
///
/// # Arguments
/// * `op` - The comparison operation to perform.
/// * `v1` - The first value.
/// * `v2` - The second value.
pub fn compare(op: &BoolOp, v1: &Value, v2: &Value) -> Result<Value> {
    // Rely on generated comparison operators.
    // The variants of Value enum are specified in the order necessary to
    // obtain the desired semantics.
    Ok(Value::Bool(match op {
        BoolOp::Eq => v1 == v2,
        BoolOp::Ne => v1 != v2,
        BoolOp::Lt => v1 < v2,
        BoolOp::Le => v1 <= v2,
        BoolOp::Gt => v1 > v2,
        BoolOp::Ge => v1 >= v2,
    }))
}
