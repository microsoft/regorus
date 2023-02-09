// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::value::{Value::*, *};

pub fn eq(v1: &Value, v2: &Value) -> Value {
    match (v1, v2) {
        (Undefined, _) | (_, Undefined) => Undefined,
        _ => Bool(v1 == v2),
    }
}

pub fn ne(v1: &Value, v2: &Value) -> Value {
    match (v1, v2) {
        (Undefined, _) | (_, Undefined) => Undefined,
        _ => Bool(v1 != v2),
    }
}

pub fn compare(op: &BoolOp, v1: &Value, v2: &Value) -> Value {
    match op {
        BoolOp::Eq => eq(v1, v2),
        BoolOp::Ne => ne(v1, v2),
        BoolOp::Ge => Bool(v1 >= v2),
        BoolOp::Gt => Bool(v1 > v2),
        BoolOp::Le => Bool(v1 <= v2),
        BoolOp::Lt => Bool(v1 < v2),
    }
}
