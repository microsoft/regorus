// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Literal expression type inference (strings, numbers, booleans, null)

use crate::type_analysis::model::{
    ConstantValue, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::value::Value;

use super::super::pipeline::TypeAnalyzer;

impl TypeAnalyzer {
    pub(crate) fn infer_string_literal(&self, value: &Value) -> TypeFact {
        TypeFact::new(
            TypeDescriptor::Structural(StructuralType::String),
            TypeProvenance::Literal,
        )
        .with_constant(ConstantValue::known(value.clone()))
    }

    pub(crate) fn infer_number_literal(&self, value: &Value) -> TypeFact {
        match value {
            Value::Number(number) if number.is_integer() => TypeFact::new(
                TypeDescriptor::Structural(StructuralType::Integer),
                TypeProvenance::Literal,
            )
            .with_constant(ConstantValue::known(value.clone())),
            _ => TypeFact::new(
                TypeDescriptor::Structural(StructuralType::Number),
                TypeProvenance::Literal,
            )
            .with_constant(ConstantValue::known(value.clone())),
        }
    }

    pub(crate) fn infer_bool_literal(&self, value: &Value) -> TypeFact {
        TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Boolean),
            TypeProvenance::Literal,
        )
        .with_constant(ConstantValue::known(value.clone()))
    }

    pub(crate) fn infer_null_literal(&self, value: &Value) -> TypeFact {
        TypeFact::new(
            TypeDescriptor::Structural(StructuralType::Null),
            TypeProvenance::Literal,
        )
        .with_constant(ConstantValue::known(value.clone()))
    }
}
