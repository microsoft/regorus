// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Utilities for converting between runtime Values and type analysis facts.

use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use crate::value::Value;

use super::model::{
    ConstantValue, StructuralObjectShape, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};

/// Converts a runtime Value into a TypeFact with constant information.
/// This is used when the interpreter evaluates a rule in constant-folding mode
/// and we need to bridge the result back to the type analyzer.
pub(crate) fn value_to_type_fact(value: &Value) -> TypeFact {
    let structural_type = infer_structural_type(value);

    TypeFact::new(
        TypeDescriptor::Structural(structural_type),
        TypeProvenance::Propagated,
    )
    .with_constant(ConstantValue::Known(value.clone()))
}

/// Infers the structural type from a runtime value.
fn infer_structural_type(value: &Value) -> StructuralType {
    match value {
        Value::Null => StructuralType::Null,
        Value::Bool(_) => StructuralType::Boolean,
        Value::Number(n) => {
            if n.is_integer() {
                StructuralType::Integer
            } else {
                StructuralType::Number
            }
        }
        Value::String(_) => StructuralType::String,
        Value::Array(items) => {
            // Try to infer a common element type
            let element_type = if items.is_empty() {
                StructuralType::Any
            } else {
                // Find the most specific common type among all elements
                let types: Vec<_> = items.iter().map(infer_structural_type).collect();
                unify_types(&types)
            };
            StructuralType::Array(Box::new(element_type))
        }
        Value::Set(items) => {
            let element_type = if items.is_empty() {
                StructuralType::Any
            } else {
                let types: Vec<_> = items.iter().map(infer_structural_type).collect();
                unify_types(&types)
            };
            StructuralType::Set(Box::new(element_type))
        }
        Value::Object(fields) => {
            // Capture string-keyed fields; fall back to a generic object if we encounter
            // non-string keys since we cannot statically represent them in a structural shape.
            let mut shape_fields = BTreeMap::new();
            for (key, value) in fields.iter() {
                let Value::String(name) = key else {
                    return StructuralType::Object(Default::default());
                };

                let field_type = infer_structural_type(value);
                shape_fields.insert(name.as_ref().to_owned(), field_type);
            }

            StructuralType::Object(StructuralObjectShape {
                fields: shape_fields,
            })
        }
        Value::Undefined => StructuralType::Unknown,
    }
}

/// Unifies multiple structural types into a single common type.
/// If all types are the same, returns that type.
/// Otherwise, returns a Union or Any as appropriate.
fn unify_types(types: &[StructuralType]) -> StructuralType {
    if types.is_empty() {
        return StructuralType::Unknown;
    }

    // Check if all types are identical (treat Unknown as neutral when Any present)
    let first = &types[0];
    if types.iter().all(|t| t == first) {
        return first.clone();
    }

    // Check if all types are numeric (Number or Integer)
    let all_numeric = types
        .iter()
        .all(|t| matches!(t, StructuralType::Number | StructuralType::Integer));
    if all_numeric {
        // If any is Number, the union is Number; otherwise Integer
        if types.iter().any(|t| matches!(t, StructuralType::Number)) {
            return StructuralType::Number;
        }
        return StructuralType::Integer;
    }

    // Otherwise, create a union
    StructuralType::Union(types.to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::Value;
    use alloc::collections::BTreeMap;
    use alloc::vec;

    #[test]
    fn test_value_to_type_fact_null() {
        let value = Value::Null;
        let fact = value_to_type_fact(&value);
        assert!(matches!(
            fact.descriptor,
            TypeDescriptor::Structural(StructuralType::Null)
        ));
        assert!(matches!(fact.constant, ConstantValue::Known(_)));
    }

    #[test]
    fn test_value_to_type_fact_bool() {
        let value = Value::Bool(true);
        let fact = value_to_type_fact(&value);
        assert!(matches!(
            fact.descriptor,
            TypeDescriptor::Structural(StructuralType::Boolean)
        ));
    }

    #[test]
    fn test_value_to_type_fact_integer() {
        let value = Value::from(42);
        let fact = value_to_type_fact(&value);
        assert!(matches!(
            fact.descriptor,
            TypeDescriptor::Structural(StructuralType::Integer)
        ));
    }

    #[test]
    fn test_value_to_type_fact_string() {
        let value = Value::String("test".into());
        let fact = value_to_type_fact(&value);
        assert!(matches!(
            fact.descriptor,
            TypeDescriptor::Structural(StructuralType::String)
        ));
    }

    #[test]
    fn test_value_to_type_fact_empty_array() {
        let value = Value::from(vec![Value::Null; 0]);
        let fact = value_to_type_fact(&value);
        assert!(matches!(
            fact.descriptor,
            TypeDescriptor::Structural(StructuralType::Array(_))
        ));
    }

    #[test]
    fn test_value_to_type_fact_homogeneous_array() {
        let value = Value::from(vec![Value::from(1), Value::from(2), Value::from(3)]);
        let fact = value_to_type_fact(&value);
        if let TypeDescriptor::Structural(StructuralType::Array(elem_type)) = &fact.descriptor {
            assert!(matches!(**elem_type, StructuralType::Integer));
        } else {
            panic!("Expected array type");
        }
    }

    #[test]
    fn test_value_to_type_fact_object_with_string_keys() {
        let mut fields = BTreeMap::new();
        fields.insert(Value::from("value"), Value::from(1));

        let value = Value::from(fields);
        let fact = value_to_type_fact(&value);

        if let TypeDescriptor::Structural(StructuralType::Object(shape)) = &fact.descriptor {
            let field = shape.fields.get("value").expect("missing field");
            assert!(matches!(field, StructuralType::Integer));
        } else {
            panic!("Expected object type");
        }
    }

    #[test]
    fn test_unify_types_same() {
        let types = vec![StructuralType::Integer, StructuralType::Integer];
        let unified = unify_types(&types);
        assert!(matches!(unified, StructuralType::Integer));
    }

    #[test]
    fn test_unify_types_numeric() {
        let types = vec![StructuralType::Integer, StructuralType::Number];
        let unified = unify_types(&types);
        assert!(matches!(unified, StructuralType::Number));
    }
}
