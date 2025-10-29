// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::schema::{Schema, Type};
use crate::type_analysis::model::{StructuralObjectShape, StructuralType, TypeDiagnosticSeverity};
use crate::type_analysis::propagation::pipeline::TypeAnalyzer;
use crate::value::Value;

impl TypeAnalyzer {
    /// Join multiple structural types to find their least upper bound (LUB)
    pub(crate) fn join_structural_types(types: &[StructuralType]) -> StructuralType {
        use StructuralType::*;

        if types.is_empty() {
            return StructuralType::Any;
        }

        if types.len() == 1 {
            return Self::normalize_structural_type(types[0].clone());
        }

        let first = &types[0];
        if types.iter().all(|t| t == first) {
            return Self::normalize_structural_type(first.clone());
        }

        let all_numbers = types.iter().all(|t| matches!(t, Number | Integer));
        if all_numbers {
            if types.iter().all(|t| matches!(t, Integer)) {
                return StructuralType::Integer;
            }
            return StructuralType::Number;
        }

        let all_arrays: Option<Vec<StructuralType>> = types
            .iter()
            .map(|t| {
                if let Array(elem) = t {
                    Some((**elem).clone())
                } else {
                    None
                }
            })
            .collect();

        if let Some(element_types) = all_arrays {
            let joined_element = Self::join_structural_types(&element_types);
            return Self::normalize_structural_type(StructuralType::Array(Box::new(
                joined_element,
            )));
        }

        let all_sets: Option<Vec<StructuralType>> = types
            .iter()
            .map(|t| {
                if let Set(elem) = t {
                    Some((**elem).clone())
                } else {
                    None
                }
            })
            .collect();

        if let Some(element_types) = all_sets {
            let joined_element = Self::join_structural_types(&element_types);
            return Self::normalize_structural_type(StructuralType::Set(Box::new(joined_element)));
        }

        let has_union = types.iter().any(|t| matches!(t, Union(_)));
        if has_union {
            let mut all_types = Vec::new();
            for ty in types {
                if let Union(inner) = ty {
                    all_types.extend(inner.clone());
                } else {
                    all_types.push(ty.clone());
                }
            }
            return Self::make_union(all_types);
        }

        Self::make_union(types.to_vec())
    }

    /// Create a Union type with deduplication and flattening
    pub(crate) fn make_union(types: Vec<StructuralType>) -> StructuralType {
        let mut flattened = Vec::new();
        for ty in types {
            if let StructuralType::Union(inner) = ty {
                flattened.extend(inner);
            } else {
                flattened.push(ty);
            }
        }

        let normalized: Vec<StructuralType> = flattened
            .into_iter()
            .map(Self::normalize_structural_type)
            .collect();

        Self::finalize_union(normalized)
    }

    /// Extract the type of a field from a structural object (supports unions)
    pub(crate) fn structural_field_type(
        ty: &StructuralType,
        field: &str,
    ) -> Option<StructuralType> {
        match ty {
            StructuralType::Object(shape) => shape.fields.get(field).cloned(),
            StructuralType::Union(variants) => {
                let mut collected = Vec::new();
                for variant in variants {
                    if let Some(field_ty) = Self::structural_field_type(variant, field) {
                        collected.push(field_ty);
                    } else {
                        return None;
                    }
                }
                if collected.is_empty() {
                    None
                } else {
                    Some(Self::make_union(collected))
                }
            }
            _ => None,
        }
    }

    pub(crate) fn structural_definitely_missing_field(ty: &StructuralType, field: &str) -> bool {
        match ty {
            StructuralType::Object(shape) => !shape.fields.contains_key(field),
            StructuralType::Union(variants) => variants
                .iter()
                .all(|variant| Self::structural_definitely_missing_field(variant, field)),
            StructuralType::Any | StructuralType::Unknown => false,
            _ => true,
        }
    }

    pub(crate) fn structural_type_display(ty: &StructuralType) -> String {
        match ty {
            StructuralType::Any => "any".to_owned(),
            StructuralType::Boolean => "boolean".to_owned(),
            StructuralType::Number => "number".to_owned(),
            StructuralType::Integer => "integer".to_owned(),
            StructuralType::String => "string".to_owned(),
            StructuralType::Null => "null".to_owned(),
            StructuralType::Array(elem) => {
                format!("array[{}]", Self::structural_type_display(elem.as_ref()))
            }
            StructuralType::Set(elem) => {
                format!("set[{}]", Self::structural_type_display(elem.as_ref()))
            }
            StructuralType::Object(shape) => {
                if shape.fields.is_empty() {
                    "object".to_owned()
                } else {
                    let fields: Vec<String> = shape.fields.keys().cloned().collect();
                    format!("object{{{}}}", fields.join(", "))
                }
            }
            StructuralType::Union(variants) => {
                let parts: Vec<String> =
                    variants.iter().map(Self::structural_type_display).collect();
                format!("union[{}]", parts.join(" | "))
            }
            StructuralType::Enum(values) => {
                let rendered: Vec<String> = values
                    .iter()
                    .map(|value| value.to_json_str().unwrap_or_else(|_| "?".to_owned()))
                    .collect();
                format!("enum[{}]", rendered.join(" | "))
            }
            StructuralType::Unknown => "unknown".to_owned(),
        }
    }

    pub(crate) fn structural_missing_property_message(
        struct_ty: &StructuralType,
        field: &str,
    ) -> Option<String> {
        if !Self::structural_definitely_missing_field(struct_ty, field) {
            return None;
        }

        match struct_ty {
            StructuralType::Object(shape) => {
                let fields: Vec<String> = shape.fields.keys().cloned().collect();
                if fields.is_empty() {
                    Some(format!(
                        "Property '{}' is not defined on this object",
                        field
                    ))
                } else {
                    Some(format!(
                        "Property '{}' is not defined on this object; known fields: {}",
                        field,
                        fields.join(", ")
                    ))
                }
            }
            StructuralType::Union(variants) => {
                let parts: Vec<String> =
                    variants.iter().map(Self::structural_type_display).collect();
                Some(format!(
                    "Property '{}' is not defined on any of the inferred union types ({})",
                    field,
                    parts.join(" | ")
                ))
            }
            StructuralType::Any | StructuralType::Unknown => None,
            other => Some(format!(
                "Cannot access property '{}' on {} value",
                field,
                Self::structural_type_display(other)
            )),
        }
    }

    /// Extract the element type from a structural array (supports unions)
    pub(crate) fn structural_array_element(ty: &StructuralType) -> Option<StructuralType> {
        match ty {
            StructuralType::Array(elem) | StructuralType::Set(elem) => Some((**elem).clone()),
            StructuralType::Union(variants) => {
                let mut collected = Vec::new();
                for variant in variants {
                    if let Some(elem_ty) = Self::structural_array_element(variant) {
                        collected.push(elem_ty);
                    } else {
                        return None;
                    }
                }
                if collected.is_empty() {
                    None
                } else {
                    Some(Self::make_union(collected))
                }
            }
            _ => None,
        }
    }

    pub(crate) fn schema_has_named_property(schema: &Schema, field: &str) -> bool {
        match schema.as_type() {
            Type::Object { properties, .. } => properties.contains_key(field),
            Type::AnyOf(variants) => variants
                .iter()
                .any(|variant| Self::schema_has_named_property(variant, field)),
            _ => false,
        }
    }

    pub(crate) fn schema_missing_property_message(schema: &Schema, field: &str) -> Option<String> {
        match schema.as_type() {
            Type::Object { properties, .. } => {
                let fields: Vec<String> = properties
                    .keys()
                    .map(|name| name.as_ref().to_owned())
                    .collect();
                if fields.is_empty() {
                    Some(format!("Property '{}' is not defined by the schema", field))
                } else {
                    Some(format!(
                        "Property '{}' is not defined by the schema; known properties: {}",
                        field,
                        fields.join(", ")
                    ))
                }
            }
            Type::AnyOf(variants) => {
                let defined_somewhere = variants
                    .iter()
                    .any(|variant| Self::schema_has_named_property(variant, field));
                if defined_somewhere {
                    None
                } else {
                    Some(format!(
                        "Property '{}' is not defined by any branch of this schema",
                        field
                    ))
                }
            }
            Type::Any { .. } => None,
            _ => Some(format!(
                "Cannot access property '{}' on non-object schema type",
                field
            )),
        }
    }

    fn schema_allows_additional_properties(schema: &Schema) -> bool {
        match schema.as_type() {
            Type::Object {
                additional_properties,
                ..
            } => additional_properties.is_some(),
            Type::AnyOf(variants) => variants
                .iter()
                .all(Self::schema_allows_additional_properties),
            _ => false,
        }
    }

    pub(crate) fn schema_missing_property_severity(schema: &Schema) -> TypeDiagnosticSeverity {
        if Self::schema_allows_additional_properties(schema) {
            TypeDiagnosticSeverity::Warning
        } else {
            TypeDiagnosticSeverity::Error
        }
    }

    pub(crate) fn normalize_structural_type(ty: StructuralType) -> StructuralType {
        use StructuralType::*;

        match ty {
            Enum(values) if Self::enum_values_are_boolean(&values) => Boolean,
            Enum(values) => Enum(values),
            Array(elem) => Array(Box::new(Self::normalize_structural_type(*elem))),
            Set(elem) => Set(Box::new(Self::normalize_structural_type(*elem))),
            Object(shape) => Object(Self::normalize_object_shape(shape)),
            Union(variants) => {
                let normalized: Vec<StructuralType> = variants
                    .into_iter()
                    .map(Self::normalize_structural_type)
                    .collect();
                Self::finalize_union(normalized)
            }
            other => other,
        }
    }

    fn normalize_object_shape(shape: StructuralObjectShape) -> StructuralObjectShape {
        let mut fields = BTreeMap::new();
        for (name, ty) in shape.fields.into_iter() {
            fields.insert(name, Self::normalize_structural_type(ty));
        }
        StructuralObjectShape { fields }
    }

    fn finalize_union(mut variants: Vec<StructuralType>) -> StructuralType {
        if variants.is_empty() {
            return StructuralType::Unknown;
        }

        variants.sort_by(|a, b| format!("{:?}", a).cmp(&format!("{:?}", b)));
        variants.dedup();

        let has_specific = variants
            .iter()
            .any(|ty| !matches!(ty, StructuralType::Any | StructuralType::Unknown));
        if has_specific {
            variants.retain(|ty| !matches!(ty, StructuralType::Any | StructuralType::Unknown));
        }

        if variants.is_empty() {
            return StructuralType::Unknown;
        }

        if variants.len() == 1 {
            return variants.into_iter().next().unwrap();
        }

        StructuralType::Union(variants)
    }

    fn enum_values_are_boolean(values: &[Value]) -> bool {
        values.iter().all(|value| value.as_bool().is_ok())
    }
}
