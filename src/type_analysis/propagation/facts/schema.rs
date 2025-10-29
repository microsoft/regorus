// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::vec::Vec;

use crate::schema::{Schema, Type};
use crate::value::Value;

pub(crate) fn schema_property(schema: &Schema, field: &str) -> Option<(Schema, Option<Value>)> {
    match schema.as_type() {
        Type::Object {
            properties,
            additional_properties,
            ..
        } => {
            let prop_schema = properties
                .get(field)
                .cloned()
                .or_else(|| additional_properties.clone())?;
            let constant = extract_schema_constant(&prop_schema);
            Some((prop_schema, constant))
        }
        Type::AnyOf(variants) => {
            let results: Vec<_> = variants
                .iter()
                .filter_map(|variant| schema_property(variant, field))
                .collect();

            if results.is_empty() {
                return None;
            }

            let prop_schema = results[0].0.clone();

            let mut constant: Option<Value> = results[0].1.clone();
            for (_, var_const) in results.iter().skip(1) {
                match (constant.as_ref(), var_const.as_ref()) {
                    (Some(c1), Some(c2)) if c1 != c2 => {
                        constant = None;
                        break;
                    }
                    (Some(_), None) | (None, Some(_)) => {
                        constant = None;
                        break;
                    }
                    _ => {}
                }
            }

            Some((prop_schema, constant))
        }
        _ => None,
    }
}

pub(crate) fn schema_additional_properties_schema(schema: &Schema) -> Option<Schema> {
    match schema.as_type() {
        Type::Object {
            additional_properties,
            ..
        } => additional_properties.clone(),
        _ => None,
    }
}

pub(crate) fn schema_array_items(schema: &Schema) -> Option<(Schema, Option<Value>)> {
    match schema.as_type() {
        Type::Array { items, .. } | Type::Set { items, .. } => {
            let constant = extract_schema_constant(items);
            Some((items.clone(), constant))
        }
        Type::AnyOf(variants) => {
            let results: Vec<_> = variants.iter().filter_map(schema_array_items).collect();

            if results.is_empty() {
                return None;
            }

            let item_schema = results[0].0.clone();

            let mut constant: Option<Value> = results[0].1.clone();
            for (_, var_const) in results.iter().skip(1) {
                match (constant.as_ref(), var_const.as_ref()) {
                    (Some(c1), Some(c2)) if c1 != c2 => {
                        constant = None;
                        break;
                    }
                    (Some(_), None) | (None, Some(_)) => {
                        constant = None;
                        break;
                    }
                    _ => {}
                }
            }

            Some((item_schema, constant))
        }
        _ => None,
    }
}

pub(crate) fn schema_allows_value(schema: &Schema, value: &Value) -> bool {
    match schema.as_type() {
        Type::Enum { values, .. } => values.iter().any(|v| v == value),
        Type::Const { value: allowed, .. } => allowed == value,
        Type::AnyOf(variants) => variants
            .iter()
            .any(|variant| schema_allows_value(variant, value)),
        _ => true,
    }
}

pub(crate) fn extract_schema_constant(schema: &Schema) -> Option<Value> {
    match schema.as_type() {
        Type::Const { value, .. } => Some(value.clone()),
        Type::Enum { values, .. } => {
            if values.len() == 1 {
                Some(values[0].clone())
            } else {
                None
            }
        }
        Type::AnyOf(variants) => {
            let mut constant: Option<Value> = None;
            for variant in variants.iter() {
                match extract_schema_constant(variant) {
                    Some(val) => {
                        if let Some(ref existing) = constant {
                            if existing != &val {
                                return None;
                            }
                        } else {
                            constant = Some(val);
                        }
                    }
                    None => {
                        return None;
                    }
                }
            }
            constant
        }
        _ => None,
    }
}
