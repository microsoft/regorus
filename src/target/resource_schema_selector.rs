// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::option_if_let_else, clippy::pattern_type_mismatch)]

use crate::schema::Type;
use crate::{format, Rc, Schema, Value};
use alloc::collections::BTreeMap;

type String = Rc<str>;

use super::{Target, TargetError};

/// Populates the resource_schema_lookup and default_resource_schema fields
/// in a Target based on its resource_schema_selector field and resource_schemas.
///
/// This function analyzes each resource schema to:
/// - Find constant properties that match the selector field name
/// - Build a lookup table mapping constant values to schemas
/// - Collect schemas that don't have the constant property
/// - Raise an error if duplicate constant values are found
pub fn populate_target_lookup_fields(target: &mut Target) -> Result<(), TargetError> {
    target.resource_schema_lookup.clear();
    target.default_resource_schema = None;

    // Track which schema index corresponds to each constant value
    let mut value_to_index = BTreeMap::new();

    // Analyze each schema for constant properties
    for (index, schema) in target.resource_schemas.iter().enumerate() {
        if let Some(constant_value) =
            find_constant_property(schema, &target.resource_schema_selector)
        {
            // Check if this constant value already exists
            if let Some(existing_index) = value_to_index.get(&constant_value) {
                return Err(TargetError::DuplicateConstantValue(format!(
                    "Duplicate constant value '{}' found for resource schema selector field '{}' in schemas at indexes {} and {}",
                    constant_value,
                    target.resource_schema_selector,
                    existing_index,
                    index
                ).into()));
            }
            // Record the mapping and add to lookup table
            value_to_index.insert(constant_value.clone(), index);
            target
                .resource_schema_lookup
                .insert(constant_value, schema.clone());
        } else {
            // Schema doesn't have the constant property
            if target.default_resource_schema.is_some() {
                return Err(TargetError::MultipleDefaultSchemas(format!(
                    "Multiple schemas found without discriminator property '{}'. Only one default resource schema is allowed.",
                    target.resource_schema_selector
                ).into()));
            }
            target.default_resource_schema = Some(schema.clone());
        }
    }

    Ok(())
}

/// Finds a constant property value in a schema for the specified field name.
/// Returns the constant value if found, or None if the schema doesn't have
/// a constant property for the given field.
fn find_constant_property(schema: &Rc<Schema>, field_name: &str) -> Option<Value> {
    match schema.as_type() {
        Type::Object { properties, .. } => {
            // Look for the field in the schema's properties
            if let Some(property_schema) = properties.get(field_name) {
                match property_schema.as_type() {
                    Type::Const { value, .. } => {
                        // Found a constant property - return its value
                        Some(value.clone())
                    }
                    _ => {
                        // Property exists but is not a constant
                        None
                    }
                }
            } else {
                // Field doesn't exist in this schema
                None
            }
        }
        _ => {
            // Schema is not an object type
            None
        }
    }
}
