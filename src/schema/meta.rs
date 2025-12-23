// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::expect_used,
    clippy::missing_const_for_fn,
    clippy::option_if_let_else
)] // meta schema loader expects static resources
#![allow(dead_code)]
use crate::*;
use lazy_static::lazy_static;

const META_SCHEMA: &str = include_str!("meta.schema.json");

lazy_static! {
    /// Lazy static JSON Schema validator for the Regorus meta-schema.
    /// This validator is initialized once and can be used to validate
    /// any schema definition against the Regorus meta-schema format.
    static ref META_SCHEMA_VALIDATOR: jsonschema::Validator = {
        let meta_schema_json: serde_json::Value = serde_json::from_str(META_SCHEMA)
            .expect("META_SCHEMA should be valid JSON");

        jsonschema::validator_for(&meta_schema_json)
            .expect("META_SCHEMA should be a valid JSON Schema")
    };
}

pub fn get_meta_schema() -> &'static str {
    META_SCHEMA
}

/// Validates a schema definition against the Regorus meta-schema.
/// Returns true if the schema is valid, false otherwise.
pub fn validate_schema(schema: &serde_json::Value) -> bool {
    META_SCHEMA_VALIDATOR.is_valid(schema)
}

/// Validates a schema definition against the Regorus meta-schema.
/// Returns Ok(()) if valid, or Err with validation errors if invalid.
pub fn validate_schema_detailed(schema: &serde_json::Value) -> Result<(), Vec<String>> {
    if let jsonschema::BasicOutput::Invalid(errors) = META_SCHEMA_VALIDATOR.apply(schema).basic() {
        let msgs: alloc::collections::BTreeSet<String> = errors
            .iter()
            .map(|e| format!("{}: {}", e.instance_location(), e.error_description()))
            .collect();
        let msgs: Vec<String> = msgs.into_iter().collect();
        return Err(msgs);
    }

    Ok(())
}

/// Validates a schema definition from a JSON string.
/// Returns true if the schema is valid, false otherwise.
pub fn validate_schema_str(schema_str: &str) -> bool {
    match serde_json::from_str::<serde_json::Value>(schema_str) {
        Ok(schema) => validate_schema(&schema),
        Err(_) => false, // Invalid JSON
    }
}

#[cfg(test)]
mod tests;
