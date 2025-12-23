// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::unwrap_used, clippy::unused_trait_names)] // tests unwrap intentional failures and import ToString anonymously

use super::super::*;
use crate::Value;
use alloc::string::ToString;
use serde_json::json;

#[test]
fn test_target_deserialization_with_direct_schemas() {
    let target_json = json!({
        "name": "test_target",
        "description": "A test target for validation",
        "version": "1.0.0",
        "resource_schema_selector": "type",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "name": { "type": "string" },
                    "type": { "const": "user" }
                },
                "required": ["name", "type"]
            },
            {
                "type": "object",
                "properties": {
                    "name": { "type": "string" },
                    "type": { "const": "group" }
                },
                "required": ["name", "type"]
            }
        ],
        "effects": {
            "allow": { "type": "boolean" },
            "deny": { "type": "boolean" }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();

    assert_eq!(target.name.as_ref(), "test_target");
    assert_eq!(
        target.description.as_ref().unwrap().as_ref(),
        "A test target for validation"
    );
    assert_eq!(target.version.as_ref(), "1.0.0");
    assert_eq!(target.resource_schema_selector.as_ref(), "type");
    assert_eq!(target.resource_schemas.len(), 2);
    assert_eq!(target.effects.len(), 2);

    // Check that lookup table was populated
    assert_eq!(target.resource_schema_lookup.len(), 2);
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("user".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("group".into())));

    // Check that default_resource_schema is None since all schemas have the discriminator
    assert!(target.default_resource_schema.is_none());
}

#[test]
fn test_target_deserialization_with_mixed_schemas() {
    let target_json = json!({
        "name": "mixed_target",
        "version": "1.0.0",
        "resource_schema_selector": "resourceType",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "id": { "type": "string" },
                    "resourceType": { "const": "storage" }
                },
                "required": ["id", "resourceType"]
            },
            {
                "type": "object",
                "properties": {
                    "id": { "type": "string" },
                    "name": { "type": "string" }
                },
                "required": ["id"]
            }
        ],
        "effects": {
            "permit": { "type": "string" }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();

    assert_eq!(target.name.as_ref(), "mixed_target");
    assert!(target.description.is_none());
    assert_eq!(target.resource_schema_selector.as_ref(), "resourceType");

    // One schema has discriminator, one doesn't
    assert_eq!(target.resource_schema_lookup.len(), 1);
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("storage".into())));

    assert!(target.default_resource_schema.is_some());
}

#[test]
fn test_target_deserialization_multiple_default_schemas_error() {
    let target_json = json!({
        "name": "multiple_default_target",
        "version": "1.0.0",
        "resource_schema_selector": "kind",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "id": { "type": "string" },
                    "data": { "type": "object" }
                },
                "required": ["id"]
            },
            {
                "type": "object",
                "properties": {
                    "name": { "type": "string" },
                    "value": { "type": "number" }
                },
                "required": ["name"]
            }
        ],
        "effects": {
            "allow": { "type": "boolean" },
            "deny": { "type": "boolean" }
        }
    });

    // No schemas have the discriminator field - this should fail with MultipleDefaultSchemas error
    let result = Target::from_json_str(&target_json.to_string());
    assert!(result.is_err());

    let error = result.unwrap_err();
    assert!(matches!(error, TargetError::MultipleDefaultSchemas(_)));
}

#[test]
fn test_target_deserialization_single_default_schema() {
    let target_json = json!({
        "name": "single_default_target",
        "version": "1.0.0",
        "resource_schema_selector": "kind",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "id": { "type": "string" },
                    "data": { "type": "object" }
                },
                "required": ["id"]
            }
        ],
        "effects": {
            "allow": { "type": "boolean" }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();

    // Single schema without discriminator should work fine
    assert_eq!(target.resource_schema_lookup.len(), 0);
    assert!(target.default_resource_schema.is_some());
}

#[test]
fn test_target_deserialization_duplicate_discriminator_error() {
    let target_json = json!({
        "name": "duplicate_target",
        "version": "1.0.0",
        "resource_schema_selector": "type",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "id": { "type": "string" },
                    "type": { "const": "duplicate" }
                },
                "required": ["id", "type"]
            },
            {
                "type": "object",
                "properties": {
                    "name": { "type": "string" },
                    "type": { "const": "duplicate" }
                },
                "required": ["name", "type"]
            }
        ],
        "effects": {
            "allow": { "type": "boolean" }
        }
    });

    let result = Target::from_json_str(&target_json.to_string());

    assert!(result.is_err());
    let error = result.unwrap_err();
    assert!(matches!(error, TargetError::DuplicateConstantValue(_)));
}

#[test]
fn test_target_deserialization_missing_required_field() {
    let target_json = json!({
        "name": "incomplete_target",
        "version": "1.0.0",
        // Missing resource_schema_selector
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "id": { "type": "string" }
                }
            }
        ],
        "effects": {}
    });

    let result = Target::from_json_str(&target_json.to_string());
    assert!(result.is_err());
    let error = result.unwrap_err();
    assert!(matches!(
        error,
        TargetError::JsonParseError(_) | TargetError::DeserializationError(_)
    ));
}

#[test]
fn test_target_deserialization_invalid_json() {
    let invalid_json = "{ invalid json }";

    let result = Target::from_json_str(invalid_json);
    assert!(result.is_err());

    let error = result.unwrap_err();
    assert!(matches!(error, TargetError::JsonParseError(_)));
}

#[test]
fn test_target_deserialization_with_registry_schemas() {
    // This test assumes that there are some schemas in the registries
    // If the registries are empty, this test will fail with appropriate errors

    let target_json = json!({
        "name": "registry_target",
        "version": "1.0.0",
        "resource_schema_selector": "type",
        "resource_schemas": [
            "some_registry_schema_name"  // This will be looked up from RESOURCE_SCHEMA_REGISTRY
        ],
        "effects": {
            "allow": "some_effect_schema_name"  // This will be looked up from EFFECT_SCHEMA_REGISTRY
        }
    });

    // This test will likely fail if the registries are empty, but it demonstrates
    // the structure for testing registry-based schema resolution
    let result = Target::from_json_str(&target_json.to_string());

    // We expect this to fail with a "not found in registry" error since we haven't
    // populated the registries with test data
    if let Err(error) = result {
        assert!(matches!(
            error,
            TargetError::JsonParseError(_) | TargetError::DeserializationError(_)
        ));
    }
}

#[test]
fn test_target_deserialization_numeric_discriminator() {
    let target_json = json!({
        "name": "numeric_target",
        "version": "1.0.0",
        "resource_schema_selector": "level",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "name": { "type": "string" },
                    "level": { "const": 1 }
                },
                "required": ["name", "level"]
            },
            {
                "type": "object",
                "properties": {
                    "name": { "type": "string" },
                    "level": { "const": 2 }
                },
                "required": ["name", "level"]
            }
        ],
        "effects": {
            "grant": { "type": "string" }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();

    // Check that numeric discriminator values work
    assert_eq!(target.resource_schema_lookup.len(), 2);
    assert!(target.resource_schema_lookup.contains_key(&Value::from(1)));
    assert!(target.resource_schema_lookup.contains_key(&Value::from(2)));
    assert!(target.default_resource_schema.is_none());
}

#[test]
fn test_target_deserialization_boolean_discriminator() {
    let target_json = json!({
        "name": "boolean_target",
        "version": "1.0.0",
        "resource_schema_selector": "enabled",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "name": { "type": "string" },
                    "enabled": { "const": true }
                },
                "required": ["name", "enabled"]
            },
            {
                "type": "object",
                "properties": {
                    "name": { "type": "string" },
                    "enabled": { "const": false }
                },
                "required": ["name", "enabled"]
            }
        ],
        "effects": {
            "activate": { "type": "boolean" }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();

    // Check that boolean discriminator values work
    assert_eq!(target.resource_schema_lookup.len(), 2);
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::from(true)));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::from(false)));
    assert!(target.default_resource_schema.is_none());
}
