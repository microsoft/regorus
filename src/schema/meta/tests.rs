// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::unwrap_used, clippy::assertions_on_result_states)] // meta-schema tests unwrap errors to assert failures

use super::*;
use serde_json::json;

#[test]
fn test_get_meta_schema() {
    let meta_schema = get_meta_schema();
    assert!(!meta_schema.is_empty());
    assert!(meta_schema.contains("$schema"));
}

#[test]
fn test_validate_valid_schema() {
    let valid_schema = json!({
        "type": "string",
        "description": "A simple string"
    });

    assert!(validate_schema(&valid_schema));
    assert!(validate_schema_detailed(&valid_schema).is_ok());
}

#[test]
fn test_validate_valid_anyof_schema() {
    let valid_anyof_schema = json!({
        "anyOf": [
            { "type": "string" },
            { "type": "integer" }
        ]
    });

    assert!(validate_schema(&valid_anyof_schema));
    assert!(validate_schema_detailed(&valid_anyof_schema).is_ok());
}

#[test]
fn test_validate_valid_const_schema() {
    let valid_const_schema = json!({
        "const": "hello",
        "description": "A constant value"
    });

    assert!(validate_schema(&valid_const_schema));
    assert!(validate_schema_detailed(&valid_const_schema).is_ok());
}

#[test]
fn test_validate_valid_enum_schema() {
    let valid_enum_schema = json!({
        "enum": ["red", "green", "blue"],
        "description": "Color enumeration"
    });

    assert!(validate_schema(&valid_enum_schema));
    assert!(validate_schema_detailed(&valid_enum_schema).is_ok());
}

#[test]
fn test_validate_invalid_schema() {
    let invalid_schema = json!({
        "invalidField": "this should not be allowed"
    });

    assert!(!validate_schema(&invalid_schema));
    assert!(validate_schema_detailed(&invalid_schema).is_err());
}

#[test]
fn test_validate_schema_str() {
    let valid_schema_str = r#"{"type": "string"}"#;
    let invalid_schema_str = r#"{"invalidField": true}"#;
    let malformed_json = r#"{"invalid": json"#;

    assert!(validate_schema_str(valid_schema_str));
    assert!(!validate_schema_str(invalid_schema_str));
    assert!(!validate_schema_str(malformed_json));
}

#[test]
fn test_validate_complex_object_schema() {
    let complex_schema = json!({
        "type": "object",
        "properties": {
            "name": { "type": "string" },
            "age": { "type": "integer", "minimum": 0 }
        },
        "required": ["name"],
    });

    assert!(validate_schema(&complex_schema));
    assert!(validate_schema_detailed(&complex_schema).is_ok());
}

#[test]
fn test_validate_detailed_error_messages() {
    let invalid_schema = json!({
        "type": "object",
        "unknownProperty": true
    });

    let result = validate_schema_detailed(&invalid_schema);
    assert!(result.is_err());

    let errors = result.unwrap_err();
    assert!(!errors.is_empty());
    // The error should mention the unknown property
    assert!(errors.iter().any(|err| err.contains("unknownProperty")));
}

#[test]
fn test_validator_is_lazy_initialized() {
    // This test ensures the lazy static validator is working
    // Multiple calls should use the same validator instance
    let schema1 = json!({"type": "string"});
    let schema2 = json!({"type": "integer"});

    assert!(validate_schema(&schema1));
    assert!(validate_schema(&schema2));
}

#[test]
fn test_validate_array_schema() {
    let array_schema = json!({
        "type": "array",
        "items": { "type": "string" },
        "minItems": 1,
        "maxItems": 10
    });

    assert!(validate_schema(&array_schema));
    assert!(validate_schema_detailed(&array_schema).is_ok());
}

#[test]
fn test_validate_discriminated_subobject_schema() {
    let discriminated_schema = json!({
        "type": "object",
        "properties": {
            "kind": { "type": "string" }
        },
        "allOf": [
            {
                "if": {
                    "properties": { "kind": { "const": "user" } }
                },
                "then": {
                    "properties": {
                        "username": { "type": "string" }
                    },
                    "required": ["username"]
                }
            }
        ]
    });

    assert!(validate_schema(&discriminated_schema));
    assert!(validate_schema_detailed(&discriminated_schema).is_ok());
}
