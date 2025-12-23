// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::pattern_type_mismatch,
    clippy::assertions_on_result_states
)] // test cases assert failures via unwrap/expect panic paths and pattern matching

use crate::{
    schema::{error::ValidationError, validate::SchemaValidator, Schema},
    *,
};
use serde_json::json;

// Helper function to create a schema for Azure Policy effects
fn create_effect_schema() -> Rc<Schema> {
    let schema_json = json!({
        "enum": ["audit", "deny", "disabled", "modify"],
        "description": "Azure Policy effect types"
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    Rc::new(schema)
}

// Helper function to create a deny effect schema
fn create_deny_effect_schema() -> Rc<Schema> {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "effect": {
                "const": "deny"
            },
            "description": {
                "type": "string",
                "description": "Explanation of what is being denied"
            }
        },
        "required": ["effect"],
        "description": "Schema for deny effect in Azure Policy"
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    Rc::new(schema)
}

// Helper function to create an audit effect schema
fn create_audit_effect_schema() -> Rc<Schema> {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "effect": {
                "const": "audit"
            },
            "description": {
                "type": "string",
                "description": "Explanation of what is being audited"
            },
            "auditDetails": {
                "type": "object",
                "properties": {
                    "category": {
                        "enum": ["security", "compliance", "cost", "operational"]
                    },
                    "severity": {
                        "enum": ["low", "medium", "high", "critical"]
                    }
                }
            }
        },
        "required": ["effect"],
        "description": "Schema for audit effect in Azure Policy"
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    Rc::new(schema)
}

// Helper function to create a modify effect schema
fn create_modify_effect_schema() -> Rc<Schema> {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "effect": {
                "const": "modify"
            },
            "description": {
                "type": "string",
                "description": "Explanation of what is being modified"
            },
            "modifyDetails": {
                "type": "object",
                "properties": {
                    "roleDefinitionIds": {
                        "type": "array",
                        "items": {
                            "type": "string"
                        },
                        "description": "List of role definition IDs required for modification"
                    },
                    "operations": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "operation": {
                                    "enum": ["add", "replace", "remove"]
                                },
                                "field": {
                                    "type": "string"
                                },
                                "value": {
                                    "type": "any",
                                    "description": "Value to add or replace"
                                }
                            },
                            "required": ["operation", "field"]
                        }
                    }
                },
                "required": ["roleDefinitionIds", "operations"]
            }
        },
        "required": ["effect", "modifyDetails"],
        "description": "Schema for modify effect in Azure Policy"
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    Rc::new(schema)
}

// Schema validation tests for Azure Policy effects

#[test]
fn test_validate_deny_effect_valid() {
    let schema = create_deny_effect_schema();

    let valid_deny_data = json!({
        "effect": "deny",
        "description": "Deny resources that don't meet security requirements"
    });

    let value = Value::from(valid_deny_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_ok());
}

#[test]
fn test_validate_deny_effect_missing_required() {
    let schema = create_deny_effect_schema();

    let invalid_deny_data = json!({
        "description": "Missing required effect field"
    });

    let value = Value::from(invalid_deny_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::MissingRequiredProperty { property, .. } => {
            assert_eq!(property, "effect".into());
        }
        other => panic!("Expected MissingRequiredProperty error, got: {:?}", other),
    }
}

#[test]
fn test_validate_deny_effect_wrong_const() {
    let schema = create_deny_effect_schema();

    let invalid_deny_data = json!({
        "effect": "audit",
        "description": "Wrong effect type"
    });

    let value = Value::from(invalid_deny_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::PropertyValidationFailed {
            property, error, ..
        } => {
            assert_eq!(property, "effect".into());
            match error.as_ref() {
                ValidationError::ConstMismatch {
                    expected, actual, ..
                } => {
                    assert_eq!(*expected, "\"deny\"".into());
                    assert_eq!(*actual, "\"audit\"".into());
                }
                other => panic!(
                    "Expected ConstMismatch error in nested structure, got: {:?}",
                    other
                ),
            }
        }
        other => panic!("Expected PropertyValidationFailed error, got: {:?}", other),
    }
}

#[test]
fn test_validate_audit_effect_valid() {
    let schema = create_audit_effect_schema();

    let valid_audit_data = json!({
        "effect": "audit",
        "description": "Audit non-compliant resources",
        "auditDetails": {
            "category": "security",
            "severity": "high"
        }
    });

    let value = Value::from(valid_audit_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_ok());
}

#[test]
fn test_validate_audit_effect_invalid_enum() {
    let schema = create_audit_effect_schema();

    let invalid_audit_data = json!({
        "effect": "audit",
        "description": "Audit with invalid category",
        "auditDetails": {
            "category": "invalid_category",
            "severity": "medium"
        }
    });

    let value = Value::from(invalid_audit_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::PropertyValidationFailed {
            property, error, ..
        } => {
            assert_eq!(property, "auditDetails".into());
            match error.as_ref() {
                ValidationError::PropertyValidationFailed {
                    property: inner_prop,
                    error: inner_error,
                    ..
                } => {
                    assert_eq!(*inner_prop, "category".into());
                    match inner_error.as_ref() {
                        ValidationError::NotInEnum { .. } => {
                            // Expected nested error structure
                        }
                        other => panic!(
                            "Expected NotInEnum error in nested structure, got: {:?}",
                            other
                        ),
                    }
                }
                other => panic!(
                    "Expected nested PropertyValidationFailed error, got: {:?}",
                    other
                ),
            }
        }
        other => panic!("Expected PropertyValidationFailed error, got: {:?}", other),
    }
}

#[test]
fn test_validate_modify_effect_valid() {
    let schema = create_modify_effect_schema();

    let valid_modify_data = json!({
        "effect": "modify",
        "description": "Modify resources to add required tags",
        "modifyDetails": {
            "roleDefinitionIds": [
                "/subscriptions/{subscriptionId}/providers/Microsoft.Authorization/roleDefinitions/b24988ac-6180-42a0-ab88-20f7382dd24c"
            ],
            "operations": [
                {
                    "operation": "add",
                    "field": "tags.Environment",
                    "value": "Production"
                }
            ]
        }
    });

    let value = Value::from(valid_modify_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_ok());
}

#[test]
fn test_validate_modify_effect_missing_required_details() {
    let schema = create_modify_effect_schema();

    let invalid_modify_data = json!({
        "effect": "modify",
        "description": "Missing modifyDetails"
    });

    let value = Value::from(invalid_modify_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::MissingRequiredProperty { property, .. } => {
            assert_eq!(property, "modifyDetails".into());
        }
        other => panic!("Expected MissingRequiredProperty error, got: {:?}", other),
    }
}

#[test]
fn test_validate_modify_effect_invalid_operation() {
    let schema = create_modify_effect_schema();

    let invalid_modify_data = json!({
        "effect": "modify",
        "description": "Invalid operation type",
        "modifyDetails": {
            "roleDefinitionIds": ["role-id-1"],
            "operations": [
                {
                    "operation": "invalid_op",
                    "field": "tags.Environment",
                    "value": "Production"
                }
            ]
        }
    });

    let value = Value::from(invalid_modify_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::PropertyValidationFailed {
            property, error, ..
        } => {
            assert_eq!(property, "modifyDetails".into());
            match error.as_ref() {
                ValidationError::PropertyValidationFailed {
                    property: inner_prop,
                    error: inner_error,
                    ..
                } => {
                    assert_eq!(*inner_prop, "operations".into());
                    match inner_error.as_ref() {
                        ValidationError::ArrayItemValidationFailed {
                            index,
                            error: array_error,
                            ..
                        } => {
                            assert_eq!(*index, 0);
                            match array_error.as_ref() {
                                ValidationError::PropertyValidationFailed {
                                    property: op_prop,
                                    error: op_error,
                                    ..
                                } => {
                                    assert_eq!(*op_prop, "operation".into());
                                    match op_error.as_ref() {
                                        ValidationError::NotInEnum { .. } => {
                                            // Expected deeply nested error structure
                                        }
                                        other => panic!("Expected NotInEnum error in operation validation, got: {:?}", other),
                                    }
                                }
                                other => panic!(
                                    "Expected PropertyValidationFailed for operation, got: {:?}",
                                    other
                                ),
                            }
                        }
                        other => {
                            panic!("Expected ArrayItemValidationFailed error, got: {:?}", other)
                        }
                    }
                }
                other => panic!(
                    "Expected nested PropertyValidationFailed error, got: {:?}",
                    other
                ),
            }
        }
        other => panic!("Expected PropertyValidationFailed error, got: {:?}", other),
    }
}

#[test]
fn test_validate_basic_effect_enum() {
    let schema = create_effect_schema();

    // Test all valid enum values
    let valid_effects = ["audit", "deny", "disabled", "modify"];

    for effect in valid_effects {
        let value = Value::from(effect);
        let result = SchemaValidator::validate(&value, &schema);
        assert!(result.is_ok(), "Effect '{effect}' should be valid");
    }

    // Test invalid enum value
    let invalid_value = Value::from("invalid_effect");
    let result = SchemaValidator::validate(&invalid_value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::NotInEnum { .. } => {
            // Expected error type
        }
        other => panic!("Expected NotInEnum error, got: {:?}", other),
    }
}

#[test]
fn test_validate_complex_azure_policy_effect() {
    let complex_schema_json = json!({
        "type": "object",
        "properties": {
            "effect": {
                "enum": ["auditIfNotExists", "deployIfNotExists"]
            },
            "parameters": {
                "type": "object",
                "additionalProperties": { "type": "any" }
            },
            "existenceCondition": {
                "type": "object",
                "properties": {
                    "field": { "type": "string" },
                    "equals": { "type": "string" }
                },
                "required": ["field"],
                "additionalProperties": { "type": "any" }
            },
            "deployment": {
                "type": "object",
                "properties": {
                    "properties": {
                        "type": "object",
                        "properties": {
                            "mode": {
                                "enum": ["incremental", "complete"]
                            },
                            "template": {
                                "type": "object",
                                "additionalProperties": { "type": "any" }
                            },
                            "parameters": {
                                "type": "object",
                                "additionalProperties": { "type": "any" }
                            }
                        },
                        "required": ["mode", "template"],
                        "additionalProperties": { "type": "any" }
                    }
                },
                "required": ["properties"],
                "additionalProperties": { "type": "any" }
            }
        },
        "required": ["effect"],
        "additionalProperties": { "type": "any" }
    });

    let schema = Schema::from_serde_json_value(complex_schema_json).unwrap();

    let valid_complex_data = json!({
        "effect": "deployIfNotExists",
        "parameters": {},
        "existenceCondition": {
            "field": "Microsoft.Security/complianceResults/resourceStatus",
            "equals": "OffByPolicy"
        },
        "deployment": {
            "properties": {
                "mode": "incremental",
                "template": {
                    "$schema": "https://schema.management.azure.com/schemas/2015-01-01/deploymentTemplate.json#",
                    "contentVersion": "1.0.0.0",
                    "resources": []
                },
                "parameters": {}
            }
        }
    });

    let value = Value::from(valid_complex_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_ok());
}

#[test]
fn test_validate_effect_type_mismatch() {
    let schema = create_deny_effect_schema();

    // Pass a non-object value to object schema
    let invalid_data = Value::from("not an object");
    let result = SchemaValidator::validate(&invalid_data, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::TypeMismatch {
            expected, actual, ..
        } => {
            assert_eq!(expected, "object".into());
            assert_eq!(actual, "string".into());
        }
        other => panic!("Expected TypeMismatch error, got: {:?}", other),
    }
}
