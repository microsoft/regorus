// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::super::registry::*;
use crate::{
    schema::{error::ValidationError, validate::SchemaValidator, Schema, Type},
    *,
};
use serde_json::json;

type String = Rc<str>;

use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref EFFECT_TEST_LOCK: Mutex<()> = Mutex::new(());
}

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

#[test]
fn test_basic_effect_enum_schema() {
    #[cfg(feature = "std")]
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let effect_schema = create_effect_schema();

    // Test registration of basic effect enum schema
    let result = registry.register("azure.policy.effect", effect_schema.clone());
    assert!(result.is_ok());
    assert!(registry.contains("azure.policy.effect"));
    assert_eq!(registry.len(), 1);

    // Verify schema can be retrieved
    let retrieved = registry.get("azure.policy.effect");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&effect_schema, &retrieved.unwrap()));
}

#[test]
fn test_deny_effect_schema() {
    #[cfg(feature = "std")]
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let deny_schema = create_deny_effect_schema();

    // Test registration of deny effect schema
    let result = registry.register("azure.policy.deny", deny_schema.clone());
    assert!(result.is_ok());
    assert!(registry.contains("azure.policy.deny"));

    // Verify schema structure
    match deny_schema.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            assert!(properties.contains_key("effect"));
            assert!(properties.contains_key("description"));
            assert!(required.clone().unwrap().contains(&"effect".into()));
        }
        _ => panic!("Expected deny schema to be an object type"),
    }
}

#[test]
fn test_audit_effect_schema() {
    #[cfg(feature = "std")]
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let audit_schema = create_audit_effect_schema();

    // Test registration of audit effect schema
    let result = registry.register("azure.policy.audit", audit_schema.clone());
    assert!(result.is_ok());
    assert!(registry.contains("azure.policy.audit"));

    // Verify schema structure
    match audit_schema.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            assert!(properties.contains_key("effect"));
            assert!(properties.contains_key("description"));
            assert!(properties.contains_key("auditDetails"));
            if let Some(req) = required {
                assert!(req.contains(&"effect".into()));
            } else {
                panic!("Expected required field to be present");
            }

            // Check auditDetails structure
            let audit_details = properties.get("auditDetails").unwrap();
            match audit_details.as_type() {
                Type::Object {
                    properties: audit_props,
                    ..
                } => {
                    assert!(audit_props.contains_key("category"));
                    assert!(audit_props.contains_key("severity"));
                }
                _ => panic!("Expected auditDetails to be an object"),
            }
        }
        _ => panic!("Expected audit schema to be an object type"),
    }
}

#[test]
fn test_modify_effect_schema() {
    #[cfg(feature = "std")]
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let modify_schema = create_modify_effect_schema();

    // Test registration of modify effect schema
    let result = registry.register("azure.policy.modify", modify_schema.clone());
    assert!(result.is_ok());
    assert!(registry.contains("azure.policy.modify"));

    // Verify schema structure
    match modify_schema.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            assert!(properties.contains_key("effect"));
            assert!(properties.contains_key("description"));
            assert!(properties.contains_key("modifyDetails"));
            assert!(required.as_ref().unwrap().contains(&"effect".into()));
            assert!(required.as_ref().unwrap().contains(&"modifyDetails".into()));

            // Check modifyDetails structure
            let modify_details = properties.get("modifyDetails").unwrap();
            match modify_details.as_type() {
                Type::Object {
                    properties: modify_props,
                    required: modify_required,
                    ..
                } => {
                    assert!(modify_props.contains_key("roleDefinitionIds"));
                    assert!(modify_props.contains_key("operations"));
                    assert!(modify_required
                        .as_ref()
                        .unwrap()
                        .contains(&"roleDefinitionIds".into()));
                    assert!(modify_required
                        .as_ref()
                        .unwrap()
                        .contains(&"operations".into()));
                }
                _ => panic!("Expected modifyDetails to be an object"),
            }
        }
        _ => panic!("Expected modify schema to be an object type"),
    }
}

#[test]
fn test_multiple_effect_schemas() {
    #[cfg(feature = "std")]
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();

    // Register all effect schemas
    let deny_schema = create_deny_effect_schema();
    let audit_schema = create_audit_effect_schema();
    let modify_schema = create_modify_effect_schema();

    assert!(registry.register("azure.policy.deny", deny_schema).is_ok());
    assert!(registry
        .register("azure.policy.audit", audit_schema)
        .is_ok());
    assert!(registry
        .register("azure.policy.modify", modify_schema)
        .is_ok());

    // Verify all are registered
    assert_eq!(registry.len(), 3);
    assert!(registry.contains("azure.policy.deny"));
    assert!(registry.contains("azure.policy.audit"));
    assert!(registry.contains("azure.policy.modify"));

    // Verify they can all be retrieved
    assert!(registry.get("azure.policy.deny").is_some());
    assert!(registry.get("azure.policy.audit").is_some());
    assert!(registry.get("azure.policy.modify").is_some());

    // List all names
    let names = registry.list_names();
    assert_eq!(names.len(), 3);
    assert!(names.contains(&"azure.policy.deny".into()));
    assert!(names.contains(&"azure.policy.audit".into()));
    assert!(names.contains(&"azure.policy.modify".into()));
}

#[test]
fn test_global_effect_registry() {
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    // Clear registry
    effect::clear();

    // Register Azure Policy effects
    let deny_schema = create_deny_effect_schema();
    let audit_schema = create_audit_effect_schema();
    let modify_schema = create_modify_effect_schema();

    assert!(effect::register("azure.policy.deny", deny_schema).is_ok());
    std::dbg!(effect::list_names());
    assert!(effect::register("azure.policy.audit", audit_schema).is_ok());
    std::dbg!(effect::list_names());
    assert!(effect::register("azure.policy.modify", modify_schema).is_ok());
    std::dbg!(effect::list_names());
    // Verify all are registered in global registry

    assert_eq!(effect::len(), 3);
    assert!(effect::contains("azure.policy.deny"));
    assert!(effect::contains("azure.policy.audit"));
    assert!(effect::contains("azure.policy.modify"));

    // Test retrieval from global registry
    let retrieved_deny = effect::get("azure.policy.deny");
    let retrieved_audit = effect::get("azure.policy.audit");
    let retrieved_modify = effect::get("azure.policy.modify");

    assert!(retrieved_deny.is_some());
    assert!(retrieved_audit.is_some());
    assert!(retrieved_modify.is_some());

    // Clean up
    effect::clear();
}

#[test]
fn test_effect_schema_validation_patterns() {
    #[cfg(feature = "std")]
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();

    // Test schema with various Azure Policy patterns
    let complex_effect_schema = json!({
        "type": "object",
        "properties": {
            "effect": {
                "enum": ["audit", "deny", "disabled", "modify", "auditIfNotExists", "deployIfNotExists"]
            },
            "parameters": {
                "type": "object",
                "description": "Parameters for the effect"
            },
            "existenceCondition": {
                "type": "object",
                "description": "Condition for existence-based effects"
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
                                "type": "object"
                            },
                            "parameters": {
                                "type": "object"
                            }
                        }
                    }
                }
            }
        },
        "required": ["effect"],
        "description": "Comprehensive Azure Policy effect schema"
    });

    let schema = Schema::from_serde_json_value(complex_effect_schema).unwrap();
    let schema_rc = Rc::new(schema);

    let result = registry.register("azure.policy.complex", schema_rc);
    assert!(result.is_ok());
    assert!(registry.contains("azure.policy.complex"));
}

#[test]
fn test_effect_schema_with_invalid_names() {
    #[cfg(feature = "std")]
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let effect_schema = create_effect_schema();

    // Test invalid names
    assert!(registry.register("", effect_schema.clone()).is_err());
    assert!(registry.register("   ", effect_schema.clone()).is_err());
    assert!(registry.register("\t", effect_schema.clone()).is_err());
    assert!(registry.register("\n", effect_schema).is_err());

    // Verify registry is empty
    assert!(registry.is_empty());
}

#[test]
fn test_effect_schema_duplicate_registration() {
    #[cfg(feature = "std")]
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let deny_schema = create_deny_effect_schema();

    // First registration should succeed
    assert!(registry
        .register("azure.policy.deny", deny_schema.clone())
        .is_ok());
    assert_eq!(registry.len(), 1);

    // Duplicate registration should fail
    let duplicate_result = registry.register("azure.policy.deny", deny_schema);
    assert!(duplicate_result.is_err());

    // Verify error type
    match duplicate_result.unwrap_err() {
        SchemaRegistryError::AlreadyExists(name) => {
            assert_eq!(name.as_ref(), "azure.policy.deny");
        }
        _ => panic!("Expected AlreadyExists error"),
    }

    // Registry should still have only one entry
    assert_eq!(registry.len(), 1);
}

#[test]
fn test_azure_policy_effect_removal() {
    #[cfg(feature = "std")]
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();

    // Register multiple Azure Policy effects
    let effects = vec![
        ("azure.policy.deny", create_deny_effect_schema()),
        ("azure.policy.audit", create_audit_effect_schema()),
        ("azure.policy.modify", create_modify_effect_schema()),
    ];

    for (name, schema) in &effects {
        assert!(registry.register(*name, schema.clone()).is_ok());
    }

    assert_eq!(registry.len(), 3);

    // Remove one effect
    let removed = registry.remove("azure.policy.audit");
    assert!(removed.is_some());
    assert_eq!(registry.len(), 2);
    assert!(!registry.contains("azure.policy.audit"));

    // Verify the removed schema is correct
    let removed_schema = removed.unwrap();
    assert!(Rc::ptr_eq(&effects[1].1, &removed_schema));

    // Other effects should still be present
    assert!(registry.contains("azure.policy.deny"));
    assert!(registry.contains("azure.policy.modify"));
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_effect_schema_access() {
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    use std::sync::Barrier;
    use std::thread;

    // Create isolated registry for this test
    let test_registry = Rc::new(SchemaRegistry::new());
    let barrier = Rc::new(Barrier::new(3));
    let mut handles = vec![];

    // Test concurrent registration of different Azure Policy effects
    let effects = [
        "azure.policy.deny",
        "azure.policy.audit",
        "azure.policy.modify",
    ];

    for (i, effect_name) in effects.iter().enumerate() {
        let barrier = Rc::clone(&barrier);
        let registry = Rc::clone(&test_registry);
        let name: String = (*effect_name).into();

        let handle: thread::JoinHandle<Result<(), SchemaRegistryError>> =
            thread::spawn(move || {
                let schema = match i {
                    0 => create_deny_effect_schema(),
                    1 => create_audit_effect_schema(),
                    2 => create_modify_effect_schema(),
                    _ => unreachable!(),
                };

                barrier.wait();
                registry.register(name, schema)
            });

        handles.push(handle);
    }

    // Wait for all threads to complete
    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

    // All registrations should succeed
    for result in results {
        assert!(result.is_ok());
    }

    // Should have 3 effect schemas registered
    assert_eq!(test_registry.len(), 3);
    assert!(test_registry.contains("azure.policy.deny"));
    assert!(test_registry.contains("azure.policy.audit"));
    assert!(test_registry.contains("azure.policy.modify"));
}

#[test]
fn test_azure_policy_effect_clear() {
    #[cfg(feature = "std")]
    let _lock = EFFECT_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();

    // Register multiple Azure Policy effects
    assert!(registry
        .register("azure.policy.deny", create_deny_effect_schema())
        .is_ok());
    assert!(registry
        .register("azure.policy.audit", create_audit_effect_schema())
        .is_ok());
    assert!(registry
        .register("azure.policy.modify", create_modify_effect_schema())
        .is_ok());

    assert_eq!(registry.len(), 3);
    assert!(!registry.is_empty());

    // Clear all effects
    registry.clear();

    assert_eq!(registry.len(), 0);
    assert!(registry.is_empty());
    assert!(registry.list_names().is_empty());

    // Verify specific effects are no longer present
    assert!(!registry.contains("azure.policy.deny"));
    assert!(!registry.contains("azure.policy.audit"));
    assert!(!registry.contains("azure.policy.modify"));
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
