// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::panic,
    clippy::unwrap_used,
    clippy::unreachable,
    clippy::indexing_slicing,
    clippy::assertions_on_result_states,
    clippy::pattern_type_mismatch
)] // registry effect tests unwrap/panic for invariant checks

use super::super::registry::*;
use crate::{
    registry::{instances::EFFECT_SCHEMA_REGISTRY, schemas::effect},
    schema::Schema,
    *,
};
use serde_json::json;

type String = Rc<str>;
type SchemaRegistryError = RegistryError;

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
    let effect_schema = create_effect_schema();

    // Test registration of basic effect enum schema
    let result =
        EFFECT_SCHEMA_REGISTRY.register("azure.policy.effect.basic", effect_schema.clone());
    assert!(result.is_ok());
    assert!(EFFECT_SCHEMA_REGISTRY.contains("azure.policy.effect.basic"));

    // Verify schema can be retrieved
    let retrieved = EFFECT_SCHEMA_REGISTRY.get("azure.policy.effect.basic");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&effect_schema, &retrieved.unwrap()));
}

#[test]
fn test_deny_effect_schema() {
    let deny_schema = create_deny_effect_schema();

    // Test registration of deny effect schema
    let result = EFFECT_SCHEMA_REGISTRY.register("azure.policy.deny.test", deny_schema.clone());
    assert!(result.is_ok());
    assert!(EFFECT_SCHEMA_REGISTRY.contains("azure.policy.deny.test"));

    // Verify basic functionality - we can't inspect internal structure due to private as_type()
    assert!(EFFECT_SCHEMA_REGISTRY.contains("azure.policy.deny.test"));

    // The schema should be retrievable
    let retrieved = EFFECT_SCHEMA_REGISTRY.get("azure.policy.deny.test");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&deny_schema, &retrieved.unwrap()));
}

#[test]
fn test_audit_effect_schema() {
    let audit_schema = create_audit_effect_schema();

    // Test registration of audit effect schema
    let result = EFFECT_SCHEMA_REGISTRY.register("azure.policy.audit.test", audit_schema.clone());
    assert!(result.is_ok());
    assert!(EFFECT_SCHEMA_REGISTRY.contains("azure.policy.audit.test"));

    // Verify basic functionality - we can't inspect internal structure due to private as_type()
    assert!(EFFECT_SCHEMA_REGISTRY.contains("azure.policy.audit.test"));

    // The schema should be retrievable
    let retrieved = EFFECT_SCHEMA_REGISTRY.get("azure.policy.audit.test");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&audit_schema, &retrieved.unwrap()));
}

#[test]
fn test_modify_effect_schema() {
    let modify_schema = create_modify_effect_schema();

    // Test registration of modify effect schema
    let result = EFFECT_SCHEMA_REGISTRY.register("azure.policy.modify.test", modify_schema.clone());
    assert!(result.is_ok());
    assert!(EFFECT_SCHEMA_REGISTRY.contains("azure.policy.modify.test"));

    // Verify basic functionality - we can't inspect internal structure due to private as_type()
    assert!(EFFECT_SCHEMA_REGISTRY.contains("azure.policy.modify.test"));

    // The schema should be retrievable
    let retrieved = EFFECT_SCHEMA_REGISTRY.get("azure.policy.modify.test");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&modify_schema, &retrieved.unwrap()));
}

#[test]
fn test_multiple_effect_schemas() {
    // Register all effect schemas with unique names for this specific test
    let deny_schema = create_deny_effect_schema();
    let audit_schema = create_audit_effect_schema();
    let modify_schema = create_modify_effect_schema();

    // Use highly unique names to avoid conflicts with other tests
    let deny_name = "azure.policy.deny.multiple.test";
    let audit_name = "azure.policy.audit.multiple.test";
    let modify_name = "azure.policy.modify.multiple.test";

    assert!(EFFECT_SCHEMA_REGISTRY
        .register(deny_name, deny_schema)
        .is_ok());
    assert!(EFFECT_SCHEMA_REGISTRY
        .register(audit_name, audit_schema)
        .is_ok());
    assert!(EFFECT_SCHEMA_REGISTRY
        .register(modify_name, modify_schema)
        .is_ok());

    // Verify all are registered
    assert!(EFFECT_SCHEMA_REGISTRY.contains(deny_name));
    assert!(EFFECT_SCHEMA_REGISTRY.contains(audit_name));
    assert!(EFFECT_SCHEMA_REGISTRY.contains(modify_name));

    // Verify they can all be retrieved
    assert!(EFFECT_SCHEMA_REGISTRY.get(deny_name).is_some());
    assert!(EFFECT_SCHEMA_REGISTRY.get(audit_name).is_some());
    assert!(EFFECT_SCHEMA_REGISTRY.get(modify_name).is_some());
}

#[test]
fn test_global_effect_registry() {
    // Register Azure Policy effects with unique names
    let deny_schema = create_deny_effect_schema();
    let audit_schema = create_audit_effect_schema();
    let modify_schema = create_modify_effect_schema();

    // Use highly unique names to avoid conflicts
    let deny_name = "azure.policy.deny.global.test";
    let audit_name = "azure.policy.audit.global.test";
    let modify_name = "azure.policy.modify.global.test";

    assert!(effect::register(deny_name, deny_schema).is_ok());
    assert!(effect::register(audit_name, audit_schema).is_ok());
    assert!(effect::register(modify_name, modify_schema).is_ok());

    // Verify all are registered in global registry
    assert!(effect::contains(deny_name));
    assert!(effect::contains(audit_name));
    assert!(effect::contains(modify_name));

    // Test retrieval from global registry
    let retrieved_deny = effect::get(deny_name);
    let retrieved_audit = effect::get(audit_name);
    let retrieved_modify = effect::get(modify_name);

    assert!(retrieved_deny.is_some());
    assert!(retrieved_audit.is_some());
    assert!(retrieved_modify.is_some());
}

#[test]
fn test_effect_schema_validation_patterns() {
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

    let result = EFFECT_SCHEMA_REGISTRY.register("azure.policy.complex.patterns", schema_rc);
    assert!(result.is_ok());
    assert!(EFFECT_SCHEMA_REGISTRY.contains("azure.policy.complex.patterns"));
}

#[test]
fn test_effect_schema_with_invalid_names() {
    let effect_schema = create_effect_schema();

    // Test invalid names
    assert!(EFFECT_SCHEMA_REGISTRY
        .register("", effect_schema.clone())
        .is_err());
    assert!(EFFECT_SCHEMA_REGISTRY
        .register("   ", effect_schema.clone())
        .is_err());
    assert!(EFFECT_SCHEMA_REGISTRY
        .register("\t", effect_schema.clone())
        .is_err());
    assert!(EFFECT_SCHEMA_REGISTRY
        .register("\n", effect_schema)
        .is_err());
}

#[test]
fn test_effect_schema_duplicate_registration() {
    let deny_schema = create_deny_effect_schema();

    // First registration should succeed
    assert!(EFFECT_SCHEMA_REGISTRY
        .register("azure.policy.deny.duplicate", deny_schema.clone())
        .is_ok());

    // Duplicate registration should fail
    let duplicate_result =
        EFFECT_SCHEMA_REGISTRY.register("azure.policy.deny.duplicate", deny_schema);
    assert!(duplicate_result.is_err());

    // Verify error type
    match duplicate_result.unwrap_err() {
        SchemaRegistryError::AlreadyExists { name, .. } => {
            assert_eq!(name.as_ref(), "azure.policy.deny.duplicate");
        }
        _ => panic!("Expected AlreadyExists error"),
    }
}

#[test]
fn test_azure_policy_effect_removal() {
    // Register multiple Azure Policy effects with unique names
    let effects = vec![
        ("azure.policy.deny.removal", create_deny_effect_schema()),
        ("azure.policy.audit.removal", create_audit_effect_schema()),
        ("azure.policy.modify.removal", create_modify_effect_schema()),
    ];

    for (name, schema) in &effects {
        assert!(EFFECT_SCHEMA_REGISTRY
            .register(*name, schema.clone())
            .is_ok());
    }

    // Remove one effect
    let removed = EFFECT_SCHEMA_REGISTRY.remove("azure.policy.audit.removal");
    assert!(removed.is_some());
    assert!(!EFFECT_SCHEMA_REGISTRY.contains("azure.policy.audit.removal"));

    // Verify the removed schema is correct
    let removed_schema = removed.unwrap();
    assert!(Rc::ptr_eq(&effects[1].1, &removed_schema));

    // Other effects should still be present
    assert!(EFFECT_SCHEMA_REGISTRY.contains("azure.policy.deny.removal"));
    assert!(EFFECT_SCHEMA_REGISTRY.contains("azure.policy.modify.removal"));
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_effect_schema_access() {
    use std::sync::Barrier;
    use std::thread;

    let barrier = Rc::new(Barrier::new(3));
    let mut handles = vec![];

    // Test concurrent registration of different Azure Policy effects
    let effects = [
        "concurrent_effect_schema_access.deny",
        "concurrent_effect_schema_access.audit",
        "concurrent_effect_schema_access.modify",
    ];

    for (i, effect_name) in effects.iter().enumerate() {
        let barrier = Rc::clone(&barrier);
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
                EFFECT_SCHEMA_REGISTRY.register(name, schema)
            });

        handles.push(handle);
    }

    // Wait for all threads to complete
    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

    // All registrations should succeed
    for result in results {
        assert!(result.is_ok());
    }

    // Should have effect schemas registered
    assert!(EFFECT_SCHEMA_REGISTRY.contains("concurrent_effect_schema_access.deny"));
    assert!(EFFECT_SCHEMA_REGISTRY.contains("concurrent_effect_schema_access.audit"));
    assert!(EFFECT_SCHEMA_REGISTRY.contains("concurrent_effect_schema_access.modify"));
}
