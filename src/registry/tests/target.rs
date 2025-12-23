// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::panic,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::unreachable,
    clippy::assertions_on_result_states,
    clippy::pattern_type_mismatch
)] // registry target tests unwrap/panic for expectations

use super::super::registry::*;
use crate::{
    registry::{instances::TARGET_REGISTRY, targets},
    target::{Target, TargetError},
    *,
};
use serde_json::json;

type String = Rc<str>;
type TargetRegistryError = RegistryError;

// Helper function to create a basic test target
fn create_basic_target(name: &str) -> Rc<Target> {
    let target_json = json!({
        "name": name,
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
            }
        ],
        "effects": {
            "allow": { "type": "boolean" },
            "deny": { "type": "boolean" }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();
    Rc::new(target)
}

// Helper function to create an Azure resource target
fn create_azure_target(name: &str) -> Rc<Target> {
    let target_json = json!({
        "name": name,
        "description": "Target for Azure resource policies",
        "version": "2.0.0",
        "resource_schema_selector": "type",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "type": { "const": "Microsoft.Compute/virtualMachines" },
                    "name": { "type": "string" },
                    "location": { "type": "string" },
                    "properties": {
                        "type": "object",
                        "properties": {
                            "hardwareProfile": {
                                "type": "object",
                                "properties": {
                                    "vmSize": { "type": "string" }
                                }
                            }
                        }
                    }
                },
                "required": ["type", "name", "location"]
            },
            {
                "type": "object",
                "properties": {
                    "type": { "const": "Microsoft.Storage/storageAccounts" },
                    "name": { "type": "string" },
                    "location": { "type": "string" },
                    "sku": {
                        "type": "object",
                        "properties": {
                            "name": { "type": "string" }
                        }
                    }
                },
                "required": ["type", "name", "location", "sku"]
            }
        ],
        "effects": {
            "allow": { "type": "boolean" },
            "deny": { "type": "boolean" },
            "audit": { "type": "string" }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();
    Rc::new(target)
}

// Helper function to create a Kubernetes target
fn create_kubernetes_target(name: &str) -> Rc<Target> {
    let target_json = json!({
        "name": name,
        "description": "Target for Kubernetes resource policies",
        "version": "1.2.0",
        "resource_schema_selector": "kind",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "apiVersion": { "type": "string" },
                    "kind": { "const": "Pod" },
                    "metadata": {
                        "type": "object",
                        "properties": {
                            "name": { "type": "string" },
                            "namespace": { "type": "string" }
                        },
                        "required": ["name"]
                    },
                    "spec": {
                        "type": "object",
                        "properties": {
                            "containers": {
                                "type": "array",
                                "items": {
                                    "type": "object",
                                    "properties": {
                                        "name": { "type": "string" },
                                        "image": { "type": "string" }
                                    },
                                    "required": ["name", "image"]
                                }
                            }
                        },
                        "required": ["containers"]
                    }
                },
                "required": ["apiVersion", "kind", "metadata", "spec"]
            },
            {
                "type": "object",
                "properties": {
                    "apiVersion": { "type": "string" },
                    "kind": { "const": "Service" },
                    "metadata": {
                        "type": "object",
                        "properties": {
                            "name": { "type": "string" },
                            "namespace": { "type": "string" }
                        },
                        "required": ["name"]
                    },
                    "spec": {
                        "type": "object",
                        "properties": {
                            "selector": { "type": "object" },
                            "ports": {
                                "type": "array",
                                "items": {
                                    "type": "object",
                                    "properties": {
                                        "port": { "type": "integer" },
                                        "targetPort": { "type": "integer" }
                                    },
                                    "required": ["port"]
                                }
                            }
                        }
                    }
                },
                "required": ["apiVersion", "kind", "metadata", "spec"]
            }
        ],
        "effects": {
            "allow": { "type": "boolean" },
            "deny": { "type": "boolean" },
            "warn": { "type": "string" }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();
    Rc::new(target)
}

// Helper function to create a generic API target
fn create_api_target(name: &str) -> Rc<Target> {
    let target_json = json!({
        "name": name,
        "description": "Target for API Gateway policies",
        "version": "3.1.0",
        "resource_schema_selector": "operation",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "operation": { "const": "GET" },
                    "path": { "type": "string" },
                    "headers": { "type": "object" },
                    "queryParams": { "type": "object" }
                },
                "required": ["operation", "path"]
            },
            {
                "type": "object",
                "properties": {
                    "operation": { "const": "POST" },
                    "path": { "type": "string" },
                    "headers": { "type": "object" },
                    "body": { "type": "object" }
                },
                "required": ["operation", "path", "body"]
            }
        ],
        "effects": {
            "allow": { "type": "boolean" },
            "deny": { "type": "boolean" },
            "rate_limit": {
                "type": "object",
                "properties": {
                    "requests_per_minute": { "type": "integer" }
                }
            }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();
    Rc::new(target)
}

// Helper function to create a Microsoft Graph API target
fn create_msgraph_target(name: &str) -> Rc<Target> {
    let target_json = json!({
        "name": name,
        "description": "Target for Microsoft Graph API policies",
        "version": "1.0.0",
        "resource_schema_selector": "@odata.type",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "@odata.type": { "const": "#microsoft.graph.user" },
                    "id": { "type": "string" },
                    "userPrincipalName": {
                        "type": "string",
                        "pattern": "^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}$"
                    },
                    "displayName": { "type": "string" },
                    "givenName": { "type": "string" },
                    "surname": { "type": "string" },
                    "mail": {
                        "type": "string",
                        "pattern": "^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}$"
                    },
                    "jobTitle": { "type": "string" },
                    "department": { "type": "string" },
                    "accountEnabled": { "type": "boolean" },
                    "assignedLicenses": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "skuId": { "type": "string" },
                                "disabledPlans": {
                                    "type": "array",
                                    "items": { "type": "string" }
                                }
                            }
                        }
                    }
                },
                "required": ["@odata.type", "id", "userPrincipalName"]
            },
            {
                "type": "object",
                "properties": {
                    "@odata.type": { "const": "#microsoft.graph.group" },
                    "id": { "type": "string" },
                    "displayName": { "type": "string" },
                    "description": { "type": "string" },
                    "groupTypes": {
                        "type": "array",
                        "items": {
                            "enum": ["Unified", "DynamicMembership"]
                        }
                    },
                    "mailEnabled": { "type": "boolean" },
                    "securityEnabled": { "type": "boolean" },
                    "mail": { "type": "string" },
                    "visibility": {
                        "enum": ["Private", "Public", "HiddenMembership"]
                    },
                    "members": {
                        "type": "array",
                        "items": { "type": "string" }
                    }
                },
                "required": ["@odata.type", "id", "displayName"]
            },
            {
                "type": "object",
                "properties": {
                    "@odata.type": { "const": "#microsoft.graph.application" },
                    "id": { "type": "string" },
                    "appId": { "type": "string" },
                    "displayName": { "type": "string" },
                    "publisherDomain": { "type": "string" },
                    "signInAudience": {
                        "enum": ["AzureADMyOrg", "AzureADMultipleOrgs", "AzureADandPersonalMicrosoftAccount", "PersonalMicrosoftAccount"]
                    },
                    "requiredResourceAccess": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "resourceAppId": { "type": "string" },
                                "resourceAccess": {
                                    "type": "array",
                                    "items": {
                                        "type": "object",
                                        "properties": {
                                            "id": { "type": "string" },
                                            "type": {
                                                "enum": ["Scope", "Role"]
                                            }
                                        },
                                        "required": ["id", "type"]
                                    }
                                }
                            },
                            "required": ["resourceAppId", "resourceAccess"]
                        }
                    }
                },
                "required": ["@odata.type", "id", "appId", "displayName"]
            },
            {
                "type": "object",
                "properties": {
                    "@odata.type": { "const": "#microsoft.graph.device" },
                    "id": { "type": "string" },
                    "deviceId": { "type": "string" },
                    "displayName": { "type": "string" },
                    "operatingSystem": { "type": "string" },
                    "operatingSystemVersion": { "type": "string" },
                    "isCompliant": { "type": "boolean" },
                    "isManaged": { "type": "boolean" },
                    "trustType": {
                        "enum": ["Workplace", "AzureAd", "ServerAd"]
                    },
                    "registrationDateTime": {
                        "type": "string"
                    }
                },
                "required": ["@odata.type", "id", "deviceId", "displayName"]
            }
        ],
        "effects": {
            "allow": { "type": "boolean" },
            "deny": { "type": "boolean" },
            "audit": {
                "type": "object",
                "properties": {
                    "level": {
                        "enum": ["info", "warning", "error"]
                    },
                    "message": { "type": "string" }
                },
                "required": ["level", "message"]
            },
            "conditional_access": {
                "type": "object",
                "properties": {
                    "requireMFA": { "type": "boolean" },
                    "requireCompliantDevice": { "type": "boolean" },
                    "allowedLocations": {
                        "type": "array",
                        "items": { "type": "string" }
                    }
                }
            }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();
    Rc::new(target)
}

// Helper function to create an Azure relationship policies target
fn create_azure_relationship_policies_target(name: &str) -> Rc<Target> {
    let target_json = json!({
        "name": name,
        "description": "Target for Azure resource relationship policies based on immutable and common properties",
        "version": "1.0.0",
        "resource_schema_selector": "type",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "type": { "type": "string" },
                    "id": { "type": "string" },
                    "name": { "type": "string" },
                    "location": { "type": "string" },
                    "resourceGroup": { "type": "string" },
                    "subscriptionId": { "type": "string" },
                    "tenantId": { "type": "string" },
                    "tags": {
                        "type": "object",
                        "additionalProperties": { "type": "string" }
                    },
                    "properties": {
                        "type": "object",
                        "properties": {
                            "provisioningState": { "type": "string" },
                            "resourceGuid": { "type": "string" },
                            "creationTime": { "type": "string" },
                            "timeCreated": { "type": "string" }
                        }
                    },
                    "managedBy": { "type": "string" },
                },
                "required": ["type", "id", "name", "location", "resourceGroup", "subscriptionId"],
                "description": "Universal Azure resource schema for relationship policies based on common immutable properties"
            }
        ],
        "effects": {
            "manage": {
                "anyOf": [
                    { "type": "boolean" },
                    {
                        "type": "object",
                        "properties": {
                            "target": { "type": "string" }
                        },
                        "required": ["target"],
                        "additionalProperties": false
                    }
                ]
            }
        }
    });

    let target = Target::from_json_str(&target_json.to_string()).unwrap();
    Rc::new(target)
}

#[test]
fn test_basic_target_registration() {
    let target = create_basic_target("basic.test.target");

    // Test registration of basic target
    let result = TARGET_REGISTRY.register("basic.test.target", target.clone());
    assert!(result.is_ok());
    assert!(TARGET_REGISTRY.contains("basic.test.target"));

    // Verify target can be retrieved
    let retrieved = TARGET_REGISTRY.get("basic.test.target");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&target, &retrieved.unwrap()));
}

#[test]
fn test_azure_target_registration() {
    let azure_target = create_azure_target("azure.compute.target");

    // Test registration of Azure target
    let result = TARGET_REGISTRY.register("azure.compute.target", azure_target.clone());
    assert!(result.is_ok());
    assert!(TARGET_REGISTRY.contains("azure.compute.target"));

    // Verify target structure
    let retrieved = TARGET_REGISTRY.get("azure.compute.target");
    assert!(retrieved.is_some());
    let target = retrieved.unwrap();

    assert_eq!(target.name.as_ref(), "azure.compute.target");
    assert_eq!(target.version.as_ref(), "2.0.0");
    assert_eq!(target.resource_schema_selector.as_ref(), "type");
    assert_eq!(target.resource_schemas.len(), 2);
    assert_eq!(target.effects.len(), 3);

    // Verify lookup table was populated
    assert_eq!(target.resource_schema_lookup.len(), 2);
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("Microsoft.Compute/virtualMachines".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("Microsoft.Storage/storageAccounts".into())));

    // Verify pointer equality
    assert!(Rc::ptr_eq(&azure_target, &target));
}

#[test]
fn test_kubernetes_target_registration() {
    let k8s_target = create_kubernetes_target("kubernetes.resources.target");

    // Test registration of Kubernetes target
    let result = TARGET_REGISTRY.register("kubernetes.resources.target", k8s_target.clone());
    assert!(result.is_ok());
    assert!(TARGET_REGISTRY.contains("kubernetes.resources.target"));

    // Verify target structure
    let retrieved = TARGET_REGISTRY.get("kubernetes.resources.target");
    assert!(retrieved.is_some());
    let target = retrieved.unwrap();

    assert_eq!(target.name.as_ref(), "kubernetes.resources.target");
    assert_eq!(target.version.as_ref(), "1.2.0");
    assert_eq!(target.resource_schema_selector.as_ref(), "kind");
    assert_eq!(target.resource_schemas.len(), 2);
    assert_eq!(target.effects.len(), 3);

    // Verify lookup table was populated for Kubernetes kinds
    assert_eq!(target.resource_schema_lookup.len(), 2);
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("Pod".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("Service".into())));

    // Verify pointer equality
    assert!(Rc::ptr_eq(&k8s_target, &target));
}

#[test]
fn test_api_target_registration() {
    let api_target = create_api_target("api.gateway.target");

    // Test registration of API target
    let result = TARGET_REGISTRY.register("api.gateway.target", api_target.clone());
    assert!(result.is_ok());
    assert!(TARGET_REGISTRY.contains("api.gateway.target"));

    // Verify target structure
    let retrieved = TARGET_REGISTRY.get("api.gateway.target");
    assert!(retrieved.is_some());
    let target = retrieved.unwrap();

    assert_eq!(target.name.as_ref(), "api.gateway.target");
    assert_eq!(target.version.as_ref(), "3.1.0");
    assert_eq!(target.resource_schema_selector.as_ref(), "operation");
    assert_eq!(target.resource_schemas.len(), 2);
    assert_eq!(target.effects.len(), 3);

    // Verify lookup table was populated for HTTP operations
    assert_eq!(target.resource_schema_lookup.len(), 2);
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("GET".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("POST".into())));

    // Verify pointer equality
    assert!(Rc::ptr_eq(&api_target, &target));
}

#[test]
fn test_multiple_target_registration() {
    // Register multiple targets with unique names
    let basic_name = "multi.basic.target";
    let azure_name = "multi.azure.target";
    let k8s_name = "multi.kubernetes.target";
    let api_name = "multi.api.target";

    let basic_target = create_basic_target(basic_name);
    let azure_target = create_azure_target(azure_name);
    let k8s_target = create_kubernetes_target(k8s_name);
    let api_target = create_api_target(api_name);

    assert!(TARGET_REGISTRY.register(basic_name, basic_target).is_ok());
    assert!(TARGET_REGISTRY.register(azure_name, azure_target).is_ok());
    assert!(TARGET_REGISTRY.register(k8s_name, k8s_target).is_ok());
    assert!(TARGET_REGISTRY.register(api_name, api_target).is_ok());

    // Verify all are registered
    assert!(TARGET_REGISTRY.contains(basic_name));
    assert!(TARGET_REGISTRY.contains(azure_name));
    assert!(TARGET_REGISTRY.contains(k8s_name));
    assert!(TARGET_REGISTRY.contains(api_name));

    // Verify they can all be retrieved
    assert!(TARGET_REGISTRY.get(basic_name).is_some());
    assert!(TARGET_REGISTRY.get(azure_name).is_some());
    assert!(TARGET_REGISTRY.get(k8s_name).is_some());
    assert!(TARGET_REGISTRY.get(api_name).is_some());
}

#[test]
fn test_global_target_registry() {
    // Register targets using global helper functions
    let basic_name = "global.basic.target";
    let azure_name = "global.azure.target";
    let k8s_name = "global.kubernetes.target";
    let api_name = "global.api.target";

    let basic_target = create_basic_target(basic_name);
    let azure_target = create_azure_target(azure_name);
    let k8s_target = create_kubernetes_target(k8s_name);
    let api_target = create_api_target(api_name);

    assert!(targets::register(basic_target.clone()).is_ok());
    assert!(targets::register(azure_target.clone()).is_ok());
    assert!(targets::register(k8s_target.clone()).is_ok());
    assert!(targets::register(api_target.clone()).is_ok());

    // Verify all are registered in global registry
    assert!(targets::contains(basic_name));
    assert!(targets::contains(azure_name));
    assert!(targets::contains(k8s_name));
    assert!(targets::contains(api_name));

    // Test retrieval from global registry
    let retrieved_basic = targets::get(basic_name);
    let retrieved_azure = targets::get(azure_name);
    let retrieved_k8s = targets::get(k8s_name);
    let retrieved_api = targets::get(api_name);

    assert!(retrieved_basic.is_some());
    assert!(retrieved_azure.is_some());
    assert!(retrieved_k8s.is_some());
    assert!(retrieved_api.is_some());

    // Verify pointer equality
    assert!(Rc::ptr_eq(&basic_target, &retrieved_basic.unwrap()));
    assert!(Rc::ptr_eq(&azure_target, &retrieved_azure.unwrap()));
    assert!(Rc::ptr_eq(&k8s_target, &retrieved_k8s.unwrap()));
    assert!(Rc::ptr_eq(&api_target, &retrieved_api.unwrap()));
}

#[test]
fn test_target_with_invalid_names() {
    let target = create_basic_target("invalid.test.target");

    // Test invalid names
    assert!(TARGET_REGISTRY.register("", target.clone()).is_err());
    assert!(TARGET_REGISTRY.register("   ", target.clone()).is_err());
    assert!(TARGET_REGISTRY.register("\t", target.clone()).is_err());
    assert!(TARGET_REGISTRY.register("\n", target).is_err());
}

#[test]
fn test_target_duplicate_registration() {
    let target = create_basic_target("duplicate.target.test");

    // First registration should succeed
    assert!(TARGET_REGISTRY
        .register("duplicate.target.test", target.clone())
        .is_ok());

    // Duplicate registration should fail
    let duplicate_result = TARGET_REGISTRY.register("duplicate.target.test", target);
    assert!(duplicate_result.is_err());

    // Verify error type
    match duplicate_result.unwrap_err() {
        TargetRegistryError::AlreadyExists { name, .. } => {
            assert_eq!(name.as_ref(), "duplicate.target.test");
        }
        _ => panic!("Expected AlreadyExists error"),
    }
}

#[test]
fn test_target_removal() {
    // Register multiple targets with unique names
    let targets = vec![
        (
            "removal.basic.target",
            create_basic_target("removal.basic.target"),
        ),
        (
            "removal.azure.target",
            create_azure_target("removal.azure.target"),
        ),
        (
            "removal.kubernetes.target",
            create_kubernetes_target("removal.kubernetes.target"),
        ),
        (
            "removal.api.target",
            create_api_target("removal.api.target"),
        ),
    ];

    for (name, target) in &targets {
        assert!(TARGET_REGISTRY.register(*name, target.clone()).is_ok());
    }

    // Remove one target
    let removed = TARGET_REGISTRY.remove("removal.azure.target");
    assert!(removed.is_some());
    assert!(!TARGET_REGISTRY.contains("removal.azure.target"));

    // Verify the removed target is correct
    let removed_target = removed.unwrap();
    assert!(Rc::ptr_eq(&targets[1].1, &removed_target));

    // Other targets should still be present
    assert!(TARGET_REGISTRY.contains("removal.basic.target"));
    assert!(TARGET_REGISTRY.contains("removal.kubernetes.target"));
    assert!(TARGET_REGISTRY.contains("removal.api.target"));
}

#[test]
fn test_target_list_operations() {
    // Register targets with predictable names
    let target_names = vec![
        "list.ops.basic",
        "list.ops.azure",
        "list.ops.kubernetes",
        "list.ops.api",
    ];

    let basic_target = create_basic_target("list.ops.basic");

    // Register all targets
    for name in &target_names {
        assert!(TARGET_REGISTRY
            .register(*name, basic_target.clone())
            .is_ok());
    }

    // Test list_names()
    let names = TARGET_REGISTRY.list_names();
    for expected_name in &target_names {
        assert!(
            names.contains(&(*expected_name).into()),
            "Name list missing {expected_name}"
        );
    }

    // Test len()
    let initial_len = TARGET_REGISTRY.len();
    assert!(initial_len >= target_names.len());

    // Test is_empty() - should be false since we have targets
    assert!(!TARGET_REGISTRY.is_empty());

    // Test iter()
    let mut found_count = 0;
    for (name, _target) in TARGET_REGISTRY.iter() {
        if target_names.contains(&name.as_ref()) {
            found_count += 1;
        }
    }
    assert_eq!(found_count, target_names.len());

    // Test list_items()
    let items = TARGET_REGISTRY.list_items();
    assert!(items.len() >= target_names.len());
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_target_access() {
    use std::sync::Barrier;
    use std::thread;

    let barrier = Rc::new(Barrier::new(4));
    let mut handles = vec![];

    // Test concurrent registration of different targets
    let target_names = [
        "concurrent.basic.target",
        "concurrent.azure.target",
        "concurrent.kubernetes.target",
        "concurrent.api.target",
    ];

    for (i, target_name) in target_names.iter().enumerate() {
        let barrier = Rc::clone(&barrier);
        let name: String = (*target_name).into();

        let handle: thread::JoinHandle<Result<(), TargetRegistryError>> =
            thread::spawn(move || {
                let target = match i {
                    0 => create_basic_target(&name),
                    1 => create_azure_target(&name),
                    2 => create_kubernetes_target(&name),
                    3 => create_api_target(&name),
                    _ => unreachable!(),
                };

                barrier.wait();
                TARGET_REGISTRY.register(name, target)
            });

        handles.push(handle);
    }

    // Wait for all threads to complete
    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

    // All registrations should succeed
    for result in results {
        assert!(result.is_ok());
    }

    // All targets should be registered
    assert!(TARGET_REGISTRY.contains("concurrent.basic.target"));
    assert!(TARGET_REGISTRY.contains("concurrent.azure.target"));
    assert!(TARGET_REGISTRY.contains("concurrent.kubernetes.target"));
    assert!(TARGET_REGISTRY.contains("concurrent.api.target"));
}

#[test]
fn test_target_versioning() {
    // Test targets with different versions
    let v1_target_json = json!({
        "name": "versioned_target",
        "description": "Version 1.0 of the target",
        "version": "1.0.0",
        "resource_schema_selector": "type",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "type": { "const": "user" },
                    "name": { "type": "string" }
                },
                "required": ["type", "name"]
            }
        ],
        "effects": {
            "allow": { "type": "boolean" }
        }
    });

    let v2_target_json = json!({
        "name": "versioned_target",
        "description": "Version 2.0 of the target with enhanced features",
        "version": "2.0.0",
        "resource_schema_selector": "type",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "type": { "const": "user" },
                    "name": { "type": "string" },
                    "email": { "type": "string" }
                },
                "required": ["type", "name", "email"]
            },
            {
                "type": "object",
                "properties": {
                    "type": { "const": "group" },
                    "name": { "type": "string" },
                    "members": {
                        "type": "array",
                        "items": { "type": "string" }
                    }
                },
                "required": ["type", "name"]
            }
        ],
        "effects": {
            "allow": { "type": "boolean" },
            "deny": { "type": "boolean" },
            "audit": { "type": "string" }
        }
    });

    let v1_target = Rc::new(Target::from_json_str(&v1_target_json.to_string()).unwrap());
    let v2_target = Rc::new(Target::from_json_str(&v2_target_json.to_string()).unwrap());

    // Register different versions
    assert!(TARGET_REGISTRY
        .register("versioned.target.v1", v1_target.clone())
        .is_ok());
    assert!(TARGET_REGISTRY
        .register("versioned.target.v2", v2_target.clone())
        .is_ok());

    // Verify both versions are registered
    assert!(TARGET_REGISTRY.contains("versioned.target.v1"));
    assert!(TARGET_REGISTRY.contains("versioned.target.v2"));

    // Verify version differences
    let retrieved_v1 = TARGET_REGISTRY.get("versioned.target.v1").unwrap();
    let retrieved_v2 = TARGET_REGISTRY.get("versioned.target.v2").unwrap();

    assert_eq!(retrieved_v1.version.as_ref(), "1.0.0");
    assert_eq!(retrieved_v2.version.as_ref(), "2.0.0");

    assert_eq!(retrieved_v1.resource_schemas.len(), 1);
    assert_eq!(retrieved_v2.resource_schemas.len(), 2);

    assert_eq!(retrieved_v1.effects.len(), 1);
    assert_eq!(retrieved_v2.effects.len(), 3);
}

#[test]
fn test_target_domain_specific_patterns() {
    // Test targets for different domains with specific naming patterns
    let domain_targets = vec![
        "finance.trading.target",
        "healthcare.patient.target",
        "retail.inventory.target",
        "gaming.player.target",
        "education.student.target",
        "iot.device.target",
    ];

    let basic_target = create_basic_target("domain.specific.target");

    // Register all domain targets
    for domain_target in &domain_targets {
        let result = TARGET_REGISTRY.register(*domain_target, basic_target.clone());
        assert!(result.is_ok(), "Failed to register {domain_target}");
    }

    // Verify all are registered
    for domain_target in &domain_targets {
        assert!(
            TARGET_REGISTRY.contains(domain_target),
            "Missing {domain_target}"
        );
        assert!(
            TARGET_REGISTRY.get(domain_target).is_some(),
            "Cannot retrieve {domain_target}"
        );
    }

    // Verify list contains all domains
    let names = TARGET_REGISTRY.list_names();
    for domain_target in &domain_targets {
        assert!(
            names.contains(&(*domain_target).into()),
            "Name list missing {domain_target}"
        );
    }
}

#[test]
fn test_microsoft_graph_target() {
    let msgraph_target = create_msgraph_target("microsoft.graph.api.target");

    // Test registration of Microsoft Graph target
    let result = TARGET_REGISTRY.register("microsoft.graph.api.target", msgraph_target.clone());
    assert!(result.is_ok());
    assert!(TARGET_REGISTRY.contains("microsoft.graph.api.target"));

    // Verify target structure
    let retrieved = TARGET_REGISTRY.get("microsoft.graph.api.target");
    assert!(retrieved.is_some());
    let target = retrieved.unwrap();

    assert_eq!(target.name.as_ref(), "microsoft.graph.api.target");
    assert_eq!(target.version.as_ref(), "1.0.0");
    assert_eq!(target.resource_schema_selector.as_ref(), "@odata.type");
    assert_eq!(target.resource_schemas.len(), 4);
    assert_eq!(target.effects.len(), 4);

    // Verify lookup table was populated for Microsoft Graph entities
    assert_eq!(target.resource_schema_lookup.len(), 4);
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.user".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.group".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.application".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.device".into())));

    // Verify no default schema (all have discriminator)
    assert!(target.default_resource_schema.is_none());

    // Verify pointer equality
    assert!(Rc::ptr_eq(&msgraph_target, &target));

    // Test that all expected Microsoft Graph entity types are present
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.user".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.group".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.application".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.device".into())));
}

#[test]
fn test_microsoft_graph_with_global_registry() {
    // Test registration using global helper functions
    let target_name = "global.msgraph.target";
    let msgraph_target = create_msgraph_target(target_name);
    assert!(targets::register(msgraph_target.clone()).is_ok());

    // Verify registration in global registry
    assert!(targets::contains(target_name));

    // Test retrieval from global registry
    let retrieved = targets::get(target_name);
    assert!(retrieved.is_some());

    let target = retrieved.unwrap();
    assert_eq!(target.name.as_ref(), target_name);
    assert_eq!(target.resource_schema_selector.as_ref(), "@odata.type");

    // Verify Microsoft Graph specific schemas are present
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.user".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.group".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.application".into())));
    assert!(target
        .resource_schema_lookup
        .contains_key(&Value::String("#microsoft.graph.device".into())));

    // Verify effects include conditional access policies
    assert!(target.effects.contains_key("conditional_access"));
    assert!(target.effects.contains_key("audit"));

    // Verify pointer equality
    assert!(Rc::ptr_eq(&msgraph_target, &target));
}

#[test]
fn test_microsoft_graph_concurrent_access() {
    use std::sync::Barrier;
    use std::thread;

    let barrier = Rc::new(Barrier::new(2));
    let mut handles = vec![];

    // Test concurrent registration of Microsoft Graph targets
    let target_names = ["concurrent.msgraph.users", "concurrent.msgraph.apps"];

    for target_name in target_names.iter() {
        let barrier = Rc::clone(&barrier);
        let name: String = (*target_name).into();

        let handle: thread::JoinHandle<Result<(), TargetRegistryError>> =
            thread::spawn(move || {
                let target = create_msgraph_target(&name);
                barrier.wait();
                TARGET_REGISTRY.register(name, target)
            });

        handles.push(handle);
    }

    // Wait for all threads to complete
    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

    // All registrations should succeed
    for result in results {
        assert!(result.is_ok());
    }

    // Both Microsoft Graph targets should be registered
    assert!(TARGET_REGISTRY.contains("concurrent.msgraph.users"));
    assert!(TARGET_REGISTRY.contains("concurrent.msgraph.apps"));

    // Verify both targets have the expected structure
    for target_name in &target_names {
        let target = TARGET_REGISTRY.get(target_name).unwrap();
        assert_eq!(target.name.as_ref(), *target_name);
        assert_eq!(target.resource_schemas.len(), 4);
        assert_eq!(target.resource_schema_lookup.len(), 4);
    }
}

#[test]
fn test_azure_relationship_policies_target() {
    let azure_target =
        create_azure_relationship_policies_target("azure.relationship.policies.target");

    // Test registration of Azure relationship policies target
    let result =
        TARGET_REGISTRY.register("azure.relationship.policies.target", azure_target.clone());
    assert!(result.is_ok());
    assert!(TARGET_REGISTRY.contains("azure.relationship.policies.target"));

    // Verify target structure
    let retrieved = TARGET_REGISTRY.get("azure.relationship.policies.target");
    assert!(retrieved.is_some());
    let target = retrieved.unwrap();

    assert_eq!(target.name.as_ref(), "azure.relationship.policies.target");
    assert_eq!(target.version.as_ref(), "1.0.0");
    assert_eq!(target.resource_schema_selector.as_ref(), "type");
    assert_eq!(target.resource_schemas.len(), 1); // Single universal schema
    assert_eq!(target.effects.len(), 1); // Only "manage" effect

    // Verify universal schema covers all Azure resource types
    assert!(target.default_resource_schema.is_some());

    // Verify "manage" effect structure
    assert!(target.effects.contains_key("manage"));

    // Verify pointer equality
    assert!(Rc::ptr_eq(&azure_target, &target));
}

#[test]
fn test_azure_relationship_policies_with_global_registry() {
    // Test registration using global helper functions
    let target_name = "global.azure.relationship.policies";
    let azure_target = create_azure_relationship_policies_target(target_name);
    assert!(targets::register(azure_target.clone()).is_ok());

    // Verify registration in global registry
    assert!(targets::contains(target_name));

    // Test retrieval from global registry
    let retrieved = targets::get(target_name);
    assert!(retrieved.is_some());

    let target = retrieved.unwrap();
    assert_eq!(target.name.as_ref(), "global.azure.relationship.policies");
    assert_eq!(target.resource_schema_selector.as_ref(), "type");

    // Verify universal schema approach - single schema for all Azure resources
    assert!(target.default_resource_schema.is_some());
    assert_eq!(target.resource_schemas.len(), 1);

    // Verify manage effect is present
    assert!(target.effects.contains_key("manage"));

    // Verify pointer equality
    assert!(Rc::ptr_eq(&azure_target, &target));
}

#[test]
fn test_azure_relationship_policies_manage_effect() {
    let azure_target =
        create_azure_relationship_policies_target("test.azure.relationship.policies");

    // Verify manage effect exists and is the only effect for relationship policies
    assert_eq!(azure_target.effects.len(), 1);
    assert!(azure_target.effects.contains_key("manage"));
}

#[test]
fn test_target_empty_resource_schemas() {
    // Create a target with empty resource schemas array - should fail validation
    let target_json = json!({
        "name": "empty_resource_schemas",
        "version": "1.0.0",
        "resource_schema_selector": "type",
        "resource_schemas": [],  // Empty array
        "effects": {
            "allow": {
                "type": "boolean"
            }
        }
    });

    // Target creation should fail due to empty resource schemas
    let result = Target::from_json_str(&target_json.to_string());
    assert!(result.is_err());

    match result.unwrap_err() {
        TargetError::EmptyResourceSchemas(msg) => {
            assert!(msg.contains("Target must have at least one resource schema defined"));
        }
        other => panic!("Expected EmptyResourceSchemas error, got: {:?}", other),
    }
}

#[test]
fn test_target_empty_effects() {
    // Create a target with empty effects - should fail validation
    let target_json = json!({
        "name": "empty_effects",
        "version": "1.0.0",
        "resource_schema_selector": "type",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "name": {"type": "string"}
                },
                "required": ["name"]
            }
        ],
        "effects": {}  // Empty object
    });

    // Target creation should fail due to empty effects
    let result = Target::from_json_str(&target_json.to_string());
    assert!(result.is_err());

    match result.unwrap_err() {
        TargetError::EmptyEffectSchemas(msg) => {
            assert!(msg.contains("Target must have at least one effect defined"));
        }
        other => panic!("Expected EmptyEffectSchemas error, got: {:?}", other),
    }
}

#[test]
fn test_target_single_schema_no_constant_selector() {
    // Create a target with one schema that doesn't have a constant property
    // matching the resource_schema_selector
    let target_json = json!({
        "name": "single_schema_no_constant",
        "version": "1.0.0",
        "resource_schema_selector": "type",
        "resource_schemas": [
            {
                "type": "object",
                "properties": {
                    "name": {"type": "string"},
                    "value": {"type": "string"},
                    "type": {"type": "string"}  // This is a regular property, not a constant
                },
                "required": ["name"]
            }
        ],
        "effects": {
            "allow": {
                "type": "boolean"
            }
        }
    });

    let target = Rc::new(Target::from_json_str(&target_json.to_string()).unwrap());

    // Test registration
    let result = TARGET_REGISTRY.register("single.schema.no.constant", target.clone());
    assert!(result.is_ok());

    // Verify target structure
    let retrieved = TARGET_REGISTRY.get("single.schema.no.constant").unwrap();
    assert_eq!(retrieved.name.as_ref(), "single_schema_no_constant");
    assert_eq!(retrieved.version.as_ref(), "1.0.0");
    assert_eq!(retrieved.resource_schema_selector.as_ref(), "type");
    assert_eq!(retrieved.resource_schemas.len(), 1);
    assert_eq!(retrieved.effects.len(), 1);

    // Since the schema doesn't have a constant property matching the selector,
    // it should become the default schema and the lookup table should be empty
    assert!(retrieved.default_resource_schema.is_some());
    assert!(retrieved.resource_schema_lookup.is_empty()); // No constant discriminator values

    // Verify pointer equality
    assert!(Rc::ptr_eq(&target, &retrieved));
}
