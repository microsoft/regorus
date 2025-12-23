// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::panic,
    clippy::unwrap_used,
    clippy::unreachable,
    clippy::indexing_slicing,
    clippy::assertions_on_result_states,
    clippy::pattern_type_mismatch
)] // registry resource tests unwrap/panic for fixture setup

use super::super::registry::*;
use crate::{
    registry::{instances::RESOURCE_SCHEMA_REGISTRY, schemas::resource},
    schema::Schema,
    *,
};
use serde_json::json;

type String = Rc<str>;
type SchemaRegistryError = RegistryError;

// Helper function to create a schema for Azure Resource types
fn create_resource_schema() -> Rc<Schema> {
    let schema_json = json!({
        "enum": ["Microsoft.Compute/virtualMachines", "Microsoft.Storage/storageAccounts", "Microsoft.Network/virtualNetworks"],
        "description": "Azure Resource types"
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    Rc::new(schema)
}

// Helper function to create a virtual machine resource schema
fn create_vm_resource_schema() -> Rc<Schema> {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "type": {
                "const": "Microsoft.Compute/virtualMachines"
            },
            "apiVersion": {
                "enum": ["2021-03-01", "2021-07-01", "2022-03-01"]
            },
            "name": {
                "type": "string",
                "pattern": "^[a-zA-Z0-9-._]{1,64}$"
            },
            "location": {
                "type": "string",
                "description": "Azure region where the VM will be deployed"
            },
            "properties": {
                "type": "object",
                "properties": {
                    "hardwareProfile": {
                        "type": "object",
                        "properties": {
                            "vmSize": {
                                "enum": ["Standard_B1s", "Standard_B2s", "Standard_D2s_v3", "Standard_D4s_v3"]
                            }
                        },
                        "required": ["vmSize"]
                    },
                    "osProfile": {
                        "type": "object",
                        "properties": {
                            "computerName": {
                                "type": "string"
                            },
                            "adminUsername": {
                                "type": "string"
                            }
                        },
                        "required": ["computerName", "adminUsername"]
                    }
                },
                "required": ["hardwareProfile", "osProfile"]
            }
        },
        "required": ["type", "apiVersion", "name", "location", "properties"],
        "description": "Schema for Azure Virtual Machine resources"
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    Rc::new(schema)
}

// Helper function to create a storage account resource schema
fn create_storage_resource_schema() -> Rc<Schema> {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "type": {
                "const": "Microsoft.Storage/storageAccounts"
            },
            "apiVersion": {
                "enum": ["2021-04-01", "2021-06-01", "2022-05-01"]
            },
            "name": {
                "type": "string",
                "pattern": "^[a-z0-9]{3,24}$"
            },
            "location": {
                "type": "string",
                "description": "Azure region for the storage account"
            },
            "sku": {
                "type": "object",
                "properties": {
                    "name": {
                        "enum": ["Standard_LRS", "Standard_GRS", "Standard_RAGRS", "Premium_LRS"]
                    }
                },
                "required": ["name"]
            },
            "kind": {
                "enum": ["Storage", "StorageV2", "BlobStorage", "FileStorage", "BlockBlobStorage"]
            },
            "properties": {
                "type": "object",
                "properties": {
                    "accessTier": {
                        "enum": ["Hot", "Cool"]
                    },
                    "encryption": {
                        "type": "object",
                        "properties": {
                            "services": {
                                "type": "object"
                            }
                        }
                    }
                }
            }
        },
        "required": ["type", "apiVersion", "name", "location", "sku", "kind"],
        "description": "Schema for Azure Storage Account resources"
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    Rc::new(schema)
}

// Helper function to create a network resource schema
fn create_network_resource_schema() -> Rc<Schema> {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "type": {
                "const": "Microsoft.Network/virtualNetworks"
            },
            "apiVersion": {
                "enum": ["2020-11-01", "2021-02-01", "2021-05-01"]
            },
            "name": {
                "type": "string",
                "pattern": "^[a-zA-Z0-9-._]{2,64}$"
            },
            "location": {
                "type": "string",
                "description": "Azure region for the virtual network"
            },
            "properties": {
                "type": "object",
                "properties": {
                    "addressSpace": {
                        "type": "object",
                        "properties": {
                            "addressPrefixes": {
                                "type": "array",
                                "items": {
                                    "type": "string",
                                    "pattern": "^(?:[0-9]{1,3}\\.){3}[0-9]{1,3}/[0-9]{1,2}$"
                                }
                            }
                        },
                        "required": ["addressPrefixes"]
                    },
                    "subnets": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "name": {
                                    "type": "string"
                                },
                                "properties": {
                                    "type": "object",
                                    "properties": {
                                        "addressPrefix": {
                                            "type": "string",
                                            "pattern": "^(?:[0-9]{1,3}\\.){3}[0-9]{1,3}/[0-9]{1,2}$"
                                        }
                                    },
                                    "required": ["addressPrefix"]
                                }
                            },
                            "required": ["name", "properties"]
                        }
                    }
                },
                "required": ["addressSpace"]
            }
        },
        "required": ["type", "apiVersion", "name", "location", "properties"],
        "description": "Schema for Azure Virtual Network resources"
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    Rc::new(schema)
}

#[test]
fn test_basic_resource_enum_schema() {
    let resource_schema = create_resource_schema();

    // Test registration of basic resource enum schema
    let result =
        RESOURCE_SCHEMA_REGISTRY.register("azure.resource.types.basic", resource_schema.clone());
    assert!(result.is_ok());
    assert!(RESOURCE_SCHEMA_REGISTRY.contains("azure.resource.types.basic"));

    // Verify schema can be retrieved
    let retrieved = RESOURCE_SCHEMA_REGISTRY.get("azure.resource.types.basic");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&resource_schema, &retrieved.unwrap()));
}

#[test]
fn test_vm_resource_schema() {
    let vm_schema = create_vm_resource_schema();

    // Test registration of VM resource schema
    let result = RESOURCE_SCHEMA_REGISTRY.register("azure.resource.vm.test", vm_schema.clone());
    assert!(result.is_ok());
    assert!(RESOURCE_SCHEMA_REGISTRY.contains("azure.resource.vm.test"));

    // Verify schema structure
    // Verify basic functionality - schema retrieval and pointer equality

    // The schema should be retrievable and be the same instance
    let retrieved = RESOURCE_SCHEMA_REGISTRY.get("azure.resource.vm.test");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&vm_schema, &retrieved.unwrap()));
}

#[test]
fn test_storage_resource_schema() {
    let storage_schema = create_storage_resource_schema();

    // Test registration of storage resource schema
    let result =
        RESOURCE_SCHEMA_REGISTRY.register("azure.resource.storage.test", storage_schema.clone());
    assert!(result.is_ok());
    assert!(RESOURCE_SCHEMA_REGISTRY.contains("azure.resource.storage.test"));

    // Verify basic functionality - schema retrieval and pointer equality

    // The schema should be retrievable and be the same instance
    let retrieved = RESOURCE_SCHEMA_REGISTRY.get("azure.resource.storage.test");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&storage_schema, &retrieved.unwrap()));
}

#[test]
fn test_network_resource_schema() {
    let network_schema = create_network_resource_schema();

    // Test registration of network resource schema
    let result =
        RESOURCE_SCHEMA_REGISTRY.register("azure.resource.network.test", network_schema.clone());
    assert!(result.is_ok());
    assert!(RESOURCE_SCHEMA_REGISTRY.contains("azure.resource.network.test"));

    // Verify basic functionality - schema retrieval and pointer equality

    // The schema should be retrievable and be the same instance
    let retrieved = RESOURCE_SCHEMA_REGISTRY.get("azure.resource.network.test");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&network_schema, &retrieved.unwrap()));
}

#[test]
fn test_multiple_resource_schemas() {
    // Register all resource schemas with unique names
    let vm_schema = create_vm_resource_schema();
    let storage_schema = create_storage_resource_schema();
    let network_schema = create_network_resource_schema();

    let vm_name = "azure.resource.vm.multiple";
    let storage_name = "azure.resource.storage.multiple";
    let network_name = "azure.resource.network.multiple";

    assert!(RESOURCE_SCHEMA_REGISTRY
        .register(vm_name, vm_schema)
        .is_ok());
    assert!(RESOURCE_SCHEMA_REGISTRY
        .register(storage_name, storage_schema)
        .is_ok());
    assert!(RESOURCE_SCHEMA_REGISTRY
        .register(network_name, network_schema)
        .is_ok());

    // Verify all are registered
    assert!(RESOURCE_SCHEMA_REGISTRY.contains(vm_name));
    assert!(RESOURCE_SCHEMA_REGISTRY.contains(storage_name));
    assert!(RESOURCE_SCHEMA_REGISTRY.contains(network_name));

    // Verify they can all be retrieved
    assert!(RESOURCE_SCHEMA_REGISTRY.get(vm_name).is_some());
    assert!(RESOURCE_SCHEMA_REGISTRY.get(storage_name).is_some());
    assert!(RESOURCE_SCHEMA_REGISTRY.get(network_name).is_some());
}

#[test]
fn test_global_resource_registry() {
    // Register Azure Resource schemas with unique names
    let vm_schema = create_vm_resource_schema();
    let storage_schema = create_storage_resource_schema();
    let network_schema = create_network_resource_schema();

    let vm_name = "azure.resource.vm.global";
    let storage_name = "azure.resource.storage.global";
    let network_name = "azure.resource.network.global";

    assert!(resource::register(vm_name, vm_schema.clone()).is_ok());
    assert!(resource::register(storage_name, storage_schema.clone()).is_ok());
    assert!(resource::register(network_name, network_schema.clone()).is_ok());

    // Verify all are registered in global registry
    assert!(resource::contains(vm_name));
    assert!(resource::contains(storage_name));
    assert!(resource::contains(network_name));

    // Test retrieval from global registry
    let retrieved_vm = resource::get(vm_name);
    let retrieved_storage = resource::get(storage_name);
    let retrieved_network = resource::get(network_name);

    assert!(retrieved_vm.is_some());
    assert!(retrieved_storage.is_some());
    assert!(retrieved_network.is_some());

    // Verify pointer equality
    assert!(Rc::ptr_eq(&vm_schema, &retrieved_vm.unwrap()));
    assert!(Rc::ptr_eq(&storage_schema, &retrieved_storage.unwrap()));
    assert!(Rc::ptr_eq(&network_schema, &retrieved_network.unwrap()));
}

#[test]
fn test_resource_schema_validation_patterns() {
    // Test schema with various Azure Resource patterns
    let complex_resource_schema = json!({
        "type": "object",
        "properties": {
            "resources": {
                "type": "array",
                "items": {
                    "type": "object",
                    "properties": {
                        "type": {
                            "type": "string",
                            "pattern": "^[a-zA-Z0-9]+\\.[a-zA-Z0-9]+/[a-zA-Z0-9]+$"
                        },
                        "apiVersion": {
                            "type": "string",
                            "pattern": "^[0-9]{4}-[0-9]{2}-[0-9]{2}$"
                        },
                        "name": {
                            "type": "string"
                        },
                        "location": {
                            "type": "string"
                        },
                        "dependsOn": {
                            "type": "array",
                            "items": {
                                "type": "string"
                            }
                        },
                        "tags": {
                            "type": "object",
                            "additionalProperties": {
                                "type": "string"
                            }
                        }
                    },
                    "required": ["type", "apiVersion", "name"]
                }
            },
            "parameters": {
                "type": "object"
            },
            "variables": {
                "type": "object"
            },
            "outputs": {
                "type": "object"
            }
        },
        "required": ["resources"],
        "description": "Comprehensive Azure Resource Manager template schema"
    });

    let schema = Schema::from_serde_json_value(complex_resource_schema).unwrap();
    let schema_rc = Rc::new(schema);

    let result =
        RESOURCE_SCHEMA_REGISTRY.register("azure.template.arm.patterns", schema_rc.clone());
    assert!(result.is_ok());
    assert!(RESOURCE_SCHEMA_REGISTRY.contains("azure.template.arm.patterns"));

    // Verify schema retrieval and pointer equality
    let retrieved = RESOURCE_SCHEMA_REGISTRY.get("azure.template.arm.patterns");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&schema_rc, &retrieved.unwrap()));
}

#[test]
fn test_resource_schema_with_invalid_names() {
    let resource_schema = create_resource_schema();

    // Test invalid names
    assert!(RESOURCE_SCHEMA_REGISTRY
        .register("", resource_schema.clone())
        .is_err());
    assert!(RESOURCE_SCHEMA_REGISTRY
        .register("   ", resource_schema.clone())
        .is_err());
    assert!(RESOURCE_SCHEMA_REGISTRY
        .register("\t", resource_schema.clone())
        .is_err());
    assert!(RESOURCE_SCHEMA_REGISTRY
        .register("\n", resource_schema)
        .is_err());
}

#[test]
fn test_resource_schema_duplicate_registration() {
    let vm_schema = create_vm_resource_schema();

    // First registration should succeed
    assert!(RESOURCE_SCHEMA_REGISTRY
        .register("azure.resource.vm.duplicate", vm_schema.clone())
        .is_ok());

    // Duplicate registration should fail
    let duplicate_result =
        RESOURCE_SCHEMA_REGISTRY.register("azure.resource.vm.duplicate", vm_schema);
    assert!(duplicate_result.is_err());

    // Verify error type
    match duplicate_result.unwrap_err() {
        SchemaRegistryError::AlreadyExists { name, .. } => {
            assert_eq!(name.as_ref(), "azure.resource.vm.duplicate");
        }
        _ => panic!("Expected AlreadyExists error"),
    }
}

#[test]
fn test_azure_resource_removal() {
    // Register multiple Azure Resource schemas with unique names
    let resources = vec![
        ("azure.resource.vm.removal", create_vm_resource_schema()),
        (
            "azure.resource.storage.removal",
            create_storage_resource_schema(),
        ),
        (
            "azure.resource.network.removal",
            create_network_resource_schema(),
        ),
    ];

    for (name, schema) in &resources {
        assert!(RESOURCE_SCHEMA_REGISTRY
            .register(*name, schema.clone())
            .is_ok());
    }

    // Remove one resource
    let removed = RESOURCE_SCHEMA_REGISTRY.remove("azure.resource.storage.removal");
    assert!(removed.is_some());
    assert!(!RESOURCE_SCHEMA_REGISTRY.contains("azure.resource.storage.removal"));

    // Verify the removed schema is correct
    let removed_schema = removed.unwrap();
    assert!(Rc::ptr_eq(&resources[1].1, &removed_schema));

    // Other resources should still be present
    assert!(RESOURCE_SCHEMA_REGISTRY.contains("azure.resource.vm.removal"));
    assert!(RESOURCE_SCHEMA_REGISTRY.contains("azure.resource.network.removal"));
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_resource_schema_access() {
    use std::sync::Barrier;
    use std::thread;

    let barrier = Rc::new(Barrier::new(3));
    let mut handles = vec![];

    // Test concurrent registration of different Azure Resource schemas
    let resources = [
        "concurrent_resource_schema_access.vm",
        "concurrent_resource_schema_access.storage",
        "concurrent_resource_schema_access.network",
    ];

    for (i, resource_name) in resources.iter().enumerate() {
        let barrier = Rc::clone(&barrier);
        let name: String = (*resource_name).into();

        let handle: thread::JoinHandle<Result<(), SchemaRegistryError>> =
            thread::spawn(move || {
                let schema = match i {
                    0 => create_vm_resource_schema(),
                    1 => create_storage_resource_schema(),
                    2 => create_network_resource_schema(),
                    _ => unreachable!(),
                };

                barrier.wait();
                RESOURCE_SCHEMA_REGISTRY.register(name, schema)
            });

        handles.push(handle);
    }

    // Wait for all threads to complete
    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

    // All registrations should succeed
    for result in results {
        assert!(result.is_ok());
    }

    // Should have resource schemas registered
    assert!(RESOURCE_SCHEMA_REGISTRY.contains("concurrent_resource_schema_access.vm"));
    assert!(RESOURCE_SCHEMA_REGISTRY.contains("concurrent_resource_schema_access.storage"));
    assert!(RESOURCE_SCHEMA_REGISTRY.contains("concurrent_resource_schema_access.network"));
}

#[test]
fn test_resource_type_validation() {
    // Test different Azure resource types with specific naming patterns
    let resource_types = vec![
        "azure.compute.vm.validation",
        "azure.storage.account.validation",
        "azure.network.vnet.validation",
        "azure.keyvault.vault.validation",
        "azure.sql.database.validation",
        "azure.webapp.site.validation",
    ];

    let basic_schema = create_resource_schema();

    // Register all resource types
    for resource_type in &resource_types {
        let result = RESOURCE_SCHEMA_REGISTRY.register(*resource_type, basic_schema.clone());
        assert!(result.is_ok(), "Failed to register {resource_type}");
    }

    // Verify all are registered
    for resource_type in &resource_types {
        assert!(
            RESOURCE_SCHEMA_REGISTRY.contains(resource_type),
            "Missing {resource_type}"
        );
        assert!(
            RESOURCE_SCHEMA_REGISTRY.get(resource_type).is_some(),
            "Cannot retrieve {resource_type}"
        );
    }

    // Verify list contains all types
    let names = RESOURCE_SCHEMA_REGISTRY.list_names();

    for resource_type in &resource_types {
        assert!(
            names.contains(&(*resource_type).into()),
            "Name list missing {resource_type}"
        );
    }
}
