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
    static ref RESOURCE_TEST_LOCK: Mutex<()> = Mutex::new(());
}

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
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let resource_schema = create_resource_schema();

    // Test registration of basic resource enum schema
    let result = registry.register("azure.resource.types", resource_schema.clone());
    assert!(result.is_ok());
    assert!(registry.contains("azure.resource.types"));
    assert_eq!(registry.len(), 1);

    // Verify schema can be retrieved
    let retrieved = registry.get("azure.resource.types");
    assert!(retrieved.is_some());
    assert!(Rc::ptr_eq(&resource_schema, &retrieved.unwrap()));
}

#[test]
fn test_vm_resource_schema() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let vm_schema = create_vm_resource_schema();

    // Test registration of VM resource schema
    let result = registry.register("azure.resource.vm", vm_schema.clone());
    assert!(result.is_ok());
    assert!(registry.contains("azure.resource.vm"));

    // Verify schema structure
    match vm_schema.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            assert!(properties.contains_key("type"));
            assert!(properties.contains_key("apiVersion"));
            assert!(properties.contains_key("name"));
            assert!(properties.contains_key("location"));
            assert!(properties.contains_key("properties"));

            if let Some(req) = required {
                assert!(req.contains(&"type".into()));
                assert!(req.contains(&"apiVersion".into()));
                assert!(req.contains(&"name".into()));
                assert!(req.contains(&"location".into()));
                assert!(req.contains(&"properties".into()));
            } else {
                panic!("Expected required fields to be present");
            }

            // Check properties structure
            let vm_properties = properties.get("properties").unwrap();
            match vm_properties.as_type() {
                Type::Object {
                    properties: vm_props,
                    ..
                } => {
                    assert!(vm_props.contains_key("hardwareProfile"));
                    assert!(vm_props.contains_key("osProfile"));
                }
                _ => panic!("Expected properties to be an object"),
            }
        }
        _ => panic!("Expected VM schema to be an object type"),
    }
}

#[test]
fn test_storage_resource_schema() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let storage_schema = create_storage_resource_schema();

    // Test registration of storage resource schema
    let result = registry.register("azure.resource.storage", storage_schema.clone());
    assert!(result.is_ok());
    assert!(registry.contains("azure.resource.storage"));

    // Verify schema structure
    match storage_schema.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            assert!(properties.contains_key("type"));
            assert!(properties.contains_key("apiVersion"));
            assert!(properties.contains_key("name"));
            assert!(properties.contains_key("location"));
            assert!(properties.contains_key("sku"));
            assert!(properties.contains_key("kind"));

            if let Some(req) = required {
                assert!(req.contains(&"type".into()));
                assert!(req.contains(&"apiVersion".into()));
                assert!(req.contains(&"name".into()));
                assert!(req.contains(&"location".into()));
                assert!(req.contains(&"sku".into()));
                assert!(req.contains(&"kind".into()));
            } else {
                panic!("Expected required fields to be present");
            }

            // Check sku structure
            let sku = properties.get("sku").unwrap();
            match sku.as_type() {
                Type::Object {
                    properties: sku_props,
                    ..
                } => {
                    assert!(sku_props.contains_key("name"));
                }
                _ => panic!("Expected sku to be an object"),
            }
        }
        _ => panic!("Expected storage schema to be an object type"),
    }
}

#[test]
fn test_network_resource_schema() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let network_schema = create_network_resource_schema();

    // Test registration of network resource schema
    let result = registry.register("azure.resource.network", network_schema.clone());
    assert!(result.is_ok());
    assert!(registry.contains("azure.resource.network"));

    // Verify schema structure
    match network_schema.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            assert!(properties.contains_key("type"));
            assert!(properties.contains_key("apiVersion"));
            assert!(properties.contains_key("name"));
            assert!(properties.contains_key("location"));
            assert!(properties.contains_key("properties"));

            if let Some(req) = required {
                assert!(req.contains(&"type".into()));
                assert!(req.contains(&"apiVersion".into()));
                assert!(req.contains(&"name".into()));
                assert!(req.contains(&"location".into()));
                assert!(req.contains(&"properties".into()));
            } else {
                panic!("Expected required fields to be present");
            }

            // Check properties structure
            let net_properties = properties.get("properties").unwrap();
            match net_properties.as_type() {
                Type::Object {
                    properties: net_props,
                    ..
                } => {
                    assert!(net_props.contains_key("addressSpace"));
                }
                _ => panic!("Expected properties to be an object"),
            }
        }
        _ => panic!("Expected network schema to be an object type"),
    }
}

#[test]
fn test_multiple_resource_schemas() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();

    // Register all resource schemas
    let vm_schema = create_vm_resource_schema();
    let storage_schema = create_storage_resource_schema();
    let network_schema = create_network_resource_schema();

    assert!(registry.register("azure.resource.vm", vm_schema).is_ok());
    assert!(registry
        .register("azure.resource.storage", storage_schema)
        .is_ok());
    assert!(registry
        .register("azure.resource.network", network_schema)
        .is_ok());

    // Verify all are registered
    assert_eq!(registry.len(), 3);
    assert!(registry.contains("azure.resource.vm"));
    assert!(registry.contains("azure.resource.storage"));
    assert!(registry.contains("azure.resource.network"));

    // Verify they can all be retrieved
    assert!(registry.get("azure.resource.vm").is_some());
    assert!(registry.get("azure.resource.storage").is_some());
    assert!(registry.get("azure.resource.network").is_some());

    // List all names
    let names = registry.list_names();
    assert_eq!(names.len(), 3);
    assert!(names.contains(&"azure.resource.vm".into()));
    assert!(names.contains(&"azure.resource.storage".into()));
    assert!(names.contains(&"azure.resource.network".into()));
}

#[test]
fn test_global_resource_registry() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    // Clear registry
    resource::clear();

    // Register Azure Resource schemas
    let vm_schema = create_vm_resource_schema();
    let storage_schema = create_storage_resource_schema();
    let network_schema = create_network_resource_schema();

    assert!(resource::register("azure.resource.vm", vm_schema).is_ok());
    assert!(resource::register("azure.resource.storage", storage_schema).is_ok());
    assert!(resource::register("azure.resource.network", network_schema).is_ok());

    // Verify all are registered in global registry
    assert_eq!(resource::len(), 3);
    assert!(resource::contains("azure.resource.vm"));
    assert!(resource::contains("azure.resource.storage"));
    assert!(resource::contains("azure.resource.network"));

    // Test retrieval from global registry
    let retrieved_vm = resource::get("azure.resource.vm");
    let retrieved_storage = resource::get("azure.resource.storage");
    let retrieved_network = resource::get("azure.resource.network");

    assert!(retrieved_vm.is_some());
    assert!(retrieved_storage.is_some());
    assert!(retrieved_network.is_some());

    // Clean up
    resource::clear();
}

#[test]
fn test_resource_schema_validation_patterns() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();

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

    let result = registry.register("azure.template.arm", schema_rc);
    assert!(result.is_ok());
    assert!(registry.contains("azure.template.arm"));
}

#[test]
fn test_resource_schema_with_invalid_names() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let resource_schema = create_resource_schema();

    // Test invalid names
    assert!(registry.register("", resource_schema.clone()).is_err());
    assert!(registry.register("   ", resource_schema.clone()).is_err());
    assert!(registry.register("\t", resource_schema.clone()).is_err());
    assert!(registry.register("\n", resource_schema).is_err());

    // Verify registry is empty
    assert!(registry.is_empty());
}

#[test]
fn test_resource_schema_duplicate_registration() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();
    let vm_schema = create_vm_resource_schema();

    // First registration should succeed
    assert!(registry
        .register("azure.resource.vm", vm_schema.clone())
        .is_ok());
    assert_eq!(registry.len(), 1);

    // Duplicate registration should fail
    let duplicate_result = registry.register("azure.resource.vm", vm_schema);
    assert!(duplicate_result.is_err());

    // Verify error type
    match duplicate_result.unwrap_err() {
        SchemaRegistryError::AlreadyExists(name) => {
            assert_eq!(name.as_ref(), "azure.resource.vm");
        }
        _ => panic!("Expected AlreadyExists error"),
    }

    // Registry should still have only one entry
    assert_eq!(registry.len(), 1);
}

#[test]
fn test_azure_resource_removal() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();

    // Register multiple Azure Resource schemas
    let resources = vec![
        ("azure.resource.vm", create_vm_resource_schema()),
        ("azure.resource.storage", create_storage_resource_schema()),
        ("azure.resource.network", create_network_resource_schema()),
    ];

    for (name, schema) in &resources {
        assert!(registry.register(*name, schema.clone()).is_ok());
    }

    assert_eq!(registry.len(), 3);

    // Remove one resource
    let removed = registry.remove("azure.resource.storage");
    assert!(removed.is_some());
    assert_eq!(registry.len(), 2);
    assert!(!registry.contains("azure.resource.storage"));

    // Verify the removed schema is correct
    let removed_schema = removed.unwrap();
    assert!(Rc::ptr_eq(&resources[1].1, &removed_schema));

    // Other resources should still be present
    assert!(registry.contains("azure.resource.vm"));
    assert!(registry.contains("azure.resource.network"));
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_resource_schema_access() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    use std::sync::Barrier;
    use std::thread;

    // Create isolated registry for this test
    let test_registry = Rc::new(SchemaRegistry::new());
    let barrier = Rc::new(Barrier::new(3));
    let mut handles = vec![];

    // Test concurrent registration of different Azure Resource schemas
    let resources = [
        "azure.resource.vm",
        "azure.resource.storage",
        "azure.resource.network",
    ];

    for (i, resource_name) in resources.iter().enumerate() {
        let barrier = Rc::clone(&barrier);
        let registry = Rc::clone(&test_registry);
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

    // Should have 3 resource schemas registered
    assert_eq!(test_registry.len(), 3);
    assert!(test_registry.contains("azure.resource.vm"));
    assert!(test_registry.contains("azure.resource.storage"));
    assert!(test_registry.contains("azure.resource.network"));
}

#[test]
fn test_azure_resource_clear() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();

    // Register multiple Azure Resource schemas
    assert!(registry
        .register("azure.resource.vm", create_vm_resource_schema())
        .is_ok());
    assert!(registry
        .register("azure.resource.storage", create_storage_resource_schema())
        .is_ok());
    assert!(registry
        .register("azure.resource.network", create_network_resource_schema())
        .is_ok());

    assert_eq!(registry.len(), 3);
    assert!(!registry.is_empty());

    // Clear all resources
    registry.clear();

    assert_eq!(registry.len(), 0);
    assert!(registry.is_empty());
    assert!(registry.list_names().is_empty());

    // Verify specific resources are no longer present
    assert!(!registry.contains("azure.resource.vm"));
    assert!(!registry.contains("azure.resource.storage"));
    assert!(!registry.contains("azure.resource.network"));
}

#[test]
fn test_resource_type_validation() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    let registry = SchemaRegistry::new();

    // Test different Azure resource types with specific naming patterns
    let resource_types = vec![
        "azure.compute.vm",
        "azure.storage.account",
        "azure.network.vnet",
        "azure.keyvault.vault",
        "azure.sql.database",
        "azure.webapp.site",
    ];

    let basic_schema = create_resource_schema();

    // Register all resource types
    for resource_type in &resource_types {
        let result = registry.register(*resource_type, basic_schema.clone());
        assert!(result.is_ok(), "Failed to register {resource_type}");
    }

    // Verify all are registered
    assert_eq!(registry.len(), resource_types.len());

    for resource_type in &resource_types {
        assert!(registry.contains(resource_type), "Missing {resource_type}");
        assert!(
            registry.get(resource_type).is_some(),
            "Cannot retrieve {resource_type}"
        );
    }

    // Verify list contains all types
    let names = registry.list_names();
    assert_eq!(names.len(), resource_types.len());

    for resource_type in &resource_types {
        assert!(
            names.contains(&(*resource_type).into()),
            "Name list missing {resource_type}"
        );
    }
}

// Schema validation tests for Azure Resource schemas

#[test]
fn test_validate_vm_resource_valid() {
    let schema = create_vm_resource_schema();

    let valid_vm_data = json!({
        "type": "Microsoft.Compute/virtualMachines",
        "apiVersion": "2021-03-01",
        "name": "my-vm-01",
        "location": "eastus",
        "properties": {
            "hardwareProfile": {
                "vmSize": "Standard_B2s"
            },
            "osProfile": {
                "computerName": "my-computer",
                "adminUsername": "azureuser"
            }
        }
    });

    let value = Value::from(valid_vm_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_ok());
}

#[test]
fn test_validate_vm_resource_missing_required() {
    let schema = create_vm_resource_schema();

    let invalid_vm_data = json!({
        "type": "Microsoft.Compute/virtualMachines",
        "apiVersion": "2021-03-01",
        "name": "my-vm-01"
        // Missing location and properties
    });

    let value = Value::from(invalid_vm_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::MissingRequiredProperty { property, .. } => {
            // Should be missing either location or properties
            assert!(property == "location".into() || property == "properties".into());
        }
        other => panic!("Expected MissingRequiredProperty error, got: {:?}", other),
    }
}

#[test]
fn test_validate_vm_resource_invalid_vm_size() {
    let schema = create_vm_resource_schema();

    let invalid_vm_data = json!({
        "type": "Microsoft.Compute/virtualMachines",
        "apiVersion": "2021-03-01",
        "name": "my-vm-01",
        "location": "eastus",
        "properties": {
            "hardwareProfile": {
                "vmSize": "InvalidSize"
            },
            "osProfile": {
                "computerName": "my-computer",
                "adminUsername": "azureuser"
            }
        }
    });

    let value = Value::from(invalid_vm_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::PropertyValidationFailed {
            property, error, ..
        } => {
            assert_eq!(property, "properties".into());
            match error.as_ref() {
                ValidationError::PropertyValidationFailed {
                    property: inner_prop,
                    error: inner_error,
                    ..
                } => {
                    assert_eq!(*inner_prop, "hardwareProfile".into());
                    match inner_error.as_ref() {
                        ValidationError::PropertyValidationFailed {
                            property: vm_size_prop,
                            error: vm_size_error,
                            ..
                        } => {
                            assert_eq!(*vm_size_prop, "vmSize".into());
                            match vm_size_error.as_ref() {
                                ValidationError::NotInEnum { .. } => {
                                    // Expected deeply nested error structure
                                }
                                other => {
                                    panic!("Expected NotInEnum error for vmSize, got: {:?}", other)
                                }
                            }
                        }
                        other => panic!(
                            "Expected PropertyValidationFailed for vmSize, got: {:?}",
                            other
                        ),
                    }
                }
                other => panic!(
                    "Expected PropertyValidationFailed for hardwareProfile, got: {:?}",
                    other
                ),
            }
        }
        other => panic!("Expected PropertyValidationFailed error, got: {:?}", other),
    }
}

#[test]
fn test_validate_storage_resource_valid() {
    let schema = create_storage_resource_schema();

    let valid_storage_data = json!({
        "type": "Microsoft.Storage/storageAccounts",
        "apiVersion": "2021-04-01",
        "name": "mystorageaccount001",
        "location": "westus2",
        "sku": {
            "name": "Standard_LRS"
        },
        "kind": "StorageV2",
        "properties": {
            "accessTier": "Hot",
            "encryption": {
                "services": {}
            }
        }
    });

    let value = Value::from(valid_storage_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_ok());
}

#[test]
fn test_validate_storage_resource_invalid_name() {
    let schema = create_storage_resource_schema();

    let invalid_storage_data = json!({
        "type": "Microsoft.Storage/storageAccounts",
        "apiVersion": "2021-04-01",
        "name": "Invalid-Storage-Name-With-Caps-And-Dashes",
        "location": "westus2",
        "sku": {
            "name": "Standard_LRS"
        },
        "kind": "StorageV2"
    });

    let value = Value::from(invalid_storage_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::PropertyValidationFailed {
            property, error, ..
        } => {
            assert_eq!(property, "name".into());
            match error.as_ref() {
                ValidationError::PatternMismatch { .. } => {
                    // Expected pattern mismatch for storage account name
                }
                other => panic!("Expected PatternMismatch error for name, got: {:?}", other),
            }
        }
        other => panic!("Expected PropertyValidationFailed error, got: {:?}", other),
    }
}

#[test]
fn test_validate_storage_resource_invalid_sku() {
    let schema = create_storage_resource_schema();

    let invalid_storage_data = json!({
        "type": "Microsoft.Storage/storageAccounts",
        "apiVersion": "2021-04-01",
        "name": "mystorageaccount001",
        "location": "westus2",
        "sku": {
            "name": "Invalid_SKU"
        },
        "kind": "StorageV2"
    });

    let value = Value::from(invalid_storage_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::PropertyValidationFailed {
            property, error, ..
        } => {
            assert_eq!(property, "sku".into());
            match error.as_ref() {
                ValidationError::PropertyValidationFailed {
                    property: sku_prop,
                    error: sku_error,
                    ..
                } => {
                    assert_eq!(*sku_prop, "name".into());
                    match sku_error.as_ref() {
                        ValidationError::NotInEnum { .. } => {
                            // Expected enum validation error
                        }
                        other => panic!("Expected NotInEnum error for sku name, got: {:?}", other),
                    }
                }
                other => panic!(
                    "Expected PropertyValidationFailed for sku name, got: {:?}",
                    other
                ),
            }
        }
        other => panic!("Expected PropertyValidationFailed error, got: {:?}", other),
    }
}

#[test]
fn test_validate_network_resource_valid() {
    let schema = create_network_resource_schema();

    let valid_network_data = json!({
        "type": "Microsoft.Network/virtualNetworks",
        "apiVersion": "2021-02-01",
        "name": "my-vnet",
        "location": "eastus",
        "properties": {
            "addressSpace": {
                "addressPrefixes": ["10.0.0.0/16"]
            },
            "subnets": [
                {
                    "name": "default",
                    "properties": {
                        "addressPrefix": "10.0.1.0/24"
                    }
                }
            ]
        }
    });

    let value = Value::from(valid_network_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_ok());
}

#[test]
fn test_validate_network_resource_invalid_address_prefix() {
    let schema = create_network_resource_schema();

    let invalid_network_data = json!({
        "type": "Microsoft.Network/virtualNetworks",
        "apiVersion": "2021-02-01",
        "name": "my-vnet",
        "location": "eastus",
        "properties": {
            "addressSpace": {
                "addressPrefixes": ["invalid-cidr"]
            }
        }
    });

    let value = Value::from(invalid_network_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_err());

    match result.unwrap_err() {
        ValidationError::PropertyValidationFailed {
            property, error, ..
        } => {
            assert_eq!(property, "properties".into());
            match error.as_ref() {
                ValidationError::PropertyValidationFailed {
                    property: addr_prop,
                    ..
                } => {
                    assert_eq!(*addr_prop, "addressSpace".into());
                    // Continue checking nested structure for array validation
                }
                other => panic!(
                    "Expected PropertyValidationFailed for addressSpace, got: {:?}",
                    other
                ),
            }
        }
        other => panic!("Expected PropertyValidationFailed error, got: {:?}", other),
    }
}

#[test]
fn test_validate_basic_resource_enum() {
    let schema = create_resource_schema();

    // Test all valid resource types
    let valid_types = [
        "Microsoft.Compute/virtualMachines",
        "Microsoft.Storage/storageAccounts",
        "Microsoft.Network/virtualNetworks",
    ];

    for resource_type in valid_types {
        let value = Value::from(resource_type);
        let result = SchemaValidator::validate(&value, &schema);
        assert!(
            result.is_ok(),
            "Resource type '{resource_type}' should be valid"
        );
    }

    // Test invalid resource type
    let invalid_value = Value::from("Microsoft.Invalid/resourceType");
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
fn test_validate_complex_arm_template() {
    let complex_schema_json = json!({
        "type": "object",
        "properties": {
            "$schema": {
                "type": "string"
            },
            "contentVersion": {
                "type": "string"
            },
            "parameters": {
                "type": "object",
                "additionalProperties": { "type": "any" }
            },
            "variables": {
                "type": "object",
                "additionalProperties": { "type": "any" }
            },
            "resources": {
                "type": "array",
                "items": {
                    "type": "object",
                    "properties": {
                        "type": {
                            "type": "string"
                        },
                        "apiVersion": {
                            "type": "string"
                        },
                        "name": {
                            "type": "string"
                        },
                        "location": {
                            "type": "string"
                        },
                        "properties": {
                            "type": "object",
                            "additionalProperties": { "type": "any" }
                        },
                        "tags": {
                            "type": "object",
                            "additionalProperties": { "type": "string" }
                        }
                    },
                    "required": ["type", "apiVersion", "name"],
                    "additionalProperties": { "type": "any" }
                }
            },
            "outputs": {
                "type": "object",
                "additionalProperties": { "type": "any" }
            }
        },
        "required": ["resources"],
        "additionalProperties": { "type": "any" }
    });

    let schema = Schema::from_serde_json_value(complex_schema_json).unwrap();

    let valid_template_data = json!({
        "$schema": "https://schema.management.azure.com/schemas/2019-04-01/deploymentTemplate.json#",
        "contentVersion": "1.0.0.0",
        "parameters": {
            "vmName": {
                "type": "string",
                "defaultValue": "myVM"
            }
        },
        "variables": {
            "storageAccountName": "[concat('storage', uniqueString(resourceGroup().id))]"
        },
        "resources": [
            {
                "type": "Microsoft.Compute/virtualMachines",
                "apiVersion": "2021-03-01",
                "name": "[parameters('vmName')]",
                "location": "[resourceGroup().location]",
                "properties": {
                    "hardwareProfile": {
                        "vmSize": "Standard_B1s"
                    }
                },
                "tags": {
                    "environment": "dev",
                    "project": "test"
                }
            }
        ],
        "outputs": {
            "vmId": {
                "type": "string",
                "value": "[resourceId('Microsoft.Compute/virtualMachines', parameters('vmName'))]"
            }
        }
    });

    let value = Value::from(valid_template_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_ok());
}

#[test]
fn test_validate_resource_type_mismatch() {
    let schema = create_vm_resource_schema();

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

#[test]
fn test_complex_nested_azure_template_validation() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    // Create a complex ARM template schema with deeply nested properties
    let complex_schema = json!({
        "type": "object",
        "properties": {
            "$schema": { "type": "string" },
            "contentVersion": { "type": "string", "pattern": "^[0-9]+\\.[0-9]+\\.[0-9]+\\.[0-9]+$" },
            "metadata": {
                "type": "object",
                "properties": {
                    "description": { "type": "string" },
                    "author": { "type": "string" },
                    "tags": {
                        "type": "object",
                        "additionalProperties": { "type": "string" }
                    }
                }
            },
            "parameters": {
                "type": "object",
                "additionalProperties": {
                    "type": "object",
                    "properties": {
                        "type": { "enum": ["string", "int", "bool", "array", "object"] },
                        "defaultValue": { "type": "any" },
                        "allowedValues": { "type": "array", "items": { "type": "any" } },
                        "minValue": { "type": "number" },
                        "maxValue": { "type": "number" },
                        "minLength": { "type": "integer" },
                        "maxLength": { "type": "integer" },
                        "metadata": {
                            "type": "object",
                            "properties": {
                                "description": { "type": "string" },
                                "strongType": { "type": "string" }
                            }
                        }
                    },
                    "required": ["type"]
                }
            },
            "variables": { "type": "object" },
            "resources": {
                "type": "array",
                "items": {
                    "type": "object",
                    "properties": {
                        "type": { "type": "string" },
                        "apiVersion": { "type": "string" },
                        "name": { "type": "string" },
                        "location": { "type": "string" },
                        "dependsOn": {
                            "type": "array",
                            "items": { "type": "string" }
                        },
                        "condition": { "type": "boolean" },
                        "copy": {
                            "type": "object",
                            "properties": {
                                "name": { "type": "string" },
                                "count": { "type": "integer", "minimum": 1, "maximum": 800 },
                                "mode": { "enum": ["Parallel", "Serial"] },
                                "batchSize": { "type": "integer", "minimum": 1 }
                            },
                            "required": ["name", "count"]
                        },
                        "properties": { "type": "object" },
                        "tags": {
                            "type": "object",
                            "additionalProperties": { "type": "string" }
                        }
                    },
                    "required": ["type", "apiVersion", "name"]
                }
            },
            "outputs": {
                "type": "object",
                "additionalProperties": {
                    "type": "object",
                    "properties": {
                        "type": { "enum": ["string", "int", "bool", "array", "object"] },
                        "value": { "type": "any" },
                        "condition": { "type": "boolean" },
                        "copy": {
                            "type": "object",
                            "properties": {
                                "count": { "type": "integer", "minimum": 1 },
                                "input": { "type": "any" }
                            },
                            "required": ["count", "input"]
                        }
                    },
                    "required": ["type", "value"]
                }
            }
        },
        "required": ["$schema", "contentVersion", "resources"]
    });

    let schema = Schema::from_serde_json_value(complex_schema).unwrap();

    // Valid complex template with nested copy loops and conditions
    let valid_template = json!({
        "$schema": "https://schema.management.azure.com/schemas/2019-04-01/deploymentTemplate.json#",
        "contentVersion": "1.2.3.4",
        "metadata": {
            "description": "Complex deployment with copy loops and conditions",
            "author": "Azure DevOps Team",
            "tags": {
                "environment": "production",
                "cost-center": "engineering",
                "department": "cloud-infrastructure"
            }
        },
        "parameters": {
            "vmCount": {
                "type": "int",
                "defaultValue": 3,
                "minValue": 1,
                "maxValue": 10,
                "metadata": {
                    "description": "Number of VMs to deploy",
                    "strongType": "Microsoft.Compute/SKUs"
                }
            },
            "environment": {
                "type": "string",
                "defaultValue": "dev",
                "allowedValues": ["dev", "test", "staging", "prod"],
                "metadata": {
                    "description": "Environment name for resource naming"
                }
            },
            "enableMonitoring": {
                "type": "bool",
                "defaultValue": true,
                "metadata": {
                    "description": "Whether to enable monitoring extensions"
                }
            }
        },
        "variables": {
            "vmPrefix": "[concat(parameters('environment'), '-vm-')]",
            "storageAccountName": "[concat('storage', uniqueString(resourceGroup().id))]"
        },
        "resources": [
            {
                "type": "Microsoft.Storage/storageAccounts",
                "apiVersion": "2021-04-01",
                "name": "[variables('storageAccountName')]",
                "location": "eastus",
                "properties": {
                    "accountType": "Standard_LRS"
                },
                "tags": {
                    "purpose": "vm-diagnostics",
                    "environment": "[parameters('environment')]"
                }
            },
            {
                "type": "Microsoft.Compute/virtualMachines",
                "apiVersion": "2021-03-01",
                "name": "[concat(variables('vmPrefix'), copyIndex(1))]",
                "location": "eastus",
                "condition": true,
                "dependsOn": [
                    "[resourceId('Microsoft.Storage/storageAccounts', variables('storageAccountName'))]"
                ],
                "copy": {
                    "name": "vmLoop",
                    "count": 5,
                    "mode": "Parallel",
                    "batchSize": 2
                },
                "properties": {
                    "hardwareProfile": {
                        "vmSize": "Standard_B2s"
                    }
                },
                "tags": {
                    "environment": "[parameters('environment')]",
                    "vm-index": "[string(copyIndex())]"
                }
            }
        ],
        "outputs": {
            "storageAccountId": {
                "type": "string",
                "value": "[resourceId('Microsoft.Storage/storageAccounts', variables('storageAccountName'))]"
            },
            "vmIds": {
                "type": "array",
                "copy": {
                    "count": 5,
                    "input": "[resourceId('Microsoft.Compute/virtualMachines', concat(variables('vmPrefix'), copyIndex(1)))]"
                },
                "value" : "[resourceId('Microsoft.Compute/virtualMachines', concat(variables('vmPrefix'), copyIndex(1)))]"
            }
        }
    });

    let value = Value::from(valid_template);
    let result = SchemaValidator::validate(&value, &schema);
    std::dbg!(&result);
    assert!(
        result.is_ok(),
        "Complex valid template should pass validation"
    );

    // Test invalid template with constraint violations
    let invalid_template = json!({
        "$schema": "https://schema.management.azure.com/schemas/2019-04-01/deploymentTemplate.json#",
        "contentVersion": "invalid-version", // Should match pattern
        "resources": [
            {
                "type": "Microsoft.Compute/virtualMachines",
                "apiVersion": "2021-03-01",
                "name": "test-vm",
                "copy": {
                    "name": "vmLoop",
                    "count": 1000 // Exceeds maximum of 800
                }
            }
        ]
    });

    let value = Value::from(invalid_template);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(
        result.is_err(),
        "Template with constraint violations should fail"
    );
}

#[test]
fn test_deep_nesting_and_recursive_structures() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    // Schema with moderate nesting (5 levels) to avoid macro recursion limits
    let deep_schema = json!({
        "type": "object",
        "properties": {
            "level1": {
                "type": "object",
                "properties": {
                    "level2": {
                        "type": "object",
                        "properties": {
                            "level3": {
                                "type": "object",
                                "properties": {
                                    "level4": {
                                        "type": "object",
                                        "properties": {
                                            "level5": {
                                                "type": "object",
                                                "properties": {
                                                    "deepValue": {
                                                        "type": "string",
                                                        "pattern": "^deep-[0-9]+$"
                                                    },
                                                    "recursiveArray": {
                                                        "type": "array",
                                                        "items": {
                                                            "type": "object",
                                                            "properties": {
                                                                "nested": {
                                                                    "type": "object",
                                                                    "properties": {
                                                                        "value": { "type": "number" },
                                                                        "metadata": {
                                                                            "type": "object",
                                                                            "additionalProperties": { "type": "string" }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                },
                                                "required": ["deepValue"]
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        },
        "required": ["level1"]
    });

    let schema = Schema::from_serde_json_value(deep_schema).unwrap();

    // Valid deeply nested structure
    let valid_deep_data = json!({
        "level1": {
            "level2": {
                "level3": {
                    "level4": {
                        "level5": {
                            "deepValue": "deep-12345",
                            "recursiveArray": [
                                {
                                    "nested": {
                                        "value": 42.5,
                                        "metadata": {
                                            "type": "numeric",
                                            "unit": "percentage",
                                            "source": "sensor-1"
                                        }
                                    }
                                },
                                {
                                    "nested": {
                                        "value": 15.3,
                                        "metadata": {
                                            "type": "numeric",
                                            "unit": "temperature",
                                            "source": "sensor-2"
                                        }
                                    }
                                }
                            ]
                        }
                    }
                }
            }
        }
    });

    let value = Value::from(valid_deep_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_ok(), "Valid deeply nested structure should pass");

    // Invalid - missing required deepValue
    let invalid_deep_data = json!({
        "level1": {
            "level2": {
                "level3": {
                    "level4": {
                        "level5": {
                            // Missing required "deepValue"
                            "recursiveArray": []
                        }
                    }
                }
            }
        }
    });

    let value = Value::from(invalid_deep_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(
        result.is_err(),
        "Structure missing required deep field should fail"
    );
}

#[test]
fn test_unicode_and_internationalization_validation() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    // Schema supporting international characters and Unicode
    let unicode_schema = json!({
        "type": "object",
        "properties": {
            "names": {
                "type": "object",
                "properties": {
                    "chinese": { "type": "string", "pattern": "^[\\u4e00-\\u9fff]+$" },
                    "russian": { "type": "string", "pattern": "^[\\u0400-\\u04ff]+$" },
                    "japanese": { "type": "string", "pattern": "^[\\u3040-\\u309f\\u30a0-\\u30ff\\u4e00-\\u9fff]+$" },
                    "korean": { "type": "string", "pattern": "^[\\uac00-\\ud7af]+$" },
                    "hindi": { "type": "string", "pattern": "^[\\u0900-\\u097f]+$" },
                    "french": { "type": "string", "pattern": "^[a-zA-ZàâäéèêëïîôöùûüÿñæœÀÂÄÉÈÊËÏÎÔÖÙÛÜŸÑÆŒ\\s-]+$" }
                }
            },
            "descriptions": {
                "type": "object",
                "additionalProperties": {
                    "type": "string",
                    "minLength": 1,
                    "maxLength": 1000
                }
            },
            "metadata": {
                "type": "object",
                "properties": {
                    "encoding": { "enum": ["UTF-8", "UTF-16", "UTF-32"] },
                    "locale": { "type": "string", "pattern": "^[a-z]{2}-[A-Z]{2}$" },
                    "timezone": { "type": "string" }
                }
            }
        },
        "required": ["names", "metadata"]
    });

    let schema = Schema::from_serde_json_value(unicode_schema).unwrap();

    // Valid international data
    let valid_unicode_data = json!({
        "names": {
            "chinese": "你好世界",
            "russian": "привет",
            "japanese": "こんにちは世界",
            "korean": "안녕하세요",
            "hindi": "नमस्ते",
            "french": "Bonjour le Monde"
        },
        "descriptions": {
            "en-US": "Hello World application for international users",
            "zh-CN": "面向国际用户的你好世界应用程序",
            "ru-RU": "Приложение Hello World для международных пользователей",
            "ja-JP": "国際ユーザー向けのHello Worldアプリケーション",
            "ko-KR": "국제 사용자를 위한 Hello World 애플리케이션",
            "hi-IN": "अंतर्राष्ट्रीय उपयोगकर्ताओं के लिए हैलो वर्ल्ड एप्लिकेशन",
            "fr-FR": "Application Hello World pour les utilisateurs internationaux"
        },
        "metadata": {
            "encoding": "UTF-8",
            "locale": "en-US",
            "timezone": "UTC"
        }
    });

    let value = Value::from(valid_unicode_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(result.is_ok(), "Valid Unicode data should pass validation");

    // Invalid - non-matching Unicode patterns
    let invalid_unicode_data = json!({
        "names": {
            "chinese": "Hello", // Should be Chinese characters
            "russian": "Goodbye", // Should be Russian characters
            "japanese": "Test", // Should be Japanese characters
            "korean": "Invalid", // Should be Korean characters
            "hindi": "Wrong", // Should be Hindi characters
            "french": "123456" // Should be French text
        },
        "metadata": {
            "encoding": "UTF-8",
            "locale": "invalid-locale", // Should match pattern
            "timezone": "UTC"
        }
    });

    let value = Value::from(invalid_unicode_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(
        result.is_err(),
        "Invalid Unicode patterns should fail validation"
    );
}

#[test]
fn test_edge_cases_and_boundary_conditions() {
    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    // Schema with strict boundary conditions
    let boundary_schema = json!({
        "type": "object",
        "properties": {
            "strings": {
                "type": "object",
                "properties": {
                    "empty": { "type": "string", "minLength": 0, "maxLength": 0 },
                    "single": { "type": "string", "minLength": 1, "maxLength": 1 },
                    "exact_length": { "type": "string", "minLength": 10, "maxLength": 10 },
                    "very_long": { "type": "string", "maxLength": 10000 }
                }
            },
            "numbers": {
                "type": "object",
                "properties": {
                    "zero": { "type": "number", "minimum": 0, "maximum": 0 },
                    "negative": { "type": "number", "minimum": -1000, "maximum": -1 },
                    "positive": { "type": "number", "minimum": 1, "maximum": 1000 },
                    "float_precision": { "type": "number" }
                }
            },
            "arrays": {
                "type": "object",
                "properties": {
                    "empty": { "type": "array", "minItems": 0, "maxItems": 0, "items": { "type": "string" } },
                    "single_item": { "type": "array", "minItems": 1, "maxItems": 1, "items": { "type": "string" } },
                    "exact_size": { "type": "array", "minItems": 5, "maxItems": 5, "items": { "type": "integer" } },
                    "large_array": { "type": "array", "maxItems": 1000, "items": { "type": "boolean" } }
                }
            },
            "objects": {
                "type": "object",
                "properties": {
                    "empty": { "type": "object", "additionalProperties": false },
                    "single_prop": {
                        "type": "object",
                        "properties": { "only": { "type": "string" } },
                        "additionalProperties": false,
                        "required": ["only"]
                    }
                }
            },
            "nulls_and_optionals": {
                "type": "object",
                "properties": {
                    "nullable": { "type": "string" },
                    "optional": { "type": "string" },
                    "required_null": { "type": "null" }
                },
                "required": ["required_null"]
            }
        },
        "required": ["strings", "numbers", "arrays", "objects", "nulls_and_optionals"]
    });

    let schema = Schema::from_serde_json_value(boundary_schema).unwrap();

    // Valid boundary condition data
    let valid_boundary_data = json!({
        "strings": {
            "empty": "",
            "single": "a",
            "exact_length": "exactly_10",
            "very_long": "a".repeat(9999)
        },
        "numbers": {
            "zero": 0,
            "negative": -500,
            "positive": 250,
            "float_precision": 123.45
        },
        "arrays": {
            "empty": [],
            "single_item": ["test"],
            "exact_size": [1, 2, 3, 4, 5],
            "large_array": vec![true; 500]
        },
        "objects": {
            "empty": {},
            "single_prop": {
                "only": "value"
            }
        },
        "nulls_and_optionals": {
            "nullable": "string_value",
            "optional": "present",
            "required_null": null
        }
    });

    let value = Value::from(valid_boundary_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(
        result.is_ok(),
        "Valid boundary conditions should pass validation"
    );

    // Invalid boundary violations
    let invalid_boundary_data = json!({
        "strings": {
            "empty": "not empty", // Should be empty
            "single": "too long", // Should be exactly 1 character
            "exact_length": "wrong", // Should be exactly 10 characters
            "very_long": "a".repeat(10001) // Exceeds maximum length
        },
        "numbers": {
            "zero": 0.1, // Should be exactly 0
            "negative": 1, // Should be negative
            "positive": -1, // Should be positive
            "float_precision": 123.456 // Wrong precision
        },
        "arrays": {
            "empty": ["not empty"], // Should be empty
            "single_item": [], // Should have exactly 1 item
            "exact_size": [1, 2, 3], // Should have exactly 5 items
            "large_array": vec![true; 1001] // Exceeds maximum items
        },
        "objects": {
            "empty": { "should_be_empty": true }, // Should have no properties
            "single_prop": {} // Missing required property
        },
        "nulls_and_optionals": {
            "nullable": "should allow null or string",
            "required_null": "should be null" // Should be null
        }
    });

    let value = Value::from(invalid_boundary_data);
    let result = SchemaValidator::validate(&value, &schema);
    assert!(
        result.is_err(),
        "Boundary violations should fail validation"
    );
}

#[test]
fn test_concurrent_schema_validation_stress() {
    use std::sync::Arc;
    use std::thread;

    let _lock = RESOURCE_TEST_LOCK.lock().unwrap();

    // Create a complex schema for concurrent testing
    let concurrent_schema = json!({
        "type": "object",
        "properties": {
            "id": { "type": "string", "pattern": "^[a-zA-Z0-9-]{8,64}$" },
            "timestamp": { "type": "string" },
            "data": {
                "type": "object",
                "properties": {
                    "values": {
                        "type": "array",
                        "items": { "type": "number" },
                        "minItems": 1,
                        "maxItems": 100
                    },
                    "metadata": {
                        "type": "object",
                        "additionalProperties": { "type": "string" }
                    }
                },
                "required": ["values"]
            }
        },
        "required": ["id", "timestamp", "data"]
    });

    let schema = Arc::new(Schema::from_serde_json_value(concurrent_schema).unwrap());

    // Spawn multiple threads to validate concurrently
    let mut handles = vec![];

    for thread_id in 0..10 {
        let schema_clone = Arc::clone(&schema);

        let handle = thread::spawn(move || {
            let mut results = Vec::new();

            for i in 0..100 {
                let test_data = json!({
                    "id": format!("thread-{}-item-{}", thread_id, i),
                    "timestamp": "2023-12-31T23:59:59Z",
                    "data": {
                        "values": vec![1.0, 2.0, 3.0, (i as f64)],
                        "metadata": {
                            "thread": thread_id.to_string(),
                            "iteration": i.to_string(),
                            "test_type": "concurrent"
                        }
                    }
                });

                let value = Value::from(test_data);
                let result = SchemaValidator::validate(&value, &schema_clone);
                results.push(result.is_ok());
            }

            results
        });

        handles.push(handle);
    }

    // Wait for all threads and collect results
    let mut all_results = Vec::new();
    for handle in handles {
        let thread_results = handle.join().expect("Thread should complete successfully");
        all_results.extend(thread_results);
    }

    // All validations should pass
    let successful_validations = all_results.iter().filter(|&&result| result).count();
    assert_eq!(
        successful_validations, 1000,
        "All 1000 concurrent validations should pass"
    );
}
