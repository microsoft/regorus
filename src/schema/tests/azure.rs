// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::pattern_type_mismatch
)] // azure schema tests panic/unwrap to assert structures

use super::super::*;

#[test]
fn test_azure_storage_account_schema() {
    let schema = r#"{
        "type": "object",
        "description": "Azure Storage Account resource schema",
        "properties": {
            "apiVersion": {
                "type": "string",
                "description": "The API version for the resource"
            },
            "name": {
                "type": "string",
                "description": "The name of the storage account",
                "minLength": 3,
                "maxLength": 24,
                "pattern": "^[a-z0-9]+$"
            },
            "location": {
                "type": "string",
                "description": "The Azure region where the resource is deployed"
            },
            "type": {
                "const": "Microsoft.Storage/storageAccounts"
            },
            "kind": {
                "enum": ["Storage", "StorageV2", "BlobStorage", "FileStorage", "BlockBlobStorage"],
                "description": "The kind of storage account"
            },
            "sku": {
                "type": "object",
                "description": "The SKU of the storage account",
                "properties": {
                    "name": {
                        "enum": ["Standard_LRS", "Standard_GRS", "Standard_RAGRS", "Standard_ZRS", "Premium_LRS", "Premium_ZRS", "Standard_GZRS", "Standard_RAGZRS"]
                    },
                    "tier": {
                        "enum": ["Standard", "Premium"]
                    }
                },
                "required": ["name"]
            },
            "properties": {
                "type": "object",
                "description": "Storage account properties",
                "properties": {
                    "accessTier": {
                        "enum": ["Hot", "Cool", "Archive"],
                        "description": "Access tier for blob storage"
                    },
                    "allowBlobPublicAccess": {
                        "type": "boolean",
                        "description": "Allow or disallow public access to all blobs or containers",
                        "default": false
                    },
                    "minimumTlsVersion": {
                        "enum": ["TLS1_0", "TLS1_1", "TLS1_2"],
                        "description": "Set the minimum TLS version to be permitted on requests"
                    },
                    "networkAcls": {
                        "type": "object",
                        "description": "Network access control rules",
                        "properties": {
                            "defaultAction": {
                                "enum": ["Allow", "Deny"]
                            },
                            "ipRules": {
                                "type": "array",
                                "description": "IP address rules",
                                "items": {
                                    "type": "object",
                                    "properties": {
                                        "value": {
                                            "type": "string",
                                            "description": "IP address or CIDR block"
                                        },
                                        "action": {
                                            "const": "Allow"
                                        }
                                    },
                                    "required": ["value"]
                                }
                            },
                            "virtualNetworkRules": {
                                "type": "array",
                                "description": "Virtual network rules",
                                "items": {
                                    "type": "object",
                                    "properties": {
                                        "id": {
                                            "type": "string",
                                            "description": "Resource ID of a subnet"
                                        },
                                        "action": {
                                            "const": "Allow"
                                        },
                                        "state": {
                                            "enum": ["provisioning", "deprovisioning", "succeeded", "failed", "networkSourceDeleted"]
                                        }
                                    },
                                    "required": ["id"]
                                }
                            }
                        },
                        "required": ["defaultAction"]
                    }
                }
            },
            "tags": {
                "type": "object",
                "description": "Resource tags",
                "additionalProperties": {
                    "type": "string"
                }
            }
        },
        "required": ["apiVersion", "name", "location", "type", "kind", "sku"]
    }"#;

    let schema = Schema::from_json_str(schema).unwrap();

    match schema.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            // Verify core properties
            assert!(properties.contains_key("name"));
            assert!(properties.contains_key("location"));
            assert!(properties.contains_key("type"));
            assert!(properties.contains_key("kind"));
            assert!(properties.contains_key("sku"));

            // Verify name constraints
            match properties.get("name").unwrap().as_type() {
                Type::String {
                    min_length,
                    max_length,
                    pattern,
                    ..
                } => {
                    assert_eq!(min_length, &Some(3));
                    assert_eq!(max_length, &Some(24));
                    assert!(pattern.is_some());
                }
                _ => panic!("Expected name to be Type::String"),
            }

            // Verify type is constant
            match properties.get("type").unwrap().as_type() {
                Type::Const { value, .. } => {
                    assert_eq!(value, &Value::from("Microsoft.Storage/storageAccounts"));
                }
                _ => panic!("Expected type to be Type::Const"),
            }

            // Verify kind enum
            match properties.get("kind").unwrap().as_type() {
                Type::Enum { values, .. } => {
                    assert_eq!(values.len(), 5);
                    assert!(values.contains(&Value::from("StorageV2")));
                }
                _ => panic!("Expected kind to be Type::Enum"),
            }

            // Verify required fields
            let req = required.as_ref().expect("required should be present");
            assert!(req.contains(&"name".into()));
            assert!(req.contains(&"type".into()));
            assert!(req.contains(&"kind".into()));
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_azure_virtual_machine_schema() {
    let schema = r#"{
        "type": "object",
        "description": "Azure Virtual Machine resource schema",
        "properties": {
            "apiVersion": {
                "type": "string",
                "description": "The API version for the resource"
            },
            "name": {
                "type": "string",
                "description": "The name of the virtual machine",
                "minLength": 1,
                "maxLength": 64
            },
            "location": {
                "type": "string",
                "description": "The Azure region where the resource is deployed"
            },
            "type": {
                "const": "Microsoft.Compute/virtualMachines"
            },
            "properties": {
                "type": "object",
                "description": "Virtual machine properties",
                "properties": {
                    "hardwareProfile": {
                        "type": "object",
                        "description": "Hardware settings for the virtual machine",
                        "properties": {
                            "vmSize": {
                                "enum": [
                                    "Standard_B1s", "Standard_B1ms", "Standard_B2s", "Standard_B2ms",
                                    "Standard_D2s_v3", "Standard_D4s_v3", "Standard_D8s_v3",
                                    "Standard_F2s_v2", "Standard_F4s_v2", "Standard_F8s_v2"
                                ],
                                "description": "The virtual machine size"
                            }
                        },
                        "required": ["vmSize"]
                    },
                    "storageProfile": {
                        "type": "object",
                        "description": "Storage settings for the virtual machine",
                        "properties": {
                            "imageReference": {
                                "type": "object",
                                "description": "The image reference",
                                "properties": {
                                    "publisher": {
                                        "type": "string",
                                        "description": "The image publisher"
                                    },
                                    "offer": {
                                        "type": "string",
                                        "description": "The image offer"
                                    },
                                    "sku": {
                                        "type": "string",
                                        "description": "The image SKU"
                                    },
                                    "version": {
                                        "type": "string",
                                        "description": "The image version",
                                        "default": "latest"
                                    }
                                },
                                "required": ["publisher", "offer", "sku"]
                            },
                            "osDisk": {
                                "type": "object",
                                "description": "Operating system disk settings",
                                "properties": {
                                    "name": {
                                        "type": "string",
                                        "description": "The disk name"
                                    },
                                    "caching": {
                                        "enum": ["None", "ReadOnly", "ReadWrite"],
                                        "description": "Disk caching type"
                                    },
                                    "createOption": {
                                        "enum": ["FromImage", "Empty", "Attach"],
                                        "description": "How the disk should be created"
                                    },
                                    "managedDisk": {
                                        "type": "object",
                                        "description": "Managed disk settings",
                                        "properties": {
                                            "storageAccountType": {
                                                "enum": ["Standard_LRS", "Premium_LRS", "StandardSSD_LRS", "UltraSSD_LRS"],
                                                "description": "Storage account type for managed disk"
                                            }
                                        },
                                        "required": ["storageAccountType"]
                                    }
                                },
                                "required": ["createOption"]
                            },
                            "dataDisks": {
                                "type": "array",
                                "description": "Data disk settings",
                                "items": {
                                    "type": "object",
                                    "properties": {
                                        "lun": {
                                            "type": "integer",
                                            "description": "Logical unit number",
                                            "minimum": 0,
                                            "maximum": 63
                                        },
                                        "name": {
                                            "type": "string",
                                            "description": "The disk name"
                                        },
                                        "caching": {
                                            "enum": ["None", "ReadOnly", "ReadWrite"],
                                            "description": "Disk caching type"
                                        },
                                        "createOption": {
                                            "enum": ["FromImage", "Empty", "Attach"],
                                            "description": "How the disk should be created"
                                        },
                                        "diskSizeGB": {
                                            "type": "integer",
                                            "description": "Disk size in GB",
                                            "minimum": 1,
                                            "maximum": 32767
                                        }
                                    },
                                    "required": ["lun", "createOption"]
                                }
                            }
                        },
                        "required": ["imageReference", "osDisk"]
                    },
                    "osProfile": {
                        "type": "object",
                        "description": "Operating system settings",
                        "properties": {
                            "computerName": {
                                "type": "string",
                                "description": "Computer name for the VM",
                                "maxLength": 15
                            },
                            "adminUsername": {
                                "type": "string",
                                "description": "Administrator username"
                            },
                            "adminPassword": {
                                "type": "string",
                                "description": "Administrator password"
                            },
                            "customData": {
                                "type": "string",
                                "description": "Base64 encoded custom data"
                            },
                            "windowsConfiguration": {
                                "type": "object",
                                "description": "Windows-specific configuration",
                                "properties": {
                                    "provisionVMAgent": {
                                        "type": "boolean",
                                        "description": "Provision VM agent",
                                        "default": true
                                    },
                                    "enableAutomaticUpdates": {
                                        "type": "boolean",
                                        "description": "Enable automatic updates",
                                        "default": true
                                    }
                                }
                            },
                            "linuxConfiguration": {
                                "type": "object",
                                "description": "Linux-specific configuration",
                                "properties": {
                                    "disablePasswordAuthentication": {
                                        "type": "boolean",
                                        "description": "Disable password authentication",
                                        "default": false
                                    }
                                }
                            }
                        },
                        "required": ["computerName", "adminUsername"]
                    },
                    "networkProfile": {
                        "type": "object",
                        "description": "Network settings for the virtual machine",
                        "properties": {
                            "networkInterfaces": {
                                "type": "array",
                                "description": "Network interfaces for the VM",
                                "items": {
                                    "type": "object",
                                    "properties": {
                                        "id": {
                                            "type": "string",
                                            "description": "Resource ID of the network interface"
                                        },
                                        "primary": {
                                            "type": "boolean",
                                            "description": "Whether this is the primary network interface",
                                            "default": false
                                        }
                                    },
                                    "required": ["id"]
                                },
                                "minItems": 1
                            }
                        },
                        "required": ["networkInterfaces"]
                    }
                },
                "required": ["hardwareProfile", "storageProfile", "osProfile", "networkProfile"]
            },
            "tags": {
                "type": "object",
                "description": "Resource tags",
                "additionalProperties": {
                    "type": "string"
                }
            }
        },
        "required": ["apiVersion", "name", "location", "type", "properties"]
    }"#;

    let s = Schema::from_json_str(schema).unwrap();
    match s.as_type() {
        Type::Object { properties, .. } => {
            // Verify core VM properties
            assert!(properties.contains_key("name"));
            assert!(properties.contains_key("location"));
            assert!(properties.contains_key("type"));
            assert!(properties.contains_key("properties"));

            // Verify VM type constant
            match properties.get("type").unwrap().as_type() {
                Type::Const { value, .. } => {
                    assert_eq!(value, &Value::from("Microsoft.Compute/virtualMachines"));
                }
                _ => panic!("Expected type to be Type::Const"),
            }

            // Verify nested properties structure
            match properties.get("properties").unwrap().as_type() {
                Type::Object {
                    properties: vm_props,
                    required: vm_req,
                    ..
                } => {
                    assert!(vm_props.contains_key("hardwareProfile"));
                    assert!(vm_props.contains_key("storageProfile"));
                    assert!(vm_props.contains_key("osProfile"));
                    assert!(vm_props.contains_key("networkProfile"));

                    let vm_required = vm_req
                        .as_ref()
                        .expect("VM properties required should be present");
                    assert!(vm_required.contains(&"hardwareProfile".into()));
                    assert!(vm_required.contains(&"storageProfile".into()));
                    assert!(vm_required.contains(&"osProfile".into()));
                    assert!(vm_required.contains(&"networkProfile".into()));
                }
                _ => panic!("Expected properties to be Type::Object"),
            }
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_azure_resource_polymorphic_schema() {
    // This demonstrates a polymorphic Azure resource schema using discriminated subobjects
    let schema = r#"{
        "type": "object",
        "description": "Polymorphic Azure resource schema",
        "properties": {
            "apiVersion": {
                "type": "string",
                "description": "The API version for the resource"
            },
            "name": {
                "type": "string",
                "description": "The resource name",
                "minLength": 1,
                "maxLength": 260
            },
            "location": {
                "type": "string",
                "description": "The Azure region where the resource is deployed"
            },
            "type": {
                "type": "string",
                "description": "The resource type"
            },
            "tags": {
                "type": "object",
                "description": "Resource tags",
                "additionalProperties": {
                    "type": "string"
                }
            }
        },
        "required": ["apiVersion", "name", "location", "type"],
        "allOf": [
            {
                "if": {
                    "properties": {
                        "type": { "const": "Microsoft.Storage/storageAccounts" }
                    }
                },
                "then": {
                    "properties": {
                        "kind": {
                            "enum": ["Storage", "StorageV2", "BlobStorage"],
                            "description": "Storage account kind"
                        },
                        "sku": {
                            "type": "object",
                            "properties": {
                                "name": {
                                    "enum": ["Standard_LRS", "Standard_GRS", "Premium_LRS"]
                                }
                            },
                            "required": ["name"]
                        },
                        "properties": {
                            "type": "object",
                            "properties": {
                                "accessTier": {
                                    "enum": ["Hot", "Cool", "Archive"]
                                },
                                "supportsHttpsTrafficOnly": {
                                    "type": "boolean",
                                    "default": true
                                }
                            }
                        }
                    },
                    "required": ["kind", "sku"]
                }
            },
            {
                "if": {
                    "properties": {
                        "type": { "const": "Microsoft.Compute/virtualMachines" }
                    }
                },
                "then": {
                    "properties": {
                        "properties": {
                            "type": "object",
                            "properties": {
                                "hardwareProfile": {
                                    "type": "object",
                                    "properties": {
                                        "vmSize": {
                                            "enum": ["Standard_B1s", "Standard_D2s_v3", "Standard_F2s_v2"]
                                        }
                                    },
                                    "required": ["vmSize"]
                                },
                                "osProfile": {
                                    "type": "object",
                                    "properties": {
                                        "computerName": {
                                            "type": "string",
                                            "maxLength": 15
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
                    "required": ["properties"]
                }
            },
            {
                "if": {
                    "properties": {
                        "type": { "const": "Microsoft.Network/virtualNetworks" }
                    }
                },
                "then": {
                    "properties": {
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
                                                "description": "CIDR block for the virtual network"
                                            },
                                            "minItems": 1
                                        }
                                    },
                                    "required": ["addressPrefixes"]
                                },
                                "subnets": {
                                    "type": "array",
                                    "description": "Subnets in the virtual network",
                                    "items": {
                                        "type": "object",
                                        "properties": {
                                            "name": {
                                                "type": "string",
                                                "description": "Subnet name"
                                            },
                                            "properties": {
                                                "type": "object",
                                                "properties": {
                                                    "addressPrefix": {
                                                        "type": "string",
                                                        "description": "CIDR block for the subnet"
                                                    },
                                                    "networkSecurityGroup": {
                                                        "type": "object",
                                                        "properties": {
                                                            "id": {
                                                                "type": "string",
                                                                "description": "Resource ID of the NSG"
                                                            }
                                                        },
                                                        "required": ["id"]
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
                    "required": ["properties"]
                }
            },
            {
                "if": {
                    "properties": {
                        "type": { "const": "Microsoft.Web/sites" }
                    }
                },
                "then": {
                    "properties": {
                        "kind": {
                            "enum": ["app", "functionapp", "api", "mobileapp"],
                            "description": "Web app kind"
                        },
                        "properties": {
                            "type": "object",
                            "properties": {
                                "serverFarmId": {
                                    "type": "string",
                                    "description": "Resource ID of the App Service plan"
                                },
                                "httpsOnly": {
                                    "type": "boolean",
                                    "description": "HTTPS only traffic",
                                    "default": false
                                },
                                "siteConfig": {
                                    "type": "object",
                                    "properties": {
                                        "appSettings": {
                                            "type": "array",
                                            "description": "Application settings",
                                            "items": {
                                                "type": "object",
                                                "properties": {
                                                    "name": {
                                                        "type": "string",
                                                        "description": "Setting name"
                                                    },
                                                    "value": {
                                                        "type": "string",
                                                        "description": "Setting value"
                                                    }
                                                },
                                                "required": ["name", "value"]
                                            }
                                        },
                                        "netFrameworkVersion": {
                                            "enum": ["v4.0", "v6.0", "v7.0", "v8.0"],
                                            "description": ".NET Framework version"
                                        }
                                    }
                                }
                            },
                            "required": ["serverFarmId"]
                        }
                    },
                    "required": ["kind", "properties"]
                }
            }
        ]
    }"#;

    let s = Schema::from_json_str(schema).unwrap();
    match s.as_type() {
        Type::Object {
            discriminated_subobject,
            properties,
            required,
            ..
        } => {
            // Verify base properties
            assert!(properties.contains_key("name"));
            assert!(properties.contains_key("location"));
            assert!(properties.contains_key("type"));
            assert!(properties.contains_key("apiVersion"));

            let req = required.as_ref().expect("required should be present");
            assert!(req.contains(&"name".into()));
            assert!(req.contains(&"location".into()));
            assert!(req.contains(&"type".into()));
            assert!(req.contains(&"apiVersion".into()));

            // Verify discriminated subobject
            let dso = discriminated_subobject
                .as_ref()
                .expect("should have discriminated_subobject");
            assert_eq!(dso.discriminator.as_ref(), "type");
            assert_eq!(dso.variants.len(), 4);

            // Verify storage account variant
            let storage_variant = dso
                .variants
                .get("Microsoft.Storage/storageAccounts")
                .expect("storage account variant");
            assert!(storage_variant.properties.contains_key("kind"));
            assert!(storage_variant.properties.contains_key("sku"));
            let storage_req = storage_variant.required.as_ref().expect("storage required");
            assert!(storage_req.contains(&"kind".into()));
            assert!(storage_req.contains(&"sku".into()));

            // Verify VM variant
            let vm_variant = dso
                .variants
                .get("Microsoft.Compute/virtualMachines")
                .expect("VM variant");
            assert!(vm_variant.properties.contains_key("properties"));
            let vm_req = vm_variant.required.as_ref().expect("VM required");
            assert!(vm_req.contains(&"properties".into()));

            // Verify VNet variant
            let vnet_variant = dso
                .variants
                .get("Microsoft.Network/virtualNetworks")
                .expect("VNet variant");
            assert!(vnet_variant.properties.contains_key("properties"));

            // Verify Web App variant
            let webapp_variant = dso
                .variants
                .get("Microsoft.Web/sites")
                .expect("Web App variant");
            assert!(webapp_variant.properties.contains_key("kind"));
            assert!(webapp_variant.properties.contains_key("properties"));
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_azure_key_vault_schema() {
    let schema = r#"{
        "type": "object",
        "description": "Azure Key Vault resource schema",
        "properties": {
            "apiVersion": {
                "type": "string",
                "description": "The API version for the resource"
            },
            "name": {
                "type": "string",
                "description": "The name of the key vault",
                "minLength": 3,
                "maxLength": 24,
                "pattern": "^[a-zA-Z0-9-]+$"
            },
            "location": {
                "type": "string",
                "description": "The Azure region where the resource is deployed"
            },
            "type": {
                "const": "Microsoft.KeyVault/vaults"
            },
            "properties": {
                "type": "object",
                "description": "Key vault properties",
                "properties": {
                    "tenantId": {
                        "type": "string",
                        "description": "The Azure Active Directory tenant ID",
                        "pattern": "^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$"
                    },
                    "sku": {
                        "type": "object",
                        "description": "SKU details for the key vault",
                        "properties": {
                            "family": {
                                "const": "A"
                            },
                            "name": {
                                "enum": ["standard", "premium"],
                                "description": "SKU name"
                            }
                        },
                        "required": ["family", "name"]
                    },
                    "accessPolicies": {
                        "type": "array",
                        "description": "Access policies for the key vault",
                        "items": {
                            "type": "object",
                            "properties": {
                                "tenantId": {
                                    "type": "string",
                                    "description": "The Azure Active Directory tenant ID"
                                },
                                "objectId": {
                                    "type": "string",
                                    "description": "The object ID of a user, service principal or security group"
                                },
                                "permissions": {
                                    "type": "object",
                                    "description": "Permissions the identity has for keys, secrets and certificates",
                                    "properties": {
                                        "keys": {
                                            "type": "array",
                                            "description": "Permissions to keys",
                                            "items": {
                                                "enum": [
                                                    "encrypt", "decrypt", "wrapKey", "unwrapKey", "sign", "verify",
                                                    "get", "list", "create", "update", "import", "delete", "backup",
                                                    "restore", "recover", "purge", "release", "rotate", "getrotationpolicy", "setrotationpolicy"
                                                ]
                                            }
                                        },
                                        "secrets": {
                                            "type": "array",
                                            "description": "Permissions to secrets",
                                            "items": {
                                                "enum": ["get", "list", "set", "delete", "backup", "restore", "recover", "purge"]
                                            }
                                        },
                                        "certificates": {
                                            "type": "array",
                                            "description": "Permissions to certificates",
                                            "items": {
                                                "enum": [
                                                    "get", "list", "delete", "create", "import", "update", "managecontacts",
                                                    "getissuers", "listissuers", "setissuers", "deleteissuers", "manageissuers",
                                                    "recover", "purge", "backup", "restore"
                                                ]
                                            }
                                        }
                                    }
                                }
                            },
                            "required": ["tenantId", "objectId", "permissions"]
                        }
                    },
                    "enabledForDeployment": {
                        "type": "boolean",
                        "description": "Property to specify whether Azure Virtual Machines are permitted to retrieve certificates",
                        "default": false
                    },
                    "enabledForDiskEncryption": {
                        "type": "boolean",
                        "description": "Property to specify whether Azure Disk Encryption is permitted to retrieve secrets",
                        "default": false
                    },
                    "enabledForTemplateDeployment": {
                        "type": "boolean",
                        "description": "Property to specify whether Azure Resource Manager is permitted to retrieve secrets",
                        "default": false
                    },
                    "enableSoftDelete": {
                        "type": "boolean",
                        "description": "Property to specify whether the soft delete functionality is enabled",
                        "default": true
                    },
                    "softDeleteRetentionInDays": {
                        "type": "integer",
                        "description": "The number of days that items should be retained for once soft-deleted",
                        "minimum": 7,
                        "maximum": 90,
                        "default": 90
                    },
                    "enablePurgeProtection": {
                        "type": "boolean",
                        "description": "Property specifying whether protection against purge is enabled",
                        "default": false
                    },
                    "networkAcls": {
                        "type": "object",
                        "description": "Rules governing the accessibility of the key vault from specific network locations",
                        "properties": {
                            "bypass": {
                                "enum": ["AzureServices", "None"],
                                "description": "Tells what traffic can bypass network rules"
                            },
                            "defaultAction": {
                                "enum": ["Allow", "Deny"],
                                "description": "The default action when no rule from ipRules and from virtualNetworkRules match"
                            },
                            "ipRules": {
                                "type": "array",
                                "description": "The list of IP address rules",
                                "items": {
                                    "type": "object",
                                    "properties": {
                                        "value": {
                                            "type": "string",
                                            "description": "An IPv4 address range in CIDR notation"
                                        }
                                    },
                                    "required": ["value"]
                                }
                            },
                            "virtualNetworkRules": {
                                "type": "array",
                                "description": "The list of virtual network rules",
                                "items": {
                                    "type": "object",
                                    "properties": {
                                        "id": {
                                            "type": "string",
                                            "description": "Full resource id of a vnet subnet"
                                        },
                                        "ignoreMissingVnetServiceEndpoint": {
                                            "type": "boolean",
                                            "description": "Property to specify whether NRP will ignore the check if parent subnet has serviceEndpoints configured",
                                            "default": false
                                        }
                                    },
                                    "required": ["id"]
                                }
                            }
                        },
                        "required": ["defaultAction"]
                    }
                },
                "required": ["tenantId", "sku", "accessPolicies"]
            },
            "tags": {
                "type": "object",
                "description": "Resource tags",
                "additionalProperties": {
                    "type": "string"
                }
            }
        },
        "required": ["apiVersion", "name", "location", "type", "properties"]
    }"#;

    let s = Schema::from_json_str(schema).unwrap();
    match s.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            // Verify Key Vault specific properties
            assert!(properties.contains_key("name"));
            assert!(properties.contains_key("type"));
            assert!(properties.contains_key("properties"));

            // Verify name constraints
            match properties.get("name").unwrap().as_type() {
                Type::String {
                    min_length,
                    max_length,
                    pattern,
                    ..
                } => {
                    assert_eq!(min_length, &Some(3));
                    assert_eq!(max_length, &Some(24));
                    assert!(pattern.is_some());
                }
                _ => panic!("Expected name to be Type::String"),
            }

            // Verify type constant
            match properties.get("type").unwrap().as_type() {
                Type::Const { value, .. } => {
                    assert_eq!(value, &Value::from("Microsoft.KeyVault/vaults"));
                }
                _ => panic!("Expected type to be Type::Const"),
            }

            // Verify complex nested properties structure
            match properties.get("properties").unwrap().as_type() {
                Type::Object {
                    properties: kv_props,
                    required: kv_req,
                    ..
                } => {
                    assert!(kv_props.contains_key("tenantId"));
                    assert!(kv_props.contains_key("sku"));
                    assert!(kv_props.contains_key("accessPolicies"));

                    let kv_required = kv_req
                        .as_ref()
                        .expect("Key Vault properties required should be present");
                    assert!(kv_required.contains(&"tenantId".into()));
                    assert!(kv_required.contains(&"sku".into()));
                    assert!(kv_required.contains(&"accessPolicies".into()));

                    // Verify access policies array structure
                    match kv_props.get("accessPolicies").unwrap().as_type() {
                        Type::Array { items, .. } => match items.as_type() {
                            Type::Object {
                                properties: policy_props,
                                ..
                            } => {
                                assert!(policy_props.contains_key("tenantId"));
                                assert!(policy_props.contains_key("objectId"));
                                assert!(policy_props.contains_key("permissions"));
                            }
                            _ => panic!("Expected access policy items to be Type::Object"),
                        },
                        _ => panic!("Expected accessPolicies to be Type::Array"),
                    }
                }
                _ => panic!("Expected properties to be Type::Object"),
            }

            // Verify required fields
            let req = required.as_ref().expect("required should be present");
            assert!(req.contains(&"name".into()));
            assert!(req.contains(&"type".into()));
            assert!(req.contains(&"properties".into()));
        }
        _ => panic!("Expected Type::Object"),
    }
}

#[test]
fn test_azure_app_service_plan_schema() {
    let schema = r#"{
        "type": "object",
        "description": "Azure App Service Plan resource schema",
        "properties": {
            "apiVersion": {
                "type": "string",
                "description": "The API version for the resource"
            },
            "name": {
                "type": "string",
                "description": "The name of the App Service plan",
                "minLength": 1,
                "maxLength": 40
            },
            "location": {
                "type": "string",
                "description": "The Azure region where the resource is deployed"
            },
            "type": {
                "const": "Microsoft.Web/serverfarms"
            },
            "sku": {
                "type": "object",
                "description": "SKU description of the App Service plan",
                "properties": {
                    "name": {
                        "enum": ["F1", "D1", "B1", "B2", "B3", "S1", "S2", "S3", "P1", "P2", "P3", "P1V2", "P2V2", "P3V2", "P1V3", "P2V3", "P3V3"],
                        "description": "Name of the SKU"
                    },
                    "tier": {
                        "enum": ["Free", "Shared", "Basic", "Standard", "Premium", "PremiumV2", "PremiumV3"],
                        "description": "Service tier of the SKU"
                    },
                    "size": {
                        "enum": ["F1", "D1", "B1", "B2", "B3", "S1", "S2", "S3", "P1", "P2", "P3", "P1V2", "P2V2", "P3V2", "P1V3", "P2V3", "P3V3"],
                        "description": "Size specifier of the SKU"
                    },
                    "family": {
                        "type": "string",
                        "description": "Family code of the SKU"
                    },
                    "capacity": {
                        "type": "integer",
                        "description": "Current number of instances assigned to the resource",
                        "minimum": 0,
                        "maximum": 100
                    }
                },
                "required": ["name"]
            },
            "kind": {
                "enum": ["app", "linux", "functionapp", "elastic"],
                "description": "Kind of resource"
            },
            "properties": {
                "type": "object",
                "description": "App Service plan properties",
                "properties": {
                    "workerTierName": {
                        "type": "string",
                        "description": "Target worker tier assigned to the App Service plan"
                    },
                    "hostingEnvironmentProfile": {
                        "type": "object",
                        "description": "Specification for the App Service Environment",
                        "properties": {
                            "id": {
                                "type": "string",
                                "description": "Resource ID of the App Service Environment"
                            }
                        },
                        "required": ["id"]
                    },
                    "perSiteScaling": {
                        "type": "boolean",
                        "description": "If true, apps assigned to this App Service plan can be scaled independently",
                        "default": false
                    },
                    "elasticScaleEnabled": {
                        "type": "boolean",
                        "description": "ServerFarm supports ElasticScale. Apps in this plan will scale as if the ServerFarm was ElasticPremium sku",
                        "default": false
                    },
                    "maximumElasticWorkerCount": {
                        "type": "integer",
                        "description": "Maximum number of total workers allowed for this ElasticScaleEnabled App Service Plan",
                        "minimum": 1,
                        "maximum": 100
                    },
                    "isSpot": {
                        "type": "boolean",
                        "description": "If true, this App Service Plan owns spot instances",
                        "default": false
                    },
                    "spotExpirationTime": {
                        "type": "string",
                        "description": "The time when the server farm expires. Valid only if it is a spot server farm"
                    },
                    "freeOfferExpirationTime": {
                        "type": "string",
                        "description": "The time when the server farm free offer expires"
                    },
                    "reserved": {
                        "type": "boolean",
                        "description": "If Linux app service plan true, false otherwise",
                        "default": false
                    },
                    "isXenon": {
                        "type": "boolean",
                        "description": "Obsolete: Hyper-V sandbox",
                        "default": false
                    },
                    "hyperV": {
                        "type": "boolean",
                        "description": "If Hyper-V container app service plan true, false otherwise",
                        "default": false
                    },
                    "targetWorkerCount": {
                        "type": "integer",
                        "description": "Scaling worker count",
                        "minimum": 0,
                        "maximum": 100
                    },
                    "targetWorkerSizeId": {
                        "type": "integer",
                        "description": "Scaling worker size ID",
                        "minimum": 0,
                        "maximum": 2
                    },
                    "kubeEnvironmentProfile": {
                        "type": "object",
                        "description": "Specification for the Kubernetes Environment",
                        "properties": {
                            "id": {
                                "type": "string",
                                "description": "Resource ID of the Kubernetes Environment"
                            }
                        },
                        "required": ["id"]
                    }
                }
            },
            "tags": {
                "type": "object",
                "description": "Resource tags",
                "additionalProperties": {
                    "type": "string"
                }
            }
        },
        "required": ["apiVersion", "name", "location", "type", "sku"]
    }"#;

    let s = Schema::from_json_str(schema).unwrap();
    match s.as_type() {
        Type::Object {
            properties,
            required,
            ..
        } => {
            // Verify App Service Plan specific properties
            assert!(properties.contains_key("name"));
            assert!(properties.contains_key("type"));
            assert!(properties.contains_key("sku"));
            assert!(properties.contains_key("kind"));

            // Verify type constant
            match properties.get("type").unwrap().as_type() {
                Type::Const { value, .. } => {
                    assert_eq!(value, &Value::from("Microsoft.Web/serverfarms"));
                }
                _ => panic!("Expected type to be Type::Const"),
            }

            // Verify SKU structure
            match properties.get("sku").unwrap().as_type() {
                Type::Object {
                    properties: sku_props,
                    required: sku_req,
                    ..
                } => {
                    assert!(sku_props.contains_key("name"));
                    assert!(sku_props.contains_key("tier"));
                    assert!(sku_props.contains_key("capacity"));

                    // Verify SKU name enum
                    match sku_props.get("name").unwrap().as_type() {
                        Type::Enum { values, .. } => {
                            assert!(values.contains(&Value::from("B1")));
                            assert!(values.contains(&Value::from("S1")));
                            assert!(values.contains(&Value::from("P1V3")));
                        }
                        _ => panic!("Expected SKU name to be Type::Enum"),
                    }

                    // Verify SKU tier enum
                    match sku_props.get("tier").unwrap().as_type() {
                        Type::Enum { values, .. } => {
                            assert!(values.contains(&Value::from("Basic")));
                            assert!(values.contains(&Value::from("Standard")));
                            assert!(values.contains(&Value::from("PremiumV3")));
                        }
                        _ => panic!("Expected SKU tier to be Type::Enum"),
                    }

                    let sku_required = sku_req.as_ref().expect("SKU required should be present");
                    assert!(sku_required.contains(&"name".into()));
                }
                _ => panic!("Expected sku to be Type::Object"),
            }

            // Verify kind enum
            match properties.get("kind").unwrap().as_type() {
                Type::Enum { values, .. } => {
                    assert!(values.contains(&Value::from("app")));
                    assert!(values.contains(&Value::from("linux")));
                    assert!(values.contains(&Value::from("functionapp")));
                }
                _ => panic!("Expected kind to be Type::Enum"),
            }

            // Verify required fields
            let req = required.as_ref().expect("required should be present");
            assert!(req.contains(&"name".into()));
            assert!(req.contains(&"type".into()));
            assert!(req.contains(&"sku".into()));
        }
        _ => panic!("Expected Type::Object"),
    }
}
