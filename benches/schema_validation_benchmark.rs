use criterion::{criterion_group, criterion_main, Criterion};
use regorus::Value;
use regorus::{Schema, SchemaValidator};
use serde_json::json;

// Observed: validate_string - 3.19 ns/iter
fn bench_string_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "string",
        "minLength": 3,
        "maxLength": 10
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from("hello");

    c.bench_function("validate_string", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_number - 146.5 ns/iter
fn bench_number_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "number",
        "minimum": 0.0,
        "maximum": 100.0
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(42.5);

    c.bench_function("validate_number", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_array - 95.0 ns/iter
fn bench_array_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "array",
        "items": { "type": "integer" },
        "minItems": 2,
        "maxItems": 5
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!([1, 2, 3]));

    c.bench_function("validate_array", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_object - 126.9 ns/iter
fn bench_object_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "name": { "type": "string" },
            "age": { "type": "integer", "minimum": 0 }
        },
        "required": ["name", "age"]
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({"name": "Alice", "age": 30}));

    c.bench_function("validate_object", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_complex_nested - 710.5 ns/iter
fn bench_complex_nested_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "user": {
                "type": "object",
                "properties": {
                    "id": { "type": "string" },
                    "profile": {
                        "type": "object",
                        "properties": {
                            "email": { "type": "string" },
                            "roles": {
                                "type": "array",
                                "items": { "type": "string" }
                            }
                        },
                        "required": ["email", "roles"]
                    }
                },
                "required": ["id", "profile"]
            },
            "active": { "type": "boolean" }
        },
        "required": ["user", "active"]
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
        "user": {
            "id": "u123",
            "profile": {
                "email": "alice@example.com",
                "roles": ["admin", "user"]
            }
        },
        "active": true
    }));

    c.bench_function("validate_complex_nested", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_string_pattern - 29.99 µs/iter
fn bench_string_pattern_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "string",
        "pattern": "^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}$"
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from("user@example.com");

    c.bench_function("validate_string_pattern", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_enum - 7.26 ns/iter
fn bench_enum_validation(c: &mut Criterion) {
    let schema_json = json!({
        "enum": ["pending", "approved", "rejected", "cancelled"]
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from("approved");

    c.bench_function("validate_enum", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_boolean - 3.22 ns/iter
fn bench_boolean_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "boolean"
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(true);

    c.bench_function("validate_boolean", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_null - 3.22 ns/iter
fn bench_null_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "null"
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::Null;

    c.bench_function("validate_null", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_large_array - 17.30 µs/iter
fn bench_large_array_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "array",
        "items": { "type": "number" },
        "minItems": 50,
        "maxItems": 200
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let large_array: Vec<_> = (0..100).map(|i| json!(i as f64)).collect();
    let value = Value::from(json!(large_array));

    c.bench_function("validate_large_array", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_deeply_nested - 468.2 ns/iter
fn bench_deeply_nested_object(c: &mut Criterion) {
    let schema_json = json!({
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
                                                "type": "string"
                                            }
                                        },
                                        "required": ["level5"]
                                    }
                                },
                                "required": ["level4"]
                            }
                        },
                        "required": ["level3"]
                    }
                },
                "required": ["level2"]
            }
        },
        "required": ["level1"]
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
        "level1": {
            "level2": {
                "level3": {
                    "level4": {
                        "level5": "deep value"
                    }
                }
            }
        }
    }));

    c.bench_function("validate_deeply_nested", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_mixed_type_array - 1.36 µs/iter
fn bench_mixed_type_array(c: &mut Criterion) {
    let schema_json = json!({
        "type": "array",
        "items": {
            "anyOf": [
                { "type": "string" },
                { "type": "number" },
                { "type": "boolean" }
            ]
        }
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!(["hello", 42, true, "world", 99.5, false]));

    c.bench_function("validate_mixed_type_array", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_additional_properties - 366.4 ns/iter
fn bench_additional_properties(c: &mut Criterion) {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "name": { "type": "string" },
            "age": { "type": "integer" }
        },
        "additionalProperties": { "type": "string" },
        "required": ["name"]
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
        "name": "Alice",
        "age": 30,
        "city": "New York",
        "country": "USA",
        "occupation": "Engineer"
    }));

    c.bench_function("validate_additional_properties", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_array_constraints - 146.2 ns/iter
fn bench_array_constraints(c: &mut Criterion) {
    let schema_json = json!({
        "type": "array",
        "items": { "type": "string" },
        "minItems": 2,
        "maxItems": 10
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!(["apple", "banana", "cherry", "date", "elderberry"]));

    c.bench_function("validate_array_constraints", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_multi_level - 915.8 ns/iter
fn bench_multi_level_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "user": {
                "type": "object",
                "properties": {
                    "profile": {
                        "type": "object",
                        "properties": {
                            "settings": {
                                "type": "object",
                                "properties": {
                                    "theme": {
                                        "enum": ["light", "dark", "auto"]
                                    },
                                    "notifications": {
                                        "type": "boolean"
                                    }
                                },
                                "required": ["theme"],
                                "additionalProperties": { "type": "string" }
                            }
                        },
                        "required": ["settings"],
                        "additionalProperties": { "type": "any" }
                    }
                },
                "required": ["profile"],
                "additionalProperties": { "type": "any" }
            }
        },
        "required": ["user"],
        "additionalProperties": { "type": "any" }
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
        "user": {
            "profile": {
                "settings": {
                    "theme": "dark",
                    "notifications": true,
                    "language": "en"
                },
                "avatar": "default.png"
            },
            "lastLogin": "2024-01-01"
        },
        "metadata": "extra info"
    }));

    c.bench_function("validate_multi_level", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Azure Resource Validation Benchmarks

// Observed: validate_azure_vm_resource - 34.74 µs/iter
fn bench_azure_vm_resource_validation(c: &mut Criterion) {
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
        "additionalProperties": { "type": "any" }
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
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
    }));

    c.bench_function("validate_azure_vm_resource", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_azure_storage_resource - 22.12 µs/iter
fn bench_azure_storage_resource_validation(c: &mut Criterion) {
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
                "type": "string"
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
                        "enum": ["Hot", "Cool", "Archive"]
                    },
                    "encryption": {
                        "type": "object",
                        "properties": {
                            "services": {
                                "type": "object"
                            }
                        }
                    }
                },
                "additionalProperties": { "type": "any" }
            }
        },
        "required": ["type", "apiVersion", "name", "location", "sku", "kind"],
        "additionalProperties": { "type": "any" }
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
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
    }));

    c.bench_function("validate_azure_storage_resource", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_azure_arm_template - 1.99 µs/iter
fn bench_azure_arm_template_validation(c: &mut Criterion) {
    let schema_json = json!({
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
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
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
    }));

    c.bench_function("validate_azure_arm_template", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Azure Policy Effect Validation Benchmarks

// Observed: validate_azure_policy_deny_effect - 188.6 ns/iter
fn bench_azure_policy_deny_effect_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "effect": {
                "const": "deny"
            },
            "description": {
                "type": "string"
            }
        },
        "required": ["effect"],
        "additionalProperties": { "type": "any" }
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
        "effect": "deny",
        "description": "Deny resources that don't meet security requirements"
    }));

    c.bench_function("validate_azure_policy_deny_effect", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_azure_policy_audit_effect - 516.7 ns/iter
fn bench_azure_policy_audit_effect_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "effect": {
                "const": "audit"
            },
            "description": {
                "type": "string"
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
                },
                "additionalProperties": { "type": "any" }
            }
        },
        "required": ["effect"],
        "additionalProperties": { "type": "any" }
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
        "effect": "audit",
        "description": "Audit non-compliant resources",
        "auditDetails": {
            "category": "security",
            "severity": "high"
        }
    }));

    c.bench_function("validate_azure_policy_audit_effect", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_azure_policy_modify_effect - 1.17 µs/iter
fn bench_azure_policy_modify_effect_validation(c: &mut Criterion) {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "effect": {
                "const": "modify"
            },
            "description": {
                "type": "string"
            },
            "modifyDetails": {
                "type": "object",
                "properties": {
                    "roleDefinitionIds": {
                        "type": "array",
                        "items": { "type": "string" }
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
                                "type": "any"
                            }
                            },
                            "required": ["operation", "field"],
                            "additionalProperties": { "type": "any" }
                        }
                    }
                },
                "required": ["roleDefinitionIds", "operations"],
                "additionalProperties": { "type": "any" }
            }
        },
        "required": ["effect", "modifyDetails"],
        "additionalProperties": { "type": "any" }
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
        "effect": "modify",
        "description": "Modify resources to ensure compliance",
        "modifyDetails": {
            "roleDefinitionIds": [
                "/providers/Microsoft.Authorization/roleDefinitions/b24988ac-6180-42a0-ab88-20f7382dd24c"
            ],
            "operations": [
                {
                    "operation": "add",
                    "field": "tags.environment",
                    "value": "production"
                }
            ]
        }
    }));

    c.bench_function("validate_azure_policy_modify_effect", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

// Observed: validate_azure_policy_complex_effect - 1.40 µs/iter
fn bench_azure_policy_complex_effect_validation(c: &mut Criterion) {
    let schema_json = json!({
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
    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    let value = Value::from(json!({
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
    }));

    c.bench_function("validate_azure_policy_complex_effect", |b| {
        b.iter(|| {
            SchemaValidator::validate(&value, &schema).unwrap();
        })
    });
}

criterion_group!(
    schema_validation_benches,
    bench_string_validation,
    bench_number_validation,
    bench_array_validation,
    bench_object_validation,
    bench_complex_nested_validation,
    bench_string_pattern_validation,
    bench_enum_validation,
    bench_boolean_validation,
    bench_null_validation,
    bench_large_array_validation,
    bench_deeply_nested_object,
    bench_mixed_type_array,
    bench_additional_properties,
    bench_array_constraints,
    bench_multi_level_validation,
    bench_azure_vm_resource_validation,
    bench_azure_storage_resource_validation,
    bench_azure_arm_template_validation,
    bench_azure_policy_deny_effect_validation,
    bench_azure_policy_audit_effect_validation,
    bench_azure_policy_modify_effect_validation,
    bench_azure_policy_complex_effect_validation
);
criterion_main!(schema_validation_benches);
