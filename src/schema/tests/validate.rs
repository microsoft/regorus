// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::{
    schema::{error::ValidationError, validate::SchemaValidator, Schema},
    *,
};
use alloc::collections::BTreeMap;
use serde_json::json;

#[test]
fn test_validate_integer() {
    let schema_json = json!({
        "type": "integer",
        "minimum": 0,
        "maximum": 100
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Valid integer
    assert!(SchemaValidator::validate(&Value::from(50), &schema).is_ok());

    // Invalid - below minimum
    let result = SchemaValidator::validate(&Value::from(-1), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::OutOfRange {
        value,
        min,
        max,
        path,
    }) = result
    {
        assert_eq!(value.as_ref(), "-1");
        assert_eq!(min.as_ref().map(|s| s.as_ref()), Some("0"));
        assert_eq!(max.as_ref().map(|s| s.as_ref()), Some("100"));
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected OutOfRange error");
    }

    // Invalid - above maximum
    let result = SchemaValidator::validate(&Value::from(101), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::OutOfRange {
        value,
        min,
        max,
        path,
    }) = result
    {
        assert_eq!(value.as_ref(), "101");
        assert_eq!(min.as_ref().map(|s| s.as_ref()), Some("0"));
        assert_eq!(max.as_ref().map(|s| s.as_ref()), Some("100"));
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected OutOfRange error");
    }

    // Invalid - not an integer
    let result = SchemaValidator::validate(&Value::from("string"), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::TypeMismatch {
        expected,
        actual,
        path,
    }) = result
    {
        assert_eq!(expected.as_ref(), "integer");
        assert_eq!(actual.as_ref(), "string");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected TypeMismatch error");
    }
}

#[test]
fn test_validate_string() {
    let schema_json = json!({
        "type": "string",
        "minLength": 2,
        "maxLength": 10,
        "pattern": "^[a-zA-Z]+$"
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Valid string
    assert!(SchemaValidator::validate(&Value::from("hello"), &schema).is_ok());

    // Invalid - too short
    let result = SchemaValidator::validate(&Value::from("a"), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::LengthConstraint {
        actual_length,
        min_length,
        max_length,
        path,
    }) = result
    {
        assert_eq!(actual_length, 1);
        assert_eq!(min_length, Some(2));
        assert_eq!(max_length, Some(10));
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected LengthConstraint error");
    }

    // Invalid - too long
    let result = SchemaValidator::validate(&Value::from("verylongstring"), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::LengthConstraint {
        actual_length,
        min_length,
        max_length,
        path,
    }) = result
    {
        assert_eq!(actual_length, 14);
        assert_eq!(min_length, Some(2));
        assert_eq!(max_length, Some(10));
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected LengthConstraint error");
    }

    // Invalid - pattern mismatch
    let result = SchemaValidator::validate(&Value::from("hello123"), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::PatternMismatch {
        value,
        pattern,
        path,
    }) = result
    {
        assert_eq!(value.as_ref(), "hello123");
        assert_eq!(pattern.as_ref(), "^[a-zA-Z]+$");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected PatternMismatch error");
    }

    // Invalid - not a string
    let result = SchemaValidator::validate(&Value::from(42), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::TypeMismatch {
        expected,
        actual,
        path,
    }) = result
    {
        assert_eq!(expected.as_ref(), "string");
        assert_eq!(actual.as_ref(), "number");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected TypeMismatch error");
    }
}

#[test]
fn test_validate_array() {
    let schema_json = json!({
        "type": "array",
        "items": { "type": "string" },
        "minItems": 1,
        "maxItems": 3
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Valid array
    let valid_json = json!(["item1", "item2"]);
    let valid_array = Value::from(valid_json);
    assert!(SchemaValidator::validate(&valid_array, &schema).is_ok());

    // Invalid - empty array (below minItems)
    let empty_json = json!([]);
    let empty_array = Value::from(empty_json);
    let result = SchemaValidator::validate(&empty_array, &schema);
    assert!(result.is_err());
    if let Err(ValidationError::ArraySizeConstraint {
        actual_size,
        min_items,
        max_items,
        path,
    }) = result
    {
        assert_eq!(actual_size, 0);
        assert_eq!(min_items, Some(1));
        assert_eq!(max_items, Some(3));
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected ArraySizeConstraint error");
    }

    // Invalid - too many items
    let large_json = json!(["item1", "item2", "item3", "item4"]);
    let large_array = Value::from(large_json);
    let result = SchemaValidator::validate(&large_array, &schema);
    assert!(result.is_err());
    if let Err(ValidationError::ArraySizeConstraint {
        actual_size,
        min_items,
        max_items,
        path,
    }) = result
    {
        assert_eq!(actual_size, 4);
        assert_eq!(min_items, Some(1));
        assert_eq!(max_items, Some(3));
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected ArraySizeConstraint error");
    }

    // Invalid - wrong item type
    let wrong_type_json = json!(["item1", 42]);
    let wrong_type_array = Value::from(wrong_type_json);
    let result = SchemaValidator::validate(&wrong_type_array, &schema);
    assert!(result.is_err());
    if let Err(ValidationError::ArrayItemValidationFailed { index, path, error }) = result {
        assert_eq!(index, 1);
        assert_eq!(path.as_ref(), "");

        // Assert the exact nested error
        if let ValidationError::TypeMismatch {
            expected, actual, ..
        } = error.as_ref()
        {
            assert_eq!(expected.as_ref(), "string");
            assert_eq!(actual.as_ref(), "number");
        } else {
            panic!("Expected nested TypeMismatch error in ArrayItemValidationFailed");
        }
    } else {
        panic!("Expected ArrayItemValidationFailed error");
    }
}

#[test]
fn test_validate_object() {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "name": { "type": "string" },
            "age": { "type": "integer", "minimum": 0 }
        },
        "required": ["name"]
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Valid object
    let valid_json = json!({
        "name": "John",
        "age": 30
    });
    let valid_object = Value::from(valid_json);
    assert!(SchemaValidator::validate(&valid_object, &schema).is_ok());

    // Invalid - missing required property
    let missing_json = json!({
        "age": 30
    });
    let missing_required = Value::from(missing_json);
    let result = SchemaValidator::validate(&missing_required, &schema);
    assert!(result.is_err());
    if let Err(ValidationError::MissingRequiredProperty { property, path }) = result {
        assert_eq!(property.as_ref(), "name");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected MissingRequiredProperty error");
    }

    // Invalid - wrong property type
    let wrong_type_json = json!({
        "name": "John",
        "age": "thirty"
    });
    let wrong_type_object = Value::from(wrong_type_json);
    let result = SchemaValidator::validate(&wrong_type_object, &schema);
    assert!(result.is_err());
    if let Err(ValidationError::PropertyValidationFailed {
        property,
        path,
        error: _,
    }) = result
    {
        assert_eq!(property.as_ref(), "age");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected PropertyValidationFailed error");
    }
}

#[test]
fn test_validate_enum() {
    let schema_json = json!({
        "enum": ["red", "green", "blue"]
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Valid enum value
    assert!(SchemaValidator::validate(&Value::from("red"), &schema).is_ok());

    // Invalid enum value
    let result = SchemaValidator::validate(&Value::from("yellow"), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::NotInEnum {
        value,
        allowed_values,
        path,
    }) = result
    {
        assert_eq!(value.as_ref(), "\"yellow\"");
        assert_eq!(allowed_values.len(), 3);
        assert!(allowed_values.contains(&"\"red\"".into()));
        assert!(allowed_values.contains(&"\"green\"".into()));
        assert!(allowed_values.contains(&"\"blue\"".into()));
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected NotInEnum error");
    }
}

#[test]
fn test_validate_const() {
    let schema_json = json!({
        "const": "specific_value"
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Valid const value
    assert!(SchemaValidator::validate(&Value::from("specific_value"), &schema).is_ok());

    // Invalid const value
    let result = SchemaValidator::validate(&Value::from("other_value"), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::ConstMismatch {
        expected,
        actual,
        path,
    }) = result
    {
        assert_eq!(expected.as_ref(), "\"specific_value\"");
        assert_eq!(actual.as_ref(), "\"other_value\"");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected ConstMismatch error");
    }
}

#[test]
fn test_validate_any_of() {
    let schema_json = json!({
        "anyOf": [
            { "type": "string" },
            { "type": "integer", "minimum": 0 }
        ]
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Valid - matches string schema
    assert!(SchemaValidator::validate(&Value::from("hello"), &schema).is_ok());

    // Valid - matches integer schema
    assert!(SchemaValidator::validate(&Value::from(42), &schema).is_ok());

    // Invalid - matches neither schema
    let result = SchemaValidator::validate(&Value::from(-1), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::NoUnionMatch { path, errors }) = result {
        assert_eq!(path.as_ref(), "");
        assert_eq!(errors.len(), 2); // Two schemas in anyOf, both should fail

        // First error should be TypeMismatch (string schema failure)
        if let ValidationError::TypeMismatch {
            expected, actual, ..
        } = &errors[0]
        {
            assert_eq!(expected.as_ref(), "string");
            assert_eq!(actual.as_ref(), "number");
        } else {
            panic!("Expected first error to be TypeMismatch for string schema");
        }

        // Second error should be OutOfRange (integer schema failure - value below minimum)
        if let ValidationError::OutOfRange {
            value, min, max, ..
        } = &errors[1]
        {
            assert_eq!(value.as_ref(), "-1");
            assert_eq!(min.as_ref().map(|s| s.as_ref()), Some("0"));
            assert_eq!(max, &None);
        } else {
            panic!("Expected second error to be OutOfRange for integer schema");
        }
    } else {
        panic!("Expected NoUnionMatch error");
    }
}

#[test]
fn test_validate_non_string_key() {
    let schema_json = json!({
        "type": "object",
        "properties": {
            "name": { "type": "string" }
        }
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Create an object with a non-string key (number)
    let mut invalid_obj = BTreeMap::new();
    invalid_obj.insert(Value::from(42), Value::from("value"));
    let invalid_object = Value::Object(Rc::new(invalid_obj));

    // This should fail because the key is not a string
    let result = SchemaValidator::validate(&invalid_object, &schema);
    assert!(result.is_err());

    if let Err(ValidationError::NonStringKey { key_type, path }) = result {
        assert_eq!(key_type.as_ref(), "number");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected NonStringKey error, got: {:?}", result);
    }
}

#[test]
fn test_validate_boolean() {
    let schema_json = json!({
        "type": "boolean"
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Valid boolean values
    assert!(SchemaValidator::validate(&Value::from(true), &schema).is_ok());
    assert!(SchemaValidator::validate(&Value::from(false), &schema).is_ok());

    // Invalid - not a boolean
    let result = SchemaValidator::validate(&Value::from("true"), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::TypeMismatch {
        expected,
        actual,
        path,
    }) = result
    {
        assert_eq!(expected.as_ref(), "boolean");
        assert_eq!(actual.as_ref(), "string");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected TypeMismatch error");
    }

    let result = SchemaValidator::validate(&Value::from(1), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::TypeMismatch {
        expected,
        actual,
        path,
    }) = result
    {
        assert_eq!(expected.as_ref(), "boolean");
        assert_eq!(actual.as_ref(), "number");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected TypeMismatch error");
    }
}

#[test]
fn test_validate_null() {
    let schema_json = json!({
        "type": "null"
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Valid null value
    assert!(SchemaValidator::validate(&Value::Null, &schema).is_ok());

    // Invalid - not null
    let result = SchemaValidator::validate(&Value::from("null"), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::TypeMismatch {
        expected,
        actual,
        path,
    }) = result
    {
        assert_eq!(expected.as_ref(), "null");
        assert_eq!(actual.as_ref(), "string");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected TypeMismatch error");
    }

    let result = SchemaValidator::validate(&Value::from(0), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::TypeMismatch {
        expected,
        actual,
        path,
    }) = result
    {
        assert_eq!(expected.as_ref(), "null");
        assert_eq!(actual.as_ref(), "number");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected TypeMismatch error");
    }
}

#[test]
fn test_validate_number() {
    let schema_json = json!({
        "type": "number",
        "minimum": 0.5,
        "maximum": 99.7
    });
    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Valid numbers
    assert!(SchemaValidator::validate(&Value::from(50.5), &schema).is_ok());
    assert!(SchemaValidator::validate(&Value::from(1), &schema).is_ok());
    assert!(SchemaValidator::validate(&Value::from(99), &schema).is_ok());

    // Invalid - below minimum
    let result = SchemaValidator::validate(&Value::from(0.3), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::OutOfRange {
        value,
        min,
        max,
        path,
    }) = result
    {
        assert_eq!(value.as_ref(), "0.3");
        assert_eq!(min.as_ref().map(|s| s.as_ref()), Some("0.5"));
        assert_eq!(max.as_ref().map(|s| s.as_ref()), Some("99.7"));
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected OutOfRange error");
    }

    // Invalid - above maximum
    let result = SchemaValidator::validate(&Value::from(100.2), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::OutOfRange {
        value,
        min,
        max,
        path,
    }) = result
    {
        assert_eq!(value.as_ref(), "100.2");
        assert_eq!(min.as_ref().map(|s| s.as_ref()), Some("0.5"));
        assert_eq!(max.as_ref().map(|s| s.as_ref()), Some("99.7"));
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected OutOfRange error");
    }

    // Invalid - not a number
    let result = SchemaValidator::validate(&Value::from("50.5"), &schema);
    assert!(result.is_err());
    if let Err(ValidationError::TypeMismatch {
        expected,
        actual,
        path,
    }) = result
    {
        assert_eq!(expected.as_ref(), "number");
        assert_eq!(actual.as_ref(), "string");
        assert_eq!(path.as_ref(), "");
    } else {
        panic!("Expected TypeMismatch error");
    }
}

#[test]
fn test_validate_discriminated_subobject() {
    // Test schema with discriminated subobjects (polymorphic objects)
    let schema_json = json!({
        "type": "object",
        "properties": {
            "name": {"type": "string"},
            "kind": {"type": "string"}
        },
        "required": ["name", "kind"],
        "allOf": [
            {
                "if": { "properties": { "kind": { "const": "user" } } },
                "then": {
                    "properties": {
                        "email": { "type": "string" },
                        "age": { "type": "integer" }
                    },
                    "required": ["email"]
                }
            },
            {
                "if": { "properties": { "kind": { "const": "admin" } } },
                "then": {
                    "properties": {
                        "permissions": { "type": "array", "items": { "type": "string" } },
                        "level": { "type": "integer" }
                    },
                    "required": ["permissions"]
                }
            }
        ]
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Test valid user object
    let user_json = json!({
        "name": "John",
        "kind": "user",
        "email": "john@example.com",
        "age": 30
    });
    let user_value = Value::from(user_json);

    let result = SchemaValidator::validate(&user_value, &schema);
    match &result {
        Ok(_) => {}
        Err(e) => panic!("User validation failed: {:?}", e),
    }

    // Test valid admin object
    let admin_json = json!({
        "name": "Alice",
        "kind": "admin",
        "permissions": ["read", "write"],
        "level": 5
    });
    let admin_value = Value::from(admin_json);

    let result = SchemaValidator::validate(&admin_value, &schema);
    assert!(result.is_ok(), "Valid admin object should pass validation");

    // Test object missing discriminator
    let invalid_json = json!({
        "name": "Bob"
    });
    let invalid_value = Value::from(invalid_json);

    let result = SchemaValidator::validate(&invalid_value, &schema);
    assert!(result.is_err(), "Object missing discriminator should fail");
    if let Err(ValidationError::MissingRequiredProperty { property, .. }) = result {
        assert_eq!(property.as_ref(), "kind");
    } else {
        panic!("Expected MissingRequiredProperty error for discriminator");
    }

    // Test unknown discriminator value
    let unknown_json = json!({
        "name": "Charlie",
        "kind": "guest"
    });
    let unknown_value = Value::from(unknown_json);

    let result = SchemaValidator::validate(&unknown_value, &schema);
    assert!(result.is_err(), "Unknown discriminator value should fail");
    if let Err(ValidationError::UnknownDiscriminatorValue {
        discriminator,
        value,
        allowed_values,
        ..
    }) = result
    {
        assert_eq!(discriminator.as_ref(), "kind");
        assert_eq!(value.as_ref(), "guest");
        assert_eq!(allowed_values.len(), 2);
        assert!(allowed_values.contains(&"user".into()));
        assert!(allowed_values.contains(&"admin".into()));
    } else {
        panic!("Expected UnknownDiscriminatorValue error");
    }

    // Test user object missing required field from variant
    let incomplete_json = json!({
        "name": "Dave",
        "kind": "user"
        // Missing required email field
    });
    let incomplete_value = Value::from(incomplete_json);

    let result = SchemaValidator::validate(&incomplete_value, &schema);
    assert!(result.is_err(), "User object missing email should fail");
    if let Err(ValidationError::DiscriminatedSubobjectValidationFailed {
        discriminator,
        value,
        error,
        ..
    }) = result
    {
        assert_eq!(discriminator.as_ref(), "kind");
        assert_eq!(value.as_ref(), "user");
        if let ValidationError::MissingRequiredProperty { property, .. } = error.as_ref() {
            assert_eq!(property.as_ref(), "email");
        } else {
            panic!("Expected MissingRequiredProperty error in discriminated subobject validation");
        }
    } else {
        panic!("Expected DiscriminatedSubobjectValidationFailed error");
    }

    // Test admin object with invalid permission type
    let invalid_admin_json = json!({
        "name": "Eve",
        "kind": "admin",
        "permissions": "not_an_array" // Wrong type - should be array
    });
    let invalid_admin_value = Value::from(invalid_admin_json);

    let result = SchemaValidator::validate(&invalid_admin_value, &schema);
    assert!(
        result.is_err(),
        "Admin object with invalid permissions type should fail"
    );

    if let Err(ValidationError::DiscriminatedSubobjectValidationFailed {
        discriminator,
        value,
        error,
        ..
    }) = result
    {
        assert_eq!(discriminator.as_ref(), "kind");
        assert_eq!(value.as_ref(), "admin");
        if let ValidationError::PropertyValidationFailed {
            property,
            error: nested_error,
            ..
        } = error.as_ref()
        {
            assert_eq!(property.as_ref(), "permissions");
            if let ValidationError::TypeMismatch {
                expected, actual, ..
            } = nested_error.as_ref()
            {
                assert_eq!(expected.as_ref(), "array");
                assert_eq!(actual.as_ref(), "string");
            } else {
                panic!("Expected TypeMismatch error for permissions field");
            }
        } else {
            panic!("Expected PropertyValidationFailed error in discriminated subobject validation");
        }
    } else {
        panic!("Expected DiscriminatedSubobjectValidationFailed error");
    }
}

#[test]
fn test_discriminated_subobject_complex_nested() {
    // Test deeply nested discriminated subobjects with multiple levels
    let schema_json = json!({
        "type": "object",
        "properties": {
            "type": {"type": "string"}
        },
        "required": ["type"],
        "allOf": [
            {
                "if": { "properties": { "type": { "const": "container" } } },
                "then": {
                    "properties": {
                        "image": { "type": "string", "pattern": "^[a-zA-Z0-9/_-]+:[a-zA-Z0-9._-]+$" },
                        "ports": {
                            "type": "array",
                            "items": {
                                "type": "object",
                                "properties": {
                                    "containerPort": { "type": "integer", "minimum": 1, "maximum": 65535 },
                                    "protocol": { "enum": ["TCP", "UDP"] }
                                },
                                "required": ["containerPort"]
                            }
                        },
                        "env": {
                            "type": "array",
                            "items": {
                                "type": "object",
                                "properties": {
                                    "name": { "type": "string", "pattern": "^[A-Z_][A-Z0-9_]*$" },
                                    "value": { "type": "string" }
                                },
                                "required": ["name", "value"]
                            }
                        }
                    },
                    "required": ["image"]
                }
            },
            {
                "if": { "properties": { "type": { "const": "volume" } } },
                "then": {
                    "properties": {
                        "mountPath": { "type": "string", "pattern": "^/[a-zA-Z0-9/_-]*$" },
                        "size": { "type": "string", "pattern": "^[0-9]+[GMK]i?$" },
                        "accessModes": {
                            "type": "array",
                            "items": { "enum": ["ReadWriteOnce", "ReadOnlyMany", "ReadWriteMany"] },
                            "minItems": 1
                        }
                    },
                    "required": ["mountPath", "size", "accessModes"]
                }
            }
        ]
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Test valid container with complex nested structure
    let valid_container = json!({
        "type": "container",
        "image": "nginx:1.21.6",
        "ports": [
            {
                "containerPort": 80,
                "protocol": "TCP"
            },
            {
                "containerPort": 443,
                "protocol": "TCP"
            }
        ],
        "env": [
            {
                "name": "NGINX_HOST",
                "value": "example.com"
            },
            {
                "name": "NGINX_PORT",
                "value": "80"
            }
        ]
    });

    let result = SchemaValidator::validate(&Value::from(valid_container), &schema);
    match &result {
        Ok(_) => {}
        Err(e) => panic!("Valid container should pass validation. Error: {:?}", e),
    }

    // Test invalid container with malformed image
    let invalid_container_image = json!({
        "type": "container",
        "image": "invalid image name!",
        "ports": []
    });

    let result = SchemaValidator::validate(&Value::from(invalid_container_image), &schema);
    assert!(result.is_err(), "Container with invalid image should fail");

    // Test invalid container with out-of-range port
    let invalid_container_port = json!({
        "type": "container",
        "image": "nginx:latest",
        "ports": [
            {
                "containerPort": 70000,
                "protocol": "TCP"
            }
        ]
    });

    let result = SchemaValidator::validate(&Value::from(invalid_container_port), &schema);
    assert!(result.is_err(), "Container with invalid port should fail");

    // Test valid volume
    let valid_volume = json!({
        "type": "volume",
        "mountPath": "/data/storage",
        "size": "10Gi",
        "accessModes": ["ReadWriteOnce"]
    });

    let result = SchemaValidator::validate(&Value::from(valid_volume), &schema);
    assert!(result.is_ok(), "Valid volume should pass validation");

    // Test invalid volume with malformed mount path
    let invalid_volume_path = json!({
        "type": "volume",
        "mountPath": "invalid-path",
        "size": "10Gi",
        "accessModes": ["ReadWriteOnce"]
    });

    let result = SchemaValidator::validate(&Value::from(invalid_volume_path), &schema);
    assert!(
        result.is_err(),
        "Volume with invalid mount path should fail"
    );
}

#[test]
fn test_discriminated_subobject_additional_properties() {
    // Test discriminated subobjects with additional properties handling
    let schema_json = json!({
        "type": "object",
        "properties": {
            "kind": {"type": "string"},
            "name": {"type": "string"}
        },
        "required": ["kind", "name"],
        "allOf": [
            {
                "if": { "properties": { "kind": { "const": "service" } } },
                "then": {
                    "properties": {
                        "port": { "type": "integer", "minimum": 1, "maximum": 65535 },
                        "protocol": { "enum": ["HTTP", "HTTPS", "TCP", "UDP"] }
                    },
                    "required": ["port"]
                }
            },
            {
                "if": { "properties": { "kind": { "const": "database" } } },
                "then": {
                    "properties": {
                        "connectionString": { "type": "string" },
                        "maxConnections": { "type": "integer", "minimum": 1 }
                    },
                    "required": ["connectionString"]
                }
            }
        ]
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Test service with required properties
    let service_basic = json!({
        "kind": "service",
        "name": "web-service",
        "port": 8080,
        "protocol": "HTTP"
    });

    let result = SchemaValidator::validate(&Value::from(service_basic), &schema);
    match &result {
        Ok(_) => {}
        Err(e) => panic!("Service with valid properties should pass. Error: {:?}", e),
    }

    // Test service with invalid port
    let service_invalid_port = json!({
        "kind": "service",
        "name": "web-service",
        "port": 70000  // Out of range
    });

    let result = SchemaValidator::validate(&Value::from(service_invalid_port), &schema);
    assert!(result.is_err(), "Service with invalid port should fail");

    // Test database with valid properties
    let database_basic = json!({
        "kind": "database",
        "name": "main-db",
        "connectionString": "postgresql://localhost:5432/mydb",
        "maxConnections": 100
    });

    let result = SchemaValidator::validate(&Value::from(database_basic), &schema);
    assert!(result.is_ok(), "Database with valid properties should pass");

    // Test unknown discriminator should fail
    let unknown_kind = json!({
        "kind": "unknown",
        "name": "test"
    });

    let result = SchemaValidator::validate(&Value::from(unknown_kind), &schema);
    assert!(result.is_err(), "Unknown discriminator should fail");
}

#[test]
fn test_discriminated_subobject_edge_cases() {
    // Test various edge cases and corner cases
    let schema_json = json!({
        "type": "object",
        "properties": {
            "discriminator": {"type": "string"},
            "id": {"type": "integer"}
        },
        "required": ["discriminator"],
        "allOf": [
            {
                "if": { "properties": { "discriminator": { "const": "empty" } } },
                "then": {
                    "properties": {}
                }
            },
            {
                "if": { "properties": { "discriminator": { "const": "minimal" } } },
                "then": {
                    "properties": {
                        "value": { "type": "null" }
                    },
                    "required": ["value"]
                }
            },
            {
                "if": { "properties": { "discriminator": { "const": "recursive" } } },
                "then": {
                    "properties": {
                        "child": {
                            "type": "object",
                            "properties": {
                                "discriminator": {"type": "string"}
                            },
                            "required": ["discriminator"]
                        }
                    },
                    "required": ["child"]
                }
            }
        ]
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Test empty variant - minimal properties
    let empty_valid = json!({
        "discriminator": "empty",
        "id": 123
    });

    let result = SchemaValidator::validate(&Value::from(empty_valid), &schema);
    assert!(
        result.is_ok(),
        "Empty variant with base properties should pass"
    );

    // Test minimal variant with null value
    let minimal_valid = json!({
        "discriminator": "minimal",
        "id": 456,
        "value": null
    });

    let result = SchemaValidator::validate(&Value::from(minimal_valid), &schema);
    assert!(
        result.is_ok(),
        "Minimal variant with null value should pass"
    );

    let minimal_invalid = json!({
        "discriminator": "minimal",
        "id": 456,
        "value": "not null"
    });

    let result = SchemaValidator::validate(&Value::from(minimal_invalid), &schema);
    assert!(
        result.is_err(),
        "Minimal variant with non-null value should fail"
    );

    // Test recursive/nested structure
    let recursive_valid = json!({
        "discriminator": "recursive",
        "id": 789,
        "child": {
            "discriminator": "nested"
        }
    });

    let result = SchemaValidator::validate(&Value::from(recursive_valid), &schema);
    match &result {
        Ok(_) => {}
        Err(e) => panic!(
            "Recursive variant with valid nested object should pass. Error: {:?}",
            e
        ),
    }

    let recursive_invalid = json!({
        "discriminator": "recursive",
        "id": 789,
        "child": {
            "missingDiscriminator": true
        }
    });

    let result = SchemaValidator::validate(&Value::from(recursive_invalid), &schema);
    assert!(
        result.is_err(),
        "Recursive variant with invalid nested object should fail"
    );
}

#[test]
fn test_discriminated_subobject_unicode_and_special_chars() {
    // Test discriminated subobjects with Unicode and special characters
    let schema_json = json!({
        "type": "object",
        "properties": {
            "类型": {"type": "string"},  // Chinese characters
            "🎯": {"type": "string"}      // Emoji
        },
        "required": ["类型"],
        "allOf": [
            {
                "if": { "properties": { "类型": { "const": "用户" } } },  // Chinese "user"
                "then": {
                    "properties": {
                        "姓名": { "type": "string" },  // Chinese "name"
                        "年龄": { "type": "integer", "minimum": 0 }  // Chinese "age"
                    },
                    "required": ["姓名"]
                }
            },
            {
                "if": { "properties": { "类型": { "const": "管理员" } } },  // Chinese "admin"
                "then": {
                    "properties": {
                        "权限": {  // Chinese "permissions"
                            "type": "array",
                            "items": { "type": "string" }
                        },
                        "级别": { "type": "integer" }  // Chinese "level"
                    },
                    "required": ["权限"]
                }
            }
        ]
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Test valid user with Chinese properties
    let valid_user = json!({
        "类型": "用户",
        "姓名": "张三",
        "年龄": 25,
        "🎯": "target"
    });

    let result = SchemaValidator::validate(&Value::from(valid_user), &schema);
    assert!(
        result.is_ok(),
        "Valid user with Unicode properties should pass"
    );

    // Test valid admin with Chinese properties
    let valid_admin = json!({
        "类型": "管理员",
        "权限": ["读取", "写入", "删除"],
        "级别": 5
    });

    let result = SchemaValidator::validate(&Value::from(valid_admin), &schema);
    assert!(
        result.is_ok(),
        "Valid admin with Unicode properties should pass"
    );

    // Test invalid discriminator value
    let invalid_discriminator = json!({
        "类型": "访客",  // Chinese "guest" - not in allowed values
        "姓名": "李四"
    });

    let result = SchemaValidator::validate(&Value::from(invalid_discriminator), &schema);
    assert!(result.is_err(), "Invalid Unicode discriminator should fail");
}

#[test]
fn test_discriminated_subobject_performance_stress() {
    // Test with many variants and deep nesting for performance
    let mut variants = Vec::new();

    // Create 50 variants to stress test performance
    for i in 0..50 {
        variants.push(json!({
            "if": { "properties": { "type": { "const": format!("variant_{}", i) } } },
            "then": {
                "properties": {
                    "data": {
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
                                                    "value": { "type": "integer" }
                                                },
                                                "required": ["value"]
                                            }
                                        },
                                        "required": ["level3"]
                                    }
                                },
                                "required": ["level2"]
                            }
                        },
                        "required": ["level1"]
                    }
                },
                "required": ["data"]
            }
        }));
    }

    let schema_json = json!({
        "type": "object",
        "properties": {
            "type": {"type": "string"}
        },
        "required": ["type"],
        "allOf": variants
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Test validation with various variants
    for i in [0, 25, 49] {
        // Test first, middle, and last variants
        let test_data = json!({
            "type": format!("variant_{}", i),
            "data": {
                "level1": {
                    "level2": {
                        "level3": {
                            "value": i * 10
                        }
                    }
                }
            }
        });

        let result = SchemaValidator::validate(&Value::from(test_data), &schema);
        assert!(result.is_ok(), "Variant {} should pass validation", i);
    }

    // Test invalid variant
    let invalid_data = json!({
        "type": "variant_100",  // Non-existent variant
        "data": {}
    });

    let result = SchemaValidator::validate(&Value::from(invalid_data), &schema);
    assert!(result.is_err(), "Non-existent variant should fail");

    // Test valid variant with invalid nested structure
    let invalid_nested = json!({
        "type": "variant_10",
        "data": {
            "level1": {
                "level2": {
                    "level3": {
                        "value": "not an integer"  // Should be integer
                    }
                }
            }
        }
    });

    let result = SchemaValidator::validate(&Value::from(invalid_nested), &schema);
    assert!(
        result.is_err(),
        "Valid variant with invalid nested data should fail"
    );
}

#[test]
fn test_discriminated_subobject_conflict_resolution() {
    // Test property conflicts between base and variant schemas
    let schema_json = json!({
        "type": "object",
        "properties": {
            "type": {"type": "string"},
            "name": {"type": "string", "maxLength": 50},  // Base constraint
            "description": {"type": "string"}
        },
        "required": ["type", "name"],
        "allOf": [
            {
                "if": { "properties": { "type": { "const": "product" } } },
                "then": {
                    "properties": {
                        "name": {"type": "string", "maxLength": 20},  // Stricter constraint in variant
                        "price": {"type": "number", "minimum": 0},
                        "category": {"type": "string"}
                    },
                    "required": ["price"]
                }
            },
            {
                "if": { "properties": { "type": { "const": "person" } } },
                "then": {
                    "properties": {
                        "name": {"type": "string", "pattern": "^[A-Za-z ]+$"},  // Different constraint in variant
                        "age": {"type": "integer", "minimum": 0, "maximum": 150},
                        "email": {"type": "string"}
                    },
                    "required": ["age"]
                }
            }
        ]
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();

    // Test product with name that satisfies variant constraint (stricter)
    let valid_product = json!({
        "type": "product",
        "name": "Short Name",  // ≤20 chars, satisfies variant constraint
        "description": "A great product",
        "price": 29.99,
        "category": "electronics"
    });

    let result = SchemaValidator::validate(&Value::from(valid_product), &schema);
    assert!(result.is_ok(), "Product with short name should pass");

    // Test product with name that violates variant constraint but satisfies base
    let invalid_product_name = json!({
        "type": "product",
        "name": "This is a very long product name that exceeds 20 characters",  // >20 chars
        "price": 29.99
    });

    let result = SchemaValidator::validate(&Value::from(invalid_product_name), &schema);
    assert!(
        result.is_err(),
        "Product with long name should fail variant validation"
    );

    // Test person with valid name pattern
    let valid_person = json!({
        "type": "person",
        "name": "John Doe",  // Matches pattern ^[A-Za-z ]+$
        "age": 30,
        "email": "john@example.com"
    });

    let result = SchemaValidator::validate(&Value::from(valid_person), &schema);
    assert!(result.is_ok(), "Person with valid name pattern should pass");

    // Test person with invalid name pattern
    let invalid_person_name = json!({
        "type": "person",
        "name": "John123",  // Contains numbers, violates pattern
        "age": 30
    });

    let result = SchemaValidator::validate(&Value::from(invalid_person_name), &schema);
    assert!(
        result.is_err(),
        "Person with invalid name pattern should fail"
    );
}
