// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::shadow_unrelated,
    clippy::assertions_on_result_states
)] // registry tests unwrap/panic to assert outcomes

use super::super::registry::*;
use crate::{schema::Schema, *};
use serde_json::json;

type String = Rc<str>;
type SchemaRegistryError = RegistryError;

#[test]
fn test_schema_registry_new() {
    let registry = SchemaRegistry::new("test");
    assert!(registry.is_empty());
    assert_eq!(registry.len(), 0);
}

#[test]
fn test_schema_registry_register_success() {
    let registry = SchemaRegistry::new("test");
    let schema = create_test_schema();

    let result = registry.register("test_schema", schema.clone());
    assert!(result.is_ok());
    assert_eq!(registry.len(), 1);
    assert!(registry.contains("test_schema"));
}

#[test]
fn test_schema_registry_register_duplicate() {
    let registry = SchemaRegistry::new("test");
    let schema = create_test_schema();

    // Register first time - should succeed
    let result1 = registry.register("test_schema", schema.clone());
    assert!(result1.is_ok());

    // Register again with same name - should fail
    let result2 = registry.register("test_schema", schema);
    assert!(result2.is_err());

    if let Err(SchemaRegistryError::AlreadyExists { name, .. }) = result2 {
        assert_eq!(name, "test_schema".into());
    } else {
        panic!("Expected AlreadyExists error");
    }
}

#[test]
fn test_schema_registry_get() {
    let registry = SchemaRegistry::new("test");
    let schema = create_test_schema();

    // Get non-existent schema
    assert!(registry.get("non_existent").is_none());

    // Register and get existing schema
    registry.register("test_schema", schema.clone()).unwrap();
    let retrieved = registry.get("test_schema");
    assert!(retrieved.is_some());

    // Verify it's the same schema (Rc comparison)
    let retrieved_schema = retrieved.unwrap();
    assert!(Rc::ptr_eq(&schema, &retrieved_schema));
}

#[test]
fn test_schema_registry_remove() {
    let registry = SchemaRegistry::new("test");
    let schema = create_test_schema();

    // Remove non-existent schema
    assert!(registry.remove("non_existent").is_none());

    // Register, then remove
    registry.register("test_schema", schema.clone()).unwrap();
    assert_eq!(registry.len(), 1);

    let removed = registry.remove("test_schema");
    assert!(removed.is_some());
    assert_eq!(registry.len(), 0);
    assert!(!registry.contains("test_schema"));

    // Verify it's the same schema
    let removed_schema = removed.unwrap();
    assert!(Rc::ptr_eq(&schema, &removed_schema));
}

#[test]
fn test_schema_registry_list_names() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");

    // Empty registry
    assert!(registry.list_names().is_empty());

    // Add multiple schemas
    let schema1 = create_test_schema();
    let schema2 = create_test_schema();

    registry.register("schema_a", schema1).unwrap();
    registry.register("schema_b", schema2).unwrap();

    let names = registry.list_names();
    assert_eq!(names.len(), 2);
    assert!(names.contains(&"schema_a".into()));
    assert!(names.contains(&"schema_b".into()));
}

#[test]
fn test_schema_registry_clear() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    // Add some schemas
    registry.register("schema1", schema.clone()).unwrap();
    registry.register("schema2", schema).unwrap();
    assert_eq!(registry.len(), 2);

    // Clear all
    registry.clear();
    assert!(registry.is_empty());
    assert_eq!(registry.len(), 0);
    assert!(registry.list_names().is_empty());
}

#[test]
fn test_error_display() {
    let error = SchemaRegistryError::AlreadyExists {
        name: "test_schema".into(),
        registry: "test".into(),
    };
    let error_message = format!("{error}");
    assert_eq!(
        error_message,
        "test registration failed: An item with the name 'test_schema' is already registered."
    );

    let invalid_error = SchemaRegistryError::InvalidName {
        name: " ".into(),
        registry: "test".into(),
    };
    let invalid_error_message = format!("{invalid_error}");
    assert_eq!(invalid_error_message, "test registration failed: The name ' ' is invalid (empty or whitespace-only names are not allowed).");
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_access() {
    use std::sync::Barrier;
    use std::thread;

    // Create a fresh registry for this test to avoid interference
    let test_registry = Rc::new(SchemaRegistry::new("TestSchemaRegistry"));

    let barrier = Rc::new(Barrier::new(4));
    let mut handles = vec![];

    // Spawn multiple threads trying to register schemas
    for i in 0..4 {
        let barrier = Rc::clone(&barrier);
        let registry = Rc::clone(&test_registry);
        let handle = thread::spawn(move || {
            let schema = create_test_schema();
            barrier.wait();

            // Each thread tries to register a schema with unique name
            let name = format!("schema_{i}");
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

    // Should have exactly 4 schemas registered
    assert_eq!(test_registry.len(), 4);
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_duplicate_registration() {
    use std::sync::Barrier;
    use std::thread;

    // Create a fresh registry for this test to avoid interference
    let test_registry = Rc::new(SchemaRegistry::new("TestSchemaRegistry"));

    let barrier = Rc::new(Barrier::new(3));
    let mut handles = vec![];

    // Spawn multiple threads trying to register the same schema name
    for _ in 0..3 {
        let barrier = Rc::clone(&barrier);
        let registry = Rc::clone(&test_registry);
        let handle = thread::spawn(move || {
            let schema = create_test_schema();
            barrier.wait();

            // All threads try to register with the same name
            registry.register("duplicate_name", schema)
        });
        handles.push(handle);
    }

    // Wait for all threads to complete
    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

    // Only one should succeed, others should fail
    let successes = results.iter().filter(|r| r.is_ok()).count();
    let failures = results.iter().filter(|r| r.is_err()).count();

    assert_eq!(successes, 1);
    assert_eq!(failures, 2);
    assert_eq!(test_registry.len(), 1);
}

// Helper function to create a test schema
fn create_test_schema() -> Rc<Schema> {
    let schema_json = json!({
        "type": "string",
        "description": "A test schema"
    });

    let schema = Schema::from_serde_json_value(schema_json).unwrap();
    Rc::new(schema)
}

// Corner case tests
#[test]
fn test_empty_schema_name() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    // Empty string as schema name should fail
    let result = registry.register("", schema);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        SchemaRegistryError::InvalidName { .. }
    ));
    assert!(!registry.contains(""));
    assert_eq!(registry.len(), 0);
    assert!(registry.is_empty());
}

#[test]
fn test_unicode_schema_names() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    // Test various Unicode characters
    let unicode_names = vec![
        "схема",     // Cyrillic
        "スキーマ",  // Japanese
        "模式",      // Chinese
        "🚀schema",  // Emoji
        "café-münü", // Accented characters
        "ñoño",      // Spanish characters
    ];

    for name in &unicode_names {
        let result = registry.register(*name, schema.clone());
        assert!(
            result.is_ok(),
            "Failed to register schema with name: {name}"
        );
        assert!(registry.contains(name));
    }

    assert_eq!(registry.len(), unicode_names.len());

    // Verify all names are listed
    let listed_names = registry.list_names();
    for name in &unicode_names {
        let name: String = (*name).into();
        assert!(listed_names.contains(&name));
    }
}

#[test]
fn test_very_long_schema_name() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    // Create a very long name (1000 characters)
    let long_name: String = "a".repeat(1000).into();

    let result = registry.register(long_name.clone(), schema);
    assert!(result.is_ok());
    assert!(registry.contains(&long_name));

    let retrieved = registry.get(&long_name);
    assert!(retrieved.is_some());
}

#[test]
fn test_special_character_schema_names() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    let special_names = vec![
        "schema-with-dashes",
        "schema_with_underscores",
        "schema.with.dots",
        "schema:with:colons",
        "schema/with/slashes",
        "schema with spaces",
        "schema\twith\ttabs",
        "schema\nwith\nnewlines",
        "UPPERCASE_SCHEMA",
        "MixedCaseSchema",
        "123numeric456",
        "!@#$%^&*()",
        "\"quoted\"",
        "'single-quoted'",
        "[bracketed]",
        "{curly}",
        "(parentheses)",
    ];

    for name in &special_names {
        let result = registry.register(*name, schema.clone());
        assert!(
            result.is_ok(),
            "Failed to register schema with name: {name}"
        );
        assert!(registry.contains(name));
    }

    assert_eq!(registry.len(), special_names.len());
}

#[test]
fn test_whitespace_only_names() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    let whitespace_names = vec![
        " ",        // Single space
        "\t",       // Tab
        "\n",       // Newline
        "\r",       // Carriage return
        "  ",       // Multiple spaces
        "\t\t",     // Multiple tabs
        " \t\n\r ", // Mixed whitespace
    ];

    for name in &whitespace_names {
        let result = registry.register(*name, schema.clone());
        assert!(
            result.is_err(),
            "Expected error for whitespace name: {name:?}"
        );
        assert!(matches!(
            result.unwrap_err(),
            SchemaRegistryError::InvalidName { .. }
        ));
        assert!(!registry.contains(name));
    }

    assert_eq!(registry.len(), 0);
}

#[test]
fn test_valid_names_with_whitespace() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    let valid_names = vec![
        "schema name",       // Space in the middle
        " schema",           // Leading space but not only whitespace
        "schema ",           // Trailing space but not only whitespace
        "my\tschema",        // Tab in the middle
        "multi word schema", // Multiple words
    ];

    for name in &valid_names {
        let result = registry.register(*name, schema.clone());
        assert!(result.is_ok(), "Expected success for valid name: {name:?}");
        assert!(registry.contains(name));
    }

    assert_eq!(registry.len(), valid_names.len());
}

#[test]
fn test_same_schema_different_names() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    // Register the same schema instance with different names
    let names = vec!["name1", "name2", "name3"];

    for name in &names {
        let result = registry.register(*name, schema.clone());
        assert!(result.is_ok());
    }

    assert_eq!(registry.len(), names.len());

    // All should point to the same schema instance
    for name in &names {
        let retrieved = registry.get(name).unwrap();
        assert!(Rc::ptr_eq(&schema, &retrieved));
    }
}

#[test]
fn test_register_after_remove_and_clear() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    // Register, remove, then register again with same name
    registry.register("test", schema.clone()).unwrap();
    assert!(registry.contains("test"));

    registry.remove("test");
    assert!(!registry.contains("test"));

    // Should be able to register again with same name
    let result = registry.register("test", schema.clone());
    assert!(result.is_ok());
    assert!(registry.contains("test"));

    // Clear and register again
    registry.clear();
    assert!(registry.is_empty());

    let result = registry.register("test", schema);
    assert!(result.is_ok());
    assert!(registry.contains("test"));
}

#[test]
fn test_case_sensitive_names() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    // Register schemas with different cases of the same name
    let case_variants = vec!["test", "Test", "TEST", "tEsT"];

    for name in &case_variants {
        let result = registry.register(*name, schema.clone());
        assert!(
            result.is_ok(),
            "Failed to register schema with name: {name}"
        );
    }

    assert_eq!(registry.len(), case_variants.len());

    // All should be treated as different schemas
    for name in &case_variants {
        assert!(registry.contains(name));
        let retrieved = registry.get(name);
        assert!(retrieved.is_some());
    }
}

#[test]
fn test_error_after_schema_removal() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema = create_test_schema();

    // Register schema
    registry.register("test", schema.clone()).unwrap();

    // Remove it
    registry.remove("test");

    // Try to register again - should succeed
    let result = registry.register("test", schema);
    assert!(result.is_ok());
}

#[test]
fn test_mixed_operations_sequence() {
    let registry = SchemaRegistry::new("TestSchemaRegistry");
    let schema1 = create_test_schema();
    let schema2 = create_test_schema();

    // Complex sequence of operations
    registry.register("a", schema1.clone()).unwrap();
    registry.register("b", schema2.clone()).unwrap();
    assert_eq!(registry.len(), 2);

    // Try duplicate - should fail
    assert!(registry.register("a", schema1.clone()).is_err());
    assert_eq!(registry.len(), 2);

    // Remove one
    registry.remove("a");
    assert_eq!(registry.len(), 1);

    // Register with removed name - should succeed
    registry.register("a", schema1).unwrap();
    assert_eq!(registry.len(), 2);

    // Clear and verify
    registry.clear();
    assert!(registry.is_empty());
    assert!(registry.list_names().is_empty());
}
