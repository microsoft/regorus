// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(dead_code)]
use crate::{schema::Schema, *};
use dashmap::DashMap;

type String = Rc<str>;

/// Errors that can occur when interacting with the SchemaRegistry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchemaRegistryError {
    AlreadyExists(String),
    InvalidName(String),
}

impl fmt::Display for SchemaRegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SchemaRegistryError::AlreadyExists(name) => {
                write!(f, "Schema registration failed: A schema with the name '{name}' is already registered.")
            }
            SchemaRegistryError::InvalidName(name) => {
                write!(f, "Schema registration failed: The name '{name}' is invalid (empty or whitespace-only names are not allowed).")
            }
        }
    }
}

impl core::error::Error for SchemaRegistryError {}

/// Validates that a schema name is not empty or whitespace-only.
fn validate_name(name: &str) -> Result<(), SchemaRegistryError> {
    if name.is_empty() || name.trim().is_empty() {
        Err(SchemaRegistryError::InvalidName(String::from(name)))
    } else {
        Ok(())
    }
}

/// Thread-safe registry for Schemas using DashMap.
#[derive(Clone, Default)]
pub struct SchemaRegistry {
    inner: DashMap<String, Rc<Schema>>,
}

#[cfg(feature = "arc")]
lazy_static::lazy_static! {
    /// Global singleton instance of resource schemas registry.
    /// Only available when using Arc (thread-safe) reference counting.
    pub static ref RESOURCE_SCHEMA_REGISTRY: SchemaRegistry = SchemaRegistry::new();
}

#[cfg(feature = "arc")]
lazy_static::lazy_static! {
    /// Global singleton instance of effect schemas registry.
    /// Only available when using Arc (thread-safe) reference counting.
    pub static ref EFFECT_SCHEMA_REGISTRY: SchemaRegistry = SchemaRegistry::new();
}

impl SchemaRegistry {
    /// Create a new, empty registry.
    pub fn new() -> Self {
        Self {
            inner: DashMap::new(),
        }
    }

    /// Register a schema with a given name. Returns Err if name already exists.
    pub fn register(
        &self,
        name: impl Into<String>,
        schema: Rc<Schema>,
    ) -> Result<(), SchemaRegistryError> {
        let name = name.into();

        // Validate the name first
        validate_name(&name)?;

        use dashmap::mapref::entry::Entry;
        match self.inner.entry(name) {
            Entry::Occupied(e) => Err(SchemaRegistryError::AlreadyExists(e.key().clone())),
            Entry::Vacant(e) => {
                e.insert(schema);
                Ok(())
            }
        }
    }

    /// Retrieve a schema by name, if it exists.
    pub fn get(&self, name: &str) -> Option<Rc<Schema>> {
        self.inner.get(name).map(|entry| Rc::clone(entry.value()))
    }

    /// Remove a schema by name. Returns the removed schema if it existed.
    pub fn remove(&self, name: &str) -> Option<Rc<Schema>> {
        self.inner.remove(name).map(|(_, v)| v)
    }

    /// List all registered schema names.
    pub fn list_names(&self) -> Vec<String> {
        self.inner.iter().map(|entry| entry.key().clone()).collect()
    }

    /// Check if a schema with the given name exists.
    pub fn contains(&self, name: &str) -> bool {
        self.inner.contains_key(name)
    }

    /// Get the number of registered schemas.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Check if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Clear all schemas from the registry.
    pub fn clear(&self) {
        self.inner.clear();
    }
}

/// Helper functions for resource schema registry operations.
/// Only available when using Arc (thread-safe) reference counting.
#[cfg(feature = "arc")]
pub mod resource {
    use super::*;

    /// Register a resource schema with a given name.
    pub fn register(
        name: impl Into<String>,
        schema: Rc<Schema>,
    ) -> Result<(), SchemaRegistryError> {
        RESOURCE_SCHEMA_REGISTRY.register(name, schema)
    }

    /// Retrieve a resource schema by name.
    pub fn get(name: &str) -> Option<Rc<Schema>> {
        RESOURCE_SCHEMA_REGISTRY.get(name)
    }

    /// Remove a resource schema by name.
    pub fn remove(name: &str) -> Option<Rc<Schema>> {
        RESOURCE_SCHEMA_REGISTRY.remove(name)
    }

    /// List all registered resource schema names.
    pub fn list_names() -> Vec<String> {
        RESOURCE_SCHEMA_REGISTRY.list_names()
    }

    /// Check if a resource schema with the given name exists.
    pub fn contains(name: &str) -> bool {
        RESOURCE_SCHEMA_REGISTRY.contains(name)
    }

    /// Get the number of registered resource schemas.
    pub fn len() -> usize {
        RESOURCE_SCHEMA_REGISTRY.len()
    }

    /// Check if the resource schema registry is empty.
    pub fn is_empty() -> bool {
        RESOURCE_SCHEMA_REGISTRY.is_empty()
    }

    /// Clear all resource schemas from the registry.
    pub fn clear() {
        RESOURCE_SCHEMA_REGISTRY.clear();
    }
}

/// Helper functions for effect schema registry operations.
/// Only available when using Arc (thread-safe) reference counting.
#[cfg(feature = "arc")]
pub mod effect {
    use super::*;

    /// Register an effect schema with a given name.
    pub fn register(
        name: impl Into<String>,
        schema: Rc<Schema>,
    ) -> Result<(), SchemaRegistryError> {
        EFFECT_SCHEMA_REGISTRY.register(name, schema)
    }

    /// Retrieve an effect schema by name.
    pub fn get(name: &str) -> Option<Rc<Schema>> {
        EFFECT_SCHEMA_REGISTRY.get(name)
    }

    /// Remove an effect schema by name.
    pub fn remove(name: &str) -> Option<Rc<Schema>> {
        EFFECT_SCHEMA_REGISTRY.remove(name)
    }

    /// List all registered effect schema names.
    pub fn list_names() -> Vec<String> {
        EFFECT_SCHEMA_REGISTRY.list_names()
    }

    /// Check if an effect schema with the given name exists.
    pub fn contains(name: &str) -> bool {
        EFFECT_SCHEMA_REGISTRY.contains(name)
    }

    /// Get the number of registered effect schemas.
    pub fn len() -> usize {
        EFFECT_SCHEMA_REGISTRY.len()
    }

    /// Check if the effect schema registry is empty.
    pub fn is_empty() -> bool {
        EFFECT_SCHEMA_REGISTRY.is_empty()
    }

    /// Clear all effect schemas from the registry.
    pub fn clear() {
        EFFECT_SCHEMA_REGISTRY.clear();
    }
}
