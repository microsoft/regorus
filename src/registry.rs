// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(missing_debug_implementations, clippy::pattern_type_mismatch)] // registry internals are not debug logged
#![allow(dead_code)]
use crate::*;
use core::fmt;
use dashmap::DashMap;

type String = Rc<str>;

#[cfg(test)]
mod tests {
    mod core;
    mod effect;
    mod resource;
    mod target;
}

/// Errors that can occur when interacting with a Registry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegistryError {
    AlreadyExists { name: String, registry: String },
    InvalidName { name: String, registry: String },
}

impl fmt::Display for RegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegistryError::AlreadyExists { name, registry } => {
                write!(
                    f,
                    "{} registration failed: An item with the name '{name}' is already registered.",
                    registry
                )
            }
            RegistryError::InvalidName { name, registry } => {
                write!(f, "{} registration failed: The name '{name}' is invalid (empty or whitespace-only names are not allowed).", registry)
            }
        }
    }
}

impl core::error::Error for RegistryError {}

/// Validates that a name is not empty or whitespace-only.
pub fn validate_name(name: &str, registry_name: &str) -> Result<(), RegistryError> {
    if name.is_empty() || name.trim().is_empty() {
        Err(RegistryError::InvalidName {
            name: String::from(name),
            registry: String::from(registry_name),
        })
    } else {
        Ok(())
    }
}

/// Generic thread-safe registry for items of type T using DashMap.
///
/// This template can be used to create registries for any type T.
/// It provides thread-safe storage and retrieval operations with customizable registry names.
#[derive(Clone)]
pub struct Registry<T> {
    inner: DashMap<String, Rc<T>>,
    name: String,
}

impl<T> Registry<T> {
    /// Create a new, empty registry with a given name.
    pub fn new(registry_name: impl Into<String>) -> Self {
        Self {
            inner: DashMap::new(),
            name: registry_name.into(),
        }
    }

    /// Get the name of this registry.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Register an item with a given name. Returns Err if name already exists.
    pub fn register(&self, name: impl Into<String>, item: Rc<T>) -> Result<(), RegistryError> {
        let name = name.into();

        // Validate the name first
        validate_name(&name, &self.name)?;

        use dashmap::mapref::entry::Entry;
        match self.inner.entry(name.clone()) {
            Entry::Occupied(e) => Err(RegistryError::AlreadyExists {
                name: e.key().clone(),
                registry: self.name.clone(),
            }),
            Entry::Vacant(e) => {
                e.insert(item);
                Ok(())
            }
        }
    }

    /// Retrieve an item by name, if it exists.
    pub fn get(&self, name: &str) -> Option<Rc<T>> {
        self.inner.get(name).map(|entry| Rc::clone(entry.value()))
    }

    /// Remove an item by name. Returns the removed item if it existed.
    pub fn remove(&self, name: &str) -> Option<Rc<T>> {
        self.inner.remove(name).map(|(_, v)| v)
    }

    /// List all registered item names.
    pub fn list_names(&self) -> Vec<String> {
        self.inner.iter().map(|entry| entry.key().clone()).collect()
    }

    /// Check if an item with the given name exists.
    pub fn contains(&self, name: &str) -> bool {
        self.inner.contains_key(name)
    }

    /// Get the number of registered items.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Check if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Clear all items from the registry.
    pub fn clear(&self) {
        self.inner.clear();
    }

    /// Get an iterator over all entries in the registry.
    /// Returns an iterator of (name, item) pairs.
    pub fn iter(&self) -> impl Iterator<Item = (String, Rc<T>)> + '_ {
        self.inner
            .iter()
            .map(|entry| (entry.key().clone(), Rc::clone(entry.value())))
    }

    /// Get all registered items as a vector.
    pub fn list_items(&self) -> Vec<Rc<T>> {
        self.inner
            .iter()
            .map(|entry| Rc::clone(entry.value()))
            .collect()
    }

    /// Try to register an item, but don't fail if the name already exists.
    /// Returns Ok(true) if the item was registered, Ok(false) if the name already exists.
    pub fn try_register(
        &self,
        name: impl Into<String>,
        item: Rc<T>,
    ) -> Result<bool, RegistryError> {
        match self.register(name, item) {
            Ok(()) => Ok(true),
            Err(RegistryError::AlreadyExists { .. }) => Ok(false),
            Err(e) => Err(e),
        }
    }
}

/// Type alias for Schema registry
pub type SchemaRegistry = Registry<crate::Schema>;

/// Type alias for Target registry
pub type TargetRegistry = Registry<crate::target::Target>;

/// Global registry instances
pub mod instances {
    use super::*;

    lazy_static::lazy_static! {
        /// Global singleton instance of resource schemas registry.
        pub static ref RESOURCE_SCHEMA_REGISTRY: Registry<crate::Schema> = Registry::new("RESOURCE_SCHEMA_REGISTRY");
    }

    lazy_static::lazy_static! {
        /// Global singleton instance of effect schemas registry.
        pub static ref EFFECT_SCHEMA_REGISTRY: Registry<crate::Schema> = Registry::new("EFFECT_SCHEMA_REGISTRY");
    }

    lazy_static::lazy_static! {
        /// Global singleton instance of targets registry.
        pub static ref TARGET_REGISTRY: Registry<crate::target::Target> = Registry::new("TARGET_REGISTRY");
    }
}

/// Macro to generate helper functions for registry operations.
///
/// This macro generates helper functions that wrap the registry operations.
/// It reduces code duplication and makes it easier to maintain registry interfaces.
///
/// # Arguments
/// * `$registry_var` - The static registry variable to wrap
/// * `$item_type` - The type of items stored in the registry (e.g., `crate::Schema`)
/// * `$item_description` - Human-readable description of the item type (e.g., "resource schema")
/// * `$item_description_plural` - Plural form of the item description (e.g., "resource schemas")
macro_rules! generate_registry_helpers {
    ($registry_var:ident, $item_type:ty, $item_description:literal, $item_description_plural:literal) => {
        #[doc = concat!("Register a ", $item_description, " with a given name.")]
        pub fn register(
            name: impl Into<String>,
            item: Rc<$item_type>,
        ) -> Result<(), RegistryError> {
            $registry_var.register(name, item)
        }

        #[doc = concat!("Retrieve a ", $item_description, " by name.")]
        pub fn get(name: &str) -> Option<Rc<$item_type>> {
            $registry_var.get(name)
        }

        #[doc = concat!("Remove a ", $item_description, " by name.")]
        pub fn remove(name: &str) -> Option<Rc<$item_type>> {
            $registry_var.remove(name)
        }

        #[doc = concat!("List all registered ", $item_description, " names.")]
        pub fn list_names() -> Vec<String> {
            $registry_var.list_names()
        }

        #[doc = concat!("Check if a ", $item_description, " with the given name exists.")]
        pub fn contains(name: &str) -> bool {
            $registry_var.contains(name)
        }

        #[doc = concat!("Get the number of registered ", $item_description_plural, ".")]
        pub fn len() -> usize {
            $registry_var.len()
        }

        #[doc = concat!("Check if the ", $item_description, " registry is empty.")]
        pub fn is_empty() -> bool {
            $registry_var.is_empty()
        }

        #[doc = concat!("Clear all ", $item_description_plural, " from the registry.")]
        pub fn clear() {
            $registry_var.clear();
        }
    };
}

/// Macro to generate a module with helper functions for registry operations.
///
/// This macro generates a complete module with helper functions that wrap the registry operations.
/// It reduces code duplication and makes it easier to maintain registry interfaces.
///
/// # Arguments
/// * `$mod_name` - The name of the module to generate
/// * `$registry_var` - The static registry variable to wrap
/// * `$item_type` - The type of items stored in the registry (e.g., `crate::Schema`)
/// * `$item_description` - Human-readable description of the item type (e.g., "resource schema")
/// * `$item_description_plural` - Plural form of the item description (e.g., "resource schemas")
macro_rules! generate_registry_module {
    ($mod_name:ident, $registry_var:ident, $item_type:ty, $item_description:literal, $item_description_plural:literal) => {
        #[doc = concat!("Helper functions for ", $item_description, " registry operations.")]
        pub mod $mod_name {
            use super::*;

            generate_registry_helpers!(
                $registry_var,
                $item_type,
                $item_description,
                $item_description_plural
            );
        }
    };
}

/// Helper functions for schema registry operations.
pub mod schemas {
    use super::*;
    use instances::*;

    // Generate helper modules for schema registries
    generate_registry_module!(
        resource,
        RESOURCE_SCHEMA_REGISTRY,
        crate::Schema,
        "resource schema",
        "resource schemas"
    );

    generate_registry_module!(
        effect,
        EFFECT_SCHEMA_REGISTRY,
        crate::Schema,
        "effect schema",
        "effect schemas"
    );
}

/// Helper functions for target registry operations.
pub mod targets {
    use super::*;
    use instances::*;

    /// Register a target using its name property.
    pub fn register(item: Rc<crate::target::Target>) -> Result<(), RegistryError> {
        let name = item.name.as_ref().to_string();
        TARGET_REGISTRY.register(name, item)
    }

    /// Retrieve a target by name.
    pub fn get(name: &str) -> Option<Rc<crate::target::Target>> {
        TARGET_REGISTRY.get(name)
    }

    /// Remove a target by name.
    pub fn remove(name: &str) -> Option<Rc<crate::target::Target>> {
        TARGET_REGISTRY.remove(name)
    }

    /// List all registered target names.
    pub fn list_names() -> Vec<String> {
        TARGET_REGISTRY.list_names()
    }

    /// Check if a target with the given name exists.
    pub fn contains(name: &str) -> bool {
        TARGET_REGISTRY.contains(name)
    }

    /// Get the number of registered targets.
    pub fn len() -> usize {
        TARGET_REGISTRY.len()
    }

    /// Check if the target registry is empty.
    pub fn is_empty() -> bool {
        TARGET_REGISTRY.is_empty()
    }

    /// Clear all targets from the registry.
    pub fn clear() {
        TARGET_REGISTRY.clear();
    }
}
