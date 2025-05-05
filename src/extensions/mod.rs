// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;
use anyhow::Result;

use std::any::Any;
use alloc::vec::Vec;
use alloc::boxed::Box;
use alloc::vec;

pub mod invoke;

/// Register any extension builtins in the builtins map
#[cfg(feature = "rego-extensions")]
pub fn register_builtins(m: &mut crate::builtins::BuiltinsMap<&'static str, crate::builtins::BuiltinFcn>) {
    invoke::register(m);
}

/// Trait for builtin extensions.
///
/// This trait is implemented by modules that extend Rego by adding
/// additional builtin functions. For example, see the `crypto` module.
pub trait BuiltinExtensionTrait: std::fmt::Debug + Send + Sync {
    /// Call the extension.
    fn call(&self, params: Vec<Value>) -> Result<Value>;

    /// Check if the extension is the same as another extension.
    fn as_any(&self) -> &dyn Any;
    
    /// Clone the extension (object safe alternative to Clone)
    fn clone_box(&self) -> Box<dyn BuiltinExtensionTrait>;
}

/// Trait to implement builtin extensions.
///
/// In addition to extensions, Regorus supports builtin extensions, which are
/// extensions that have a well-defined behavior and are registered in the
/// builtins map. They act similar to regular builtins, but their implementation
/// can be provided by any struct that implements the BuiltinExtensionTrait.
pub struct BuiltinExtension {
    /// Name of the builtin extension
    pub name: &'static str,
    
    /// Number of arguments the builtin extension expects
    pub nargs: u8,
    
    /// Default implementation factory - should return a Box<dyn BuiltinExtensionTrait> that will handle calls
    pub default_factory: Option<fn() -> Box<dyn BuiltinExtensionTrait>>,

    /// Whether the extension is thread-safe (stateless)
    /// If false (default), the extension will be wrapped with a mutex to ensure thread safety
    /// If true, the extension is considered stateless and will be used without mutex protection
    pub thread_safe: bool,
}

// Implement the Clone trait for BuiltinExtension
impl Clone for BuiltinExtension {
    fn clone(&self) -> Self {
        BuiltinExtension {
            name: self.name,
            nargs: self.nargs,
            default_factory: self.default_factory,
            thread_safe: self.thread_safe,
        }
    }
}

// Define the list of available builtin extensions
lazy_static::lazy_static! {
    pub static ref BUILTIN_EXTENSIONS: Vec<BuiltinExtension> = vec![
        BuiltinExtension {
            name: "invoke",
            nargs: 2,
            default_factory: Some(invoke::create_invoke_extension),
            thread_safe: false,
        },
        // Additional builtin extensions can be added here
    ];
}

impl std::fmt::Debug for BuiltinExtension {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BuiltinExtension")
            .field("name", &self.name)
            .field("nargs", &self.nargs)
            .field("has_default", &self.default_factory.is_some())
            .field("thread_safe", &self.thread_safe)
            .finish()
    }
}

/// Implement BuiltinExtensionTrait for any function that takes parameters and returns a Result<Value>
impl<F> BuiltinExtensionTrait for F
where
    F: Fn(Vec<Value>) -> Result<Value> + std::fmt::Debug + Send + Sync + Clone + 'static,
{
    fn call(&self, params: Vec<Value>) -> Result<Value> {
        self(params)
    }

    fn as_any(&self) -> &dyn Any {
        self as &dyn Any
    }
    
    fn clone_box(&self) -> Box<dyn BuiltinExtensionTrait> {
        Box::new(self.clone())
    }
}