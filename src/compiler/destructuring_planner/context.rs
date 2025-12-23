// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::redundant_pub_crate)]

//! Context traits shared across planner submodules.

use alloc::collections::BTreeSet;
use alloc::string::String;

/// Scoping mode for variable binding decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopingMode {
    /// Respect existing bindings from parent scopes (normal scoping).
    RespectParent,
    /// Allow shadowing of parent scope bindings (local scoping).
    AllowShadowing,
}

/// Trait for determining variable binding status within a scope context.
pub trait VariableBindingContext {
    /// Check if a variable is unbound in this context.
    ///
    /// # Arguments
    /// * `var_name` - The name of the variable to check
    /// * `scoping` - Whether to respect parent scopes or allow shadowing
    fn is_var_unbound(&self, var_name: &str, scoping: ScopingMode) -> bool;

    /// Determine whether the current scope already bound this variable.
    ///
    /// This is used to detect same-scope rebinding conflicts when the planner
    /// encounters `:=` assignments, while still allowing shadowing in nested scopes.
    fn has_same_scope_binding(&self, var_name: &str) -> bool;
}

/// Context overlay that tracks newly bound variables on top of an existing context.
pub(crate) struct OverlayBindingContext<'a, T: VariableBindingContext> {
    pub(crate) base: &'a T,
    pub(crate) newly_bound: &'a BTreeSet<String>,
}

impl<'a, T: VariableBindingContext> VariableBindingContext for OverlayBindingContext<'a, T> {
    fn is_var_unbound(&self, var_name: &str, scoping: ScopingMode) -> bool {
        if self.newly_bound.contains(var_name) {
            return false;
        }

        self.base.is_var_unbound(var_name, scoping)
    }

    fn has_same_scope_binding(&self, var_name: &str) -> bool {
        if self.newly_bound.contains(var_name) {
            return true;
        }

        self.base.has_same_scope_binding(var_name)
    }
}
