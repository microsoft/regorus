// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::unused_trait_names)]

//! Compilation context types shared across compiler components.
//!
//! This module defines context structures used for tracking scope-level information
//! during compilation and analysis phases. These types are designed to be compatible
//! with both the interpreter's loop hoisting and the RVM compiler.

use crate::ast::ExprRef;
use alloc::collections::BTreeSet;
use alloc::string::{String, ToString};

/// Type of compilation context for tracking different scenarios
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContextType {
    /// Rule context (Complete, PartialSet, PartialObject, or Function)
    Rule,
    /// Comprehension context (Array, Set, or Object)
    Comprehension,
    /// Every quantifier context
    Every,
    /// Query/statement context (no output expressions)
    Query,
}

/// Context for tracking variable bindings and output expressions within a scope.
/// Used during loop hoisting and compilation to determine what needs to be hoisted
/// and what's already bound.
///
/// This design is compatible with RVM's CompilationContext for potential future unification.
#[derive(Debug, Clone)]
pub struct ScopeContext {
    /// Type of context (Rule, Comprehension, Every, Query)
    #[allow(dead_code)]
    pub context_type: ContextType,

    /// Variables that are bound in the current scope
    pub bound_vars: BTreeSet<String>,

    /// Variables that are introduced in this scope (used for conflict detection)
    pub current_scope_bound_vars: BTreeSet<String>,

    /// Variables that are explicitly marked as unbound (from `some` declarations)
    pub unbound_vars: BTreeSet<String>,

    /// Variables that are local to this scope and will become bound once assigned
    pub local_vars: BTreeSet<String>,

    /// Flag indicating whether scheduler scope information was available
    pub has_scheduler_scope: bool,

    /// Key expression from rule head or object comprehension (for output expression hoisting)
    #[allow(dead_code)]
    pub key_expr: Option<ExprRef>,

    /// Value expression from rule assignment or comprehension term (for output expression hoisting)
    #[allow(dead_code)]
    pub value_expr: Option<ExprRef>,

    /// Shared set of module-level globals available in this scope
    pub module_globals: Option<crate::Rc<BTreeSet<String>>>,
}

impl ScopeContext {
    /// Create a new context with Query type (default, no output expressions)
    pub const fn new() -> Self {
        Self {
            context_type: ContextType::Query,
            bound_vars: BTreeSet::new(),
            current_scope_bound_vars: BTreeSet::new(),
            unbound_vars: BTreeSet::new(),
            local_vars: BTreeSet::new(),
            has_scheduler_scope: false,
            key_expr: None,
            value_expr: None,
            module_globals: None,
        }
    }

    /// Create a new context with a specific context type
    #[allow(dead_code)]
    pub const fn with_context_type(context_type: ContextType) -> Self {
        Self {
            context_type,
            bound_vars: BTreeSet::new(),
            current_scope_bound_vars: BTreeSet::new(),
            unbound_vars: BTreeSet::new(),
            local_vars: BTreeSet::new(),
            has_scheduler_scope: false,
            key_expr: None,
            value_expr: None,
            module_globals: None,
        }
    }

    /// Create a new context with output expressions (for rules and comprehensions)
    #[allow(dead_code)]
    pub const fn with_output_exprs(
        context_type: ContextType,
        key_expr: Option<ExprRef>,
        value_expr: Option<ExprRef>,
    ) -> Self {
        Self {
            context_type,
            bound_vars: BTreeSet::new(),
            current_scope_bound_vars: BTreeSet::new(),
            unbound_vars: BTreeSet::new(),
            local_vars: BTreeSet::new(),
            has_scheduler_scope: false,
            key_expr,
            value_expr,
            module_globals: None,
        }
    }

    /// Create a child context that inherits bindings but overrides context type and output expressions
    pub fn child_with_output_exprs(
        &self,
        context_type: ContextType,
        key_expr: Option<ExprRef>,
        value_expr: Option<ExprRef>,
    ) -> Self {
        Self {
            context_type,
            bound_vars: self.bound_vars.clone(),
            current_scope_bound_vars: BTreeSet::new(),
            unbound_vars: self.unbound_vars.clone(),
            local_vars: self.local_vars.clone(),
            has_scheduler_scope: self.has_scheduler_scope,
            key_expr,
            value_expr,
            module_globals: self.module_globals.clone(),
        }
    }

    /// Add a variable to the bound set
    pub fn bind_variable(&mut self, var_name: &str) {
        if var_name != "_" {
            self.bound_vars.insert(var_name.to_string());
            self.current_scope_bound_vars.insert(var_name.to_string());
            self.unbound_vars.remove(var_name);
            self.local_vars.remove(var_name);
        }
    }

    /// Mark a variable as unbound
    pub fn add_unbound_variable(&mut self, var_name: &str) {
        if var_name != "_" {
            self.bound_vars.remove(var_name);
            self.current_scope_bound_vars.remove(var_name);
            self.local_vars.remove(var_name);
            self.unbound_vars.insert(var_name.to_string());
        }
    }

    /// Check if a variable is known to be unbound
    pub fn is_unbound(&self, var_name: &str) -> bool {
        self.unbound_vars.contains(var_name)
    }

    /// Check if we can determine that a variable should be treated as a loop iterator
    /// (either it's unbound or explicitly marked as such)
    pub fn should_hoist_as_loop(&self, var_name: &str) -> bool {
        if var_name == "_" {
            return true;
        }

        if self
            .module_globals
            .as_ref()
            .is_some_and(|globals| globals.contains(var_name))
        {
            return false;
        }

        if self.is_unbound(var_name) {
            return true;
        }

        if self.has_scheduler_scope {
            return self.local_vars.contains(var_name);
        }

        !self.bound_vars.contains(var_name)
    }
}

impl Default for ScopeContext {
    fn default() -> Self {
        Self::new()
    }
}
