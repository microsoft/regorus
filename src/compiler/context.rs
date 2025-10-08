// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

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
    pub context_type: ContextType,

    /// Variables that are bound in the current scope
    pub bound_vars: BTreeSet<String>,

    /// Variables that are explicitly marked as unbound (from `some` declarations)
    pub unbound_vars: BTreeSet<String>,

    /// Key expression from rule head or object comprehension (for output expression hoisting)
    pub key_expr: Option<ExprRef>,

    /// Value expression from rule assignment or comprehension term (for output expression hoisting)
    pub value_expr: Option<ExprRef>,
}

impl ScopeContext {
    /// Create a new context with Query type (default, no output expressions)
    pub fn new() -> Self {
        Self {
            context_type: ContextType::Query,
            bound_vars: BTreeSet::new(),
            unbound_vars: BTreeSet::new(),
            key_expr: None,
            value_expr: None,
        }
    }

    /// Create a new context with a specific context type
    #[allow(dead_code)]
    pub fn with_context_type(context_type: ContextType) -> Self {
        Self {
            context_type,
            bound_vars: BTreeSet::new(),
            unbound_vars: BTreeSet::new(),
            key_expr: None,
            value_expr: None,
        }
    }

    /// Create a new context with output expressions (for rules and comprehensions)
    #[allow(dead_code)]
    pub fn with_output_exprs(
        context_type: ContextType,
        key_expr: Option<ExprRef>,
        value_expr: Option<ExprRef>,
    ) -> Self {
        Self {
            context_type,
            bound_vars: BTreeSet::new(),
            unbound_vars: BTreeSet::new(),
            key_expr,
            value_expr,
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
            unbound_vars: self.unbound_vars.clone(),
            key_expr,
            value_expr,
        }
    }

    /// Add a variable to the bound set
    pub fn bind_variable(&mut self, var_name: &str) {
        if var_name != "_" {
            self.bound_vars.insert(var_name.to_string());
            self.unbound_vars.remove(var_name);
        }
    }

    /// Mark a variable as unbound
    pub fn add_unbound_variable(&mut self, var_name: &str) {
        if var_name != "_" && !self.bound_vars.contains(var_name) {
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
        if var_name == "_" || self.is_unbound(var_name) {
            true
        } else {
            // Treat variables that haven't been bound in this scope as potential loop iterators
            !self.bound_vars.contains(var_name)
        }
    }

    /// Create a child context inheriting parent bindings, output expressions, and context type
    pub fn child(&self) -> Self {
        Self {
            context_type: self.context_type.clone(),
            bound_vars: self.bound_vars.clone(),
            unbound_vars: self.unbound_vars.clone(),
            key_expr: self.key_expr.clone(),
            value_expr: self.value_expr.clone(),
        }
    }
}

impl Default for ScopeContext {
    fn default() -> Self {
        Self::new()
    }
}
