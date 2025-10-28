// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use alloc::{borrow::ToOwned, collections::BTreeMap, string::String, vec::Vec};

use crate::lookup::Lookup;

use super::model::{TypeFact, TypeProvenance};

/// Central storage for the types inferred for each expression.
#[derive(Clone, Default, Debug)]
pub struct LookupContext {
    expr_types: Lookup<TypeFact>,
    expr_rule_references: Lookup<Vec<String>>,
    /// Current rule being analyzed (for dependency tracking)
    current_rule: Option<String>,
    /// Set of reachable rules (when entrypoint filtering is enabled)
    reachable_rules: BTreeMap<String, bool>,
    /// Dynamic reference patterns discovered during analysis
    dynamic_references: Vec<DynamicReferencePattern>,
}

/// Pattern for a dynamic data/rule reference
#[derive(Clone, Debug)]
pub struct DynamicReferencePattern {
    /// Static prefix components (e.g., ["data", "pkg"])
    pub static_prefix: Vec<String>,
    /// Full pattern with wildcards (e.g., "data.pkg.*.rule")
    pub pattern: String,
    /// Module and expression where this reference occurs
    pub location: (u32, u32),
}

impl LookupContext {
    pub fn new() -> Self {
        LookupContext {
            expr_types: Lookup::new(),
            expr_rule_references: Lookup::new(),
            current_rule: None,
            reachable_rules: BTreeMap::new(),
            dynamic_references: Vec::new(),
        }
    }

    pub fn ensure_expr_capacity(&mut self, module_idx: u32, max_expr_idx: u32) {
        // Ensure the module has at least an empty slot so cross-module lookups
        // cannot underflow, even when the module has zero expressions.
        if self.expr_types.module_len() <= module_idx as usize {
            self.expr_types.push_module(Vec::new());
        }
        if self.expr_rule_references.module_len() <= module_idx as usize {
            self.expr_rule_references.push_module(Vec::new());
        }

        self.expr_types.ensure_capacity(module_idx, max_expr_idx);
        self.expr_rule_references
            .ensure_capacity(module_idx, max_expr_idx);
    }

    pub fn record_expr(&mut self, module_idx: u32, expr_idx: u32, fact: TypeFact) {
        self.expr_types.set(module_idx, expr_idx, fact);
    }

    pub fn get_expr(&self, module_idx: u32, expr_idx: u32) -> Option<&TypeFact> {
        self.expr_types.get_checked(module_idx, expr_idx)
    }

    pub fn expr_types(&self) -> &Lookup<TypeFact> {
        &self.expr_types
    }

    pub fn expr_types_mut(&mut self) -> &mut Lookup<TypeFact> {
        &mut self.expr_types
    }

    pub fn record_rule_reference(&mut self, module_idx: u32, expr_idx: u32, rule_path: String) {
        self.expr_rule_references
            .ensure_capacity(module_idx, expr_idx);
        let slot = self.expr_rule_references.get_mut(module_idx, expr_idx);
        let entry = slot.get_or_insert_with(Vec::new);
        if !entry.contains(&rule_path) {
            entry.push(rule_path);
        }
    }

    pub fn get_rule_references(&self, module_idx: u32, expr_idx: u32) -> Option<&[String]> {
        self.expr_rule_references
            .get_checked(module_idx, expr_idx)
            .map(|vec| vec.as_slice())
    }

    /// Set the current rule being analyzed
    pub fn set_current_rule(&mut self, rule_path: Option<String>) {
        self.current_rule = rule_path;
    }

    pub fn current_rule(&self) -> Option<&str> {
        self.current_rule.as_deref()
    }

    /// Mark a rule as reachable
    pub fn mark_reachable(&mut self, rule_path: String) {
        self.reachable_rules.insert(rule_path, true);
    }

    /// Check if a rule is reachable
    pub fn is_reachable(&self, rule_path: &str) -> bool {
        self.reachable_rules
            .get(rule_path)
            .copied()
            .unwrap_or(false)
    }

    /// Get all reachable rules
    pub fn reachable_rules(&self) -> impl Iterator<Item = &String> {
        self.reachable_rules.keys()
    }

    /// Record a dynamic reference pattern
    pub fn record_dynamic_reference(
        &mut self,
        static_prefix: Vec<String>,
        pattern: String,
        module_idx: u32,
        expr_idx: u32,
    ) {
        self.dynamic_references.push(DynamicReferencePattern {
            static_prefix,
            pattern,
            location: (module_idx, expr_idx),
        });
    }

    /// Get all dynamic reference patterns
    pub fn dynamic_references(&self) -> &[DynamicReferencePattern] {
        &self.dynamic_references
    }
}

/// Scoped variable bindings collected while walking a query.
#[derive(Clone, Default, Debug)]
pub struct ScopedBindings {
    stack: Vec<BTreeMap<String, TypeFact>>,
}

impl ScopedBindings {
    pub fn new() -> Self {
        ScopedBindings { stack: Vec::new() }
    }

    pub fn push_scope(&mut self) {
        self.stack.push(BTreeMap::new());
    }

    pub fn pop_scope(&mut self) {
        self.stack.pop();
    }

    pub fn assign(&mut self, name: String, fact: TypeFact) {
        if let Some(scope) = self.stack.last_mut() {
            scope.insert(name, fact);
        }
    }

    pub fn ensure_root_scope(&mut self) {
        if self.stack.is_empty() {
            self.push_scope();
        }
    }

    pub fn lookup(&self, name: &str) -> Option<&TypeFact> {
        for scope in self.stack.iter().rev() {
            if let Some(fact) = scope.get(name) {
                return Some(fact);
            }
        }
        None
    }

    pub fn assign_if_absent(&mut self, name: String, fact: TypeFact) {
        self.ensure_root_scope();
        if self.lookup(&name).is_none() {
            self.assign(name, fact);
        }
    }

    pub fn assign_propagated(&mut self, name: &str, fact: &TypeFact) {
        self.ensure_root_scope();
        if let Some(scope) = self.stack.last_mut() {
            scope.insert(
                name.to_owned(),
                TypeFact {
                    descriptor: fact.descriptor.clone(),
                    constant: fact.constant.clone(),
                    provenance: TypeProvenance::Propagated,
                    origins: fact.origins.clone(),
                    specialization_hits: fact.specialization_hits.clone(),
                },
            );
        }
    }

    pub fn binding_names(&self) -> Vec<String> {
        let mut names = Vec::new();
        for scope in &self.stack {
            for key in scope.keys() {
                if !names.contains(key) {
                    names.push(key.clone());
                }
            }
        }
        names
    }
}
