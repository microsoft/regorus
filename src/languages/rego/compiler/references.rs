// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::expect_used,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

use super::{Compiler, CompilerError, Register, Result, WorklistEntry};
use crate::lexer::Span;
use crate::rvm::instructions::{
    ChainedIndexParams, LiteralOrRegister, VirtualDataDocumentLookupParams,
};
use crate::rvm::Instruction;
use crate::Value;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

use crate::ast::{Expr, ExprRef};

/// Component of a reference chain - either a literal field or a dynamic expression
#[derive(Debug, Clone)]
pub(super) enum AccessComponent {
    /// Static field access (e.g., .field_name)
    Field(String),
    /// Dynamic access (e.g., [expr])
    Expression(ExprRef),
}

/// Root of a reference chain - either a named variable or another arbitrary expression
#[derive(Debug, Clone)]
pub(super) enum ReferenceRoot {
    Variable(String),
    Expression(ExprRef),
}

/// Represents a chained reference like data.a.b[expr].c[expr]
#[derive(Debug, Clone)]
pub(super) struct ReferenceChain {
    /// The root of the chain (variable or arbitrary expression)
    pub(super) root: ReferenceRoot,
    /// Chain of field accesses - either literal field names or dynamic expressions
    pub(super) components: Vec<AccessComponent>,
}

impl ReferenceChain {
    /// Get the static prefix path (all literal components from the start)
    pub(super) fn get_static_prefix(&self) -> Option<Vec<&str>> {
        let ReferenceRoot::Variable(root) = &self.root else {
            return None;
        };

        let mut prefix = vec![root.as_str()];
        for component in &self.components {
            match component {
                AccessComponent::Field(field) => prefix.push(field.as_str()),
                AccessComponent::Expression(_) => break,
            }
        }
        Some(prefix)
    }
}

/// Parse a chained reference expression into a ReferenceChain
pub(super) fn parse_reference_chain(expr: &ExprRef) -> Result<ReferenceChain> {
    let mut components = Vec::new();
    let mut current_expr = expr;

    // Walk the chain backwards to collect components
    loop {
        match current_expr.as_ref() {
            Expr::Var { span, .. } => {
                // Found the root variable
                let root = ReferenceRoot::Variable(span.text().to_string());
                components.reverse(); // We built backwards, so reverse
                return Ok(ReferenceChain { root, components });
            }
            Expr::RefDot { refr, field, .. } => {
                let (span, _) = field;
                components.push(AccessComponent::Field(span.text().to_string()));
                current_expr = refr;
            }
            Expr::RefBrack { refr, index, .. } => {
                // Bracket access - check if it's a string literal or dynamic
                match index.as_ref() {
                    Expr::String { span, .. } => {
                        // String literal - treat as static field
                        components.push(AccessComponent::Field(span.text().to_string()));
                    }
                    _ => {
                        // Dynamic expression
                        components.push(AccessComponent::Expression(index.clone()));
                    }
                }
                current_expr = refr;
            }
            _ => {
                // Fallback root expression (e.g., array literal, function call)
                components.reverse();
                return Ok(ReferenceChain {
                    root: ReferenceRoot::Expression(current_expr.clone()),
                    components,
                });
            }
        }
    }
}

impl<'a> Compiler<'a> {
    /// Compile chained reference expressions (Var, RefDot, RefBrack chains)
    /// Uses ReferenceChain to analyze and optimize the access pattern
    pub(super) fn compile_chained_ref(&mut self, expr: &ExprRef, span: &Span) -> Result<Register> {
        // Parse the expression into a reference chain
        let chain = parse_reference_chain(expr)?;

        match chain.root.clone() {
            ReferenceRoot::Variable(name) => match name.as_str() {
                "input" => self.compile_input_chain(&chain, span),
                "data" => self.compile_data_chain(&chain, span),
                _ => self.compile_local_var_chain(&name, &chain, span),
            },
            ReferenceRoot::Expression(root_expr) => {
                let root_reg =
                    self.compile_rego_expr_with_span(&root_expr, root_expr.span(), false)?;
                self.compile_chain_access(root_reg, &chain.components, span)
            }
        }
    }

    /// Compile input variable access chain
    fn compile_input_chain(&mut self, chain: &ReferenceChain, span: &Span) -> Result<Register> {
        let input_reg = self.resolve_variable("input", span)?;

        if chain.components.is_empty() {
            // Just "input"
            return Ok(input_reg);
        }

        self.compile_chain_access(input_reg, &chain.components, span)
    }

    /// Compile data namespace access chain (may involve rules)
    fn compile_data_chain(&mut self, chain: &ReferenceChain, span: &Span) -> Result<Register> {
        if chain.components.is_empty() {
            // Just "data" - direct access to data root is not allowed
            return Err(CompilerError::DirectDataAccess.at(span));
        }

        // Build the static prefix path components for rule matching
        let static_prefix = chain
            .get_static_prefix()
            .expect("data references must have variable roots");

        // Try to find the longest matching rule prefix
        // Start from the full path and work backwards
        for i in (1..static_prefix.len()).rev() {
            // Start from 1 to skip just "data"
            let rule_candidate = static_prefix[0..=i].join(".");

            if let Ok(rule_index) = self.get_or_assign_rule_index(&rule_candidate) {
                // Found a rule match! Call the rule
                let rule_result_reg = self.alloc_register();
                self.emit_instruction(
                    Instruction::CallRule {
                        dest: rule_result_reg,
                        rule_index,
                    },
                    span,
                );

                // Handle remaining components after the matched rule
                let consumed_components = i;
                if consumed_components < chain.components.len() {
                    let remaining_components = &chain.components[consumed_components..];
                    return self.compile_chain_access(rule_result_reg, remaining_components, span);
                }

                return Ok(rule_result_reg);
            }
        }

        // Check if this path could be a prefix of any rules (for virtual document lookup)
        // Convert the full chain to a pattern that includes wildcards for dynamic components
        let path_pattern = self.create_path_pattern(&chain.components);
        let matching_rules: Vec<String> = self
            .policy
            .inner
            .rules
            .keys()
            .filter(|rule_path| self.matches_path_pattern(rule_path, &path_pattern))
            .cloned()
            .collect();

        if !matching_rules.is_empty() {
            // This path is a prefix of some rules - use DataVirtualDocumentLookup
            for rule_path in &matching_rules {
                if !self
                    .rule_worklist
                    .iter()
                    .any(|entry| entry.rule_path == *rule_path)
                {
                    // Assign a rule index for this rule before adding to worklist
                    self.get_or_assign_rule_index(rule_path)?;
                    let entry =
                        WorklistEntry::new(rule_path.clone(), self.current_call_stack.clone());
                    self.rule_worklist.push(entry);
                }
            }

            return self.compile_data_virtual_lookup(&chain.components, span);
        }

        // No rules involved - simple data access
        let data_reg = self.resolve_variable("data", span)?;
        self.compile_chain_access(data_reg, &chain.components, span)
    }

    /// Create a path pattern from access components, using '*' for dynamic components
    /// e.g., [Field("a"), Expression(...), Field("b")] becomes "data.a.*.b"
    fn create_path_pattern(&self, components: &[AccessComponent]) -> String {
        let mut pattern_parts = vec!["data"];

        for component in components {
            match component {
                AccessComponent::Field(field) => pattern_parts.push(field.as_str()),
                AccessComponent::Expression(_) => pattern_parts.push("*"),
            }
        }

        pattern_parts.join(".")
    }

    /// Check if a rule path matches the given pattern with wildcards
    /// e.g., "data.test.users.alice_profile" matches "data.test.users.*"
    fn matches_path_pattern(&self, rule_path: &str, pattern: &str) -> bool {
        // Use simple string matching implementation that handles wildcard patterns
        if pattern.contains('*') {
            self.simple_wildcard_match(rule_path, pattern)
        } else {
            // Simple prefix match for patterns without wildcards
            rule_path.starts_with(&format!("{}.", pattern)) || rule_path == pattern
        }
    }

    /// Simple wildcard matching without regex dependencies
    /// Checks if a rule path could be a prefix of the access pattern
    /// e.g., rule "data.test.users.alice_data" matches pattern "data.*.*.*.*.* because
    /// the rule could be accessed with the first 4 components of the pattern
    /// Ensures exact component matching - "fee" will NOT match "feed"
    fn simple_wildcard_match(&self, rule_path: &str, access_pattern: &str) -> bool {
        let rule_parts: Vec<&str> = rule_path.split('.').collect();
        let pattern_parts: Vec<&str> = access_pattern.split('.').collect();

        // Check how many components of the pattern the rule can match
        let match_length = rule_parts.len().min(pattern_parts.len());

        // Check if the rule matches the pattern up to the available components
        for i in 0..match_length {
            let rule_part = rule_parts[i];
            let pattern_part = pattern_parts[i];

            if pattern_part == "*" {
                // Wildcard in pattern matches any non-empty rule component exactly
                if rule_part.is_empty() {
                    return false;
                }
            } else if rule_part != pattern_part {
                return false;
            }
        }

        // Rule matches if either:
        // 1. It's at least as long as the pattern, OR
        // 2. It matches all available components and the remaining pattern parts are wildcards
        rule_parts.len() >= pattern_parts.len()
            || (match_length > 0
                && pattern_parts[match_length..]
                    .iter()
                    .all(|&part| part == "*"))
    }

    /// Compile local variable access chain
    fn compile_local_var_chain(
        &mut self,
        root: &str,
        chain: &ReferenceChain,
        span: &Span,
    ) -> Result<Register> {
        // Check if it's a local variable first (precedence over rules)
        if let Some(var_reg) = self.lookup_variable(root) {
            if chain.components.is_empty() {
                return Ok(var_reg);
            }
            return self.compile_chain_access(var_reg, &chain.components, span);
        }

        // Check if there's a rule in the current package that matches
        let current_pkg_prefix = format!("{}.{}", &self.current_package, root);

        // Build static path for rule matching
        let mut rule_path_parts = vec![current_pkg_prefix.as_str()];
        for component in &chain.components {
            match component {
                AccessComponent::Field(field) => rule_path_parts.push(field.as_str()),
                AccessComponent::Expression(_) => break, // Stop at first dynamic component
            }
        }

        // Try to find the longest matching rule prefix
        for i in (0..rule_path_parts.len()).rev() {
            let rule_candidate = rule_path_parts[0..=i].join(".");

            if let Ok(rule_index) = self.get_or_assign_rule_index(&rule_candidate) {
                let rule_result_reg = self.alloc_register();
                self.emit_instruction(
                    Instruction::CallRule {
                        dest: rule_result_reg,
                        rule_index,
                    },
                    span,
                );

                // Handle remaining components after the matched rule
                let consumed_components = i; // Number of components consumed by the rule (excluding root)
                if consumed_components < chain.components.len() {
                    let remaining_components = &chain.components[consumed_components..];
                    return self.compile_chain_access(rule_result_reg, remaining_components, span);
                }

                return Ok(rule_result_reg);
            }
        }

        // No rule found; fall back to module-level imports.
        let import_key = format!("{}.{}", &self.current_package, root);
        if let Some(import_expr) = self.policy.inner.imports.get(&import_key) {
            let import_reg =
                self.compile_rego_expr_with_span(import_expr, import_expr.span(), false)?;
            if chain.components.is_empty() {
                return Ok(import_reg);
            }
            return self.compile_chain_access(import_reg, &chain.components, span);
        }

        // No rule or import found - undefined variable
        Err(CompilerError::UndefinedVariable {
            name: root.to_string(),
        }
        .at(span))
    }

    /// Compile chain access using appropriate instructions based on chain length and complexity
    fn compile_chain_access(
        &mut self,
        root_reg: Register,
        components: &[AccessComponent],
        span: &Span,
    ) -> Result<Register> {
        if components.is_empty() {
            return Ok(root_reg);
        }

        if components.len() == 1 {
            // Single level access - use optimized instructions
            match &components[0] {
                AccessComponent::Field(field) => {
                    let dest_reg = self.alloc_register();
                    let literal_idx = self.add_literal(Value::String(field.clone().into()));
                    self.emit_instruction(
                        Instruction::IndexLiteral {
                            dest: dest_reg,
                            container: root_reg,
                            literal_idx,
                        },
                        span,
                    );
                    Ok(dest_reg)
                }
                AccessComponent::Expression(expr) => {
                    let dest_reg = self.alloc_register();
                    let key_reg = self.compile_rego_expr_with_span(expr, expr.span(), false)?;
                    self.emit_instruction(
                        Instruction::Index {
                            dest: dest_reg,
                            container: root_reg,
                            key: key_reg,
                        },
                        span,
                    );
                    Ok(dest_reg)
                }
            }
        } else {
            // Multi-level access - use ChainedIndex
            let dest_reg = self.alloc_register();
            let mut path_components = Vec::new();

            for component in components {
                match component {
                    AccessComponent::Field(field) => {
                        let literal_idx = self.add_literal(Value::String(field.clone().into()));
                        path_components.push(LiteralOrRegister::Literal(literal_idx));
                    }
                    AccessComponent::Expression(expr) => {
                        let reg = self.compile_rego_expr_with_span(expr, expr.span(), false)?;
                        path_components.push(LiteralOrRegister::Register(reg));
                    }
                }
            }

            let params = ChainedIndexParams {
                dest: dest_reg,
                root: root_reg,
                path_components,
            };

            let params_index = self.program.instruction_data.chained_index_params.len() as u16;
            self.program
                .instruction_data
                .chained_index_params
                .push(params);

            self.emit_instruction(Instruction::ChainedIndex { params_index }, span);

            Ok(dest_reg)
        }
    }

    /// Compile data virtual document lookup for rule-involved data access
    fn compile_data_virtual_lookup(
        &mut self,
        components: &[AccessComponent],
        span: &Span,
    ) -> Result<Register> {
        let dest_reg = self.alloc_register();
        let mut path_components = Vec::new();

        for component in components {
            match component {
                AccessComponent::Field(field) => {
                    let literal_idx = self.add_literal(Value::String(field.clone().into()));
                    path_components.push(LiteralOrRegister::Literal(literal_idx));
                }
                AccessComponent::Expression(expr) => {
                    let reg = self.compile_rego_expr_with_span(expr, expr.span(), false)?;
                    path_components.push(LiteralOrRegister::Register(reg));
                }
            }
        }

        let params = VirtualDataDocumentLookupParams {
            dest: dest_reg,
            path_components,
        };

        let params_index = self
            .program
            .instruction_data
            .virtual_data_document_lookup_params
            .len() as u16;
        self.program
            .instruction_data
            .virtual_data_document_lookup_params
            .push(params);

        self.emit_instruction(
            Instruction::VirtualDataDocumentLookup { params_index },
            span,
        );

        // Set flag indicating runtime recursion check is needed
        self.program.needs_runtime_recursion_check = true;

        Ok(dest_reg)
    }
}
