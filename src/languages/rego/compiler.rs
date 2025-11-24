// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::{
    ArrayCreateParams, ChainedIndexParams, ComprehensionBeginParams, ComprehensionMode,
    LiteralOrRegister, LoopMode, LoopStartParams, ObjectCreateParams, SetCreateParams,
    VirtualDataDocumentLookupParams,
};
use crate::rvm::program::Program;
use crate::rvm::Instruction;

mod destructuring;
use crate::ast::{Expr, ExprRef, Rule, RuleHead};
use crate::builtins;
use crate::compiler::destructuring_planner::plans::BindingPlan;
use crate::compiler::hoist::{HoistedLoop, LoopType};
use crate::interpreter::Interpreter;
use crate::lexer::Span;
use crate::rvm::program::RuleType;
use crate::rvm::program::SpanInfo;
use crate::utils::get_path_string;
use crate::Map;
use crate::{CompiledPolicy, Value};
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::{String, ToString};
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use indexmap::IndexMap;

pub type Register = u8;

/// Component of a reference chain - either a literal field or a dynamic expression
#[derive(Debug, Clone)]
enum AccessComponent {
    /// Static field access (e.g., .field_name)
    Field(String),
    /// Dynamic access (e.g., [expr])
    Expression(ExprRef),
}

/// Represents a chained reference like data.a.b[expr].c[expr]
#[derive(Debug, Clone)]
struct ReferenceChain {
    /// The root variable (e.g., "data", "input", "local_var")
    root: String,
    /// Chain of field accesses - either literal field names or dynamic expressions
    components: Vec<AccessComponent>,
}

impl ReferenceChain {
    /// Get the static prefix path (all literal components from the start)
    fn get_static_prefix(&self) -> Vec<&str> {
        let mut prefix = vec![self.root.as_str()];
        for component in &self.components {
            match component {
                AccessComponent::Field(field) => prefix.push(field.as_str()),
                AccessComponent::Expression(_) => break,
            }
        }
        prefix
    }
}

/// Parse a chained reference expression into a ReferenceChain
fn parse_reference_chain(expr: &ExprRef) -> Result<ReferenceChain> {
    let mut components = Vec::new();
    let mut current_expr = expr;

    // Walk the chain backwards to collect components
    loop {
        match current_expr.as_ref() {
            Expr::Var { span, .. } => {
                // Found the root variable
                let root = span.text().to_string();
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
                return Err(CompilerError::NotSimpleReferenceChain);
            }
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum CompilerError {
    #[error("Not a builtin function: {name}")]
    NotBuiltinFunction { name: String },

    #[error("Unknown builtin function: {name}")]
    UnknownBuiltinFunction { name: String },

    #[error("internal: missing context for yield")]
    MissingYieldContext,

    #[error(
        "Direct access to 'data' root is not allowed. Use a specific path like 'data.package.rule'"
    )]
    DirectDataAccess,

    #[error("Not a simple reference chain")]
    NotSimpleReferenceChain,

    #[error("Missing binding plan for {context}")]
    MissingBindingPlan { context: String },

    #[error("Unexpected binding plan variant for {context}: {found}")]
    UnexpectedBindingPlan { context: String, found: String },

    #[error("Invalid destructuring pattern in assignment")]
    InvalidDestructuringPattern,

    #[error("Unsupported expression type in chained reference")]
    UnsupportedChainedExpression,

    #[error("internal: no rule type found for '{rule_path}'")]
    RuleTypeNotFound { rule_path: String },

    #[error("unary - can only be used with numeric literals")]
    InvalidUnaryMinus,

    #[error("Unknown function: '{name}'")]
    UnknownFunction { name: String },

    #[error("Undefined variable: '{name}'")]
    UndefinedVariable { name: String },

    #[error("SomeIn should have been hoisted as a loop")]
    SomeInNotHoisted,

    #[error("Invalid function expression")]
    InvalidFunctionExpression,

    #[error("Invalid function expression with package")]
    InvalidFunctionExpressionWithPackage,

    #[error("Compilation error: {message}")]
    General { message: String },
}

impl From<anyhow::Error> for CompilerError {
    fn from(err: anyhow::Error) -> Self {
        CompilerError::General {
            message: alloc::format!("{}", err),
        }
    }
}

pub type Result<T> = core::result::Result<T, CompilerError>;

#[derive(Debug, Clone, Default)]
struct Scope {
    bound_vars: BTreeMap<String, Register>,
    unbound_vars: BTreeSet<String>,
}

#[derive(Debug, Clone)]
pub enum ComprehensionType {
    Array,
    Object,
    Set,
}

#[derive(Debug, Clone)]
pub enum ContextType {
    Comprehension(ComprehensionType),
    Rule(RuleType),
    Every,
}

/// Compilation context for handling different types of rule bodies and comprehensions
#[derive(Debug, Clone)]
pub struct CompilationContext {
    context_type: ContextType,
    dest_register: Register,
    key_expr: Option<ExprRef>,
    value_expr: Option<ExprRef>,
    span: Span,
    key_value_loops_hoisted: bool,
}

/// Entry in the rule compilation worklist that tracks both rule path and full call stack for recursion detection
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WorklistEntry {
    /// Rule path to be compiled (e.g., "data.package.rule")
    pub rule_path: String,
    /// Call stack of rule indices leading to this rule (empty for entry point)
    pub call_stack: Vec<u16>,
}

impl WorklistEntry {
    pub fn new(rule_path: String, call_stack: Vec<u16>) -> Self {
        Self {
            rule_path,
            call_stack,
        }
    }

    pub fn entry_point(rule_path: String) -> Self {
        Self {
            rule_path,
            call_stack: Vec::new(),
        }
    }

    /// Create a new entry by extending the call stack with the caller's rule index
    pub fn with_caller(
        rule_path: String,
        current_call_stack: &[u16],
        caller_rule_index: u16,
    ) -> Self {
        let mut new_call_stack = current_call_stack.to_vec();
        new_call_stack.push(caller_rule_index);
        Self {
            rule_path,
            call_stack: new_call_stack,
        }
    }

    /// Check if this entry would create a recursive call
    pub fn would_create_recursion(&self, target_rule_index: u16) -> bool {
        self.call_stack.contains(&target_rule_index)
    }
}

pub struct Compiler<'a> {
    program: Program, // Program being built with instructions and parameter data
    spans: Vec<SpanInfo>,
    register_counter: Register,
    scopes: Vec<Scope>,         // Stack of variable scopes (like the interpreter)
    policy: &'a CompiledPolicy, // Reference to the compiled policy for rule lookup
    current_package: String,    // Current package path (e.g., "data.test")
    current_module_index: u32, // Current module index for scheduler lookup (set from rule's source file index)
    // Three-level hierarchy compilation fields
    rule_index_map: BTreeMap<String, u16>, // Maps rule paths to their assigned rule indices
    rule_worklist: Vec<WorklistEntry>,     // Rules that need to be compiled with caller tracking
    rule_definitions: Vec<Vec<Vec<u32>>>, // rule_index -> Vec<definition> where definition is Vec<body_entry_point>
    rule_definition_function_params: Vec<Vec<Option<Vec<String>>>>, // rule_index -> Vec<definition> -> Some(param_names) for function defs, None for others
    rule_definition_destructuring_patterns: Vec<Vec<Option<u32>>>, // rule_index -> Vec<definition> -> Some(destructuring_block_entry) for defs with destructuring
    rule_types: Vec<RuleType>, // rule_index -> true if set rule, false if regular rule
    rule_function_param_count: Vec<Option<usize>>, // rule_index -> Some(param_count) for function rules, None for others
    rule_result_registers: Vec<u8>, // rule_index -> result register allocated for this rule
    rule_num_registers: Vec<u8>,    // rule_index -> number of registers used by this rule
    // Context stack for output expression handling
    context_stack: Vec<CompilationContext>, // Stack of compilation contexts
    loop_expr_register_map: BTreeMap<ExprRef, Register>, // Map from loop expressions to their allocated registers
    // Source tracking for span information (0-based indices)
    source_to_index: BTreeMap<String, usize>, // Maps source file paths to source indices (0-based)
    // Builtin management
    builtin_index_map: BTreeMap<String, u16>, // Maps builtin names to their assigned indices
    // Input/Data loading optimization - track registers per rule definition
    current_input_register: Option<Register>, // Register holding input in current rule definition
    current_data_register: Option<Register>,  // Register holding data in current rule definition
    // Current rule being compiled for recursion detection
    current_rule_path: String, // Path of the rule currently being compiled
    // Call stack tracking for recursion detection
    current_call_stack: Vec<u16>, // Stack of rule indices currently being compiled
    // Entry points tracking
    entry_points: IndexMap<String, usize>, // Maps entry point names to their instruction indices
}

impl<'a> Compiler<'a> {
    pub fn with_policy(policy: &'a CompiledPolicy) -> Self {
        let mut program = Program::new();
        program.rego_v0 = policy.is_rego_v0();
        Self {
            program,
            spans: Vec::new(),
            register_counter: 1,
            scopes: vec![Scope::default()],
            policy,
            current_package: "".to_string(), // Default package, will be set dynamically during compilation
            current_module_index: 0, // Will be set from rule's source file index during compilation
            rule_index_map: BTreeMap::new(),
            rule_worklist: Vec::new(),
            rule_definitions: Vec::new(),
            rule_definition_function_params: Vec::new(),
            rule_definition_destructuring_patterns: Vec::new(),
            rule_types: Vec::new(),
            rule_function_param_count: Vec::new(),
            rule_result_registers: Vec::new(),
            rule_num_registers: Vec::new(),
            context_stack: vec![], // Default context
            loop_expr_register_map: BTreeMap::new(),
            source_to_index: BTreeMap::new(),
            builtin_index_map: BTreeMap::new(),
            current_input_register: None,
            current_data_register: None,
            current_rule_path: String::new(),
            current_call_stack: Vec::new(),
            entry_points: IndexMap::new(),
        }
    }

    /// Check if a function path is a builtin function (similar to interpreter's is_builtin)
    fn is_builtin(&self, path: &str) -> bool {
        path == "print" || builtins::BUILTINS.contains_key(path)
    }

    /// Check if a function path is a user-defined function rule
    fn is_user_defined_function(&self, rule_path: &str) -> bool {
        self.policy.inner.rules.contains_key(rule_path)
    }

    /// Get builtin index for a builtin function
    fn get_builtin_index(&mut self, builtin_name: &str) -> Result<u16> {
        if !self.is_builtin(builtin_name) {
            return Err(CompilerError::NotBuiltinFunction {
                name: builtin_name.to_string(),
            });
        }

        // Check if we already have an index for this builtin
        if let Some(&index) = self.builtin_index_map.get(builtin_name) {
            return Ok(index);
        }

        // Get the builtin function info to determine number of arguments
        let num_args = if builtin_name == "print" {
            2 // Special case for print
        } else if let Some(builtin_fcn) = builtins::BUILTINS.get(builtin_name) {
            builtin_fcn.1 as u16 // Second element is the number of arguments
        } else {
            return Err(CompilerError::UnknownBuiltinFunction {
                name: builtin_name.to_string(),
            });
        };

        // Create builtin info and add it to the program
        let builtin_info = crate::rvm::program::BuiltinInfo {
            name: builtin_name.to_string(),
            num_args,
        };
        let index = self.program.add_builtin_info(builtin_info);

        // Store in our mapping
        self.builtin_index_map
            .insert(builtin_name.to_string(), index);

        Ok(index)
    }

    pub fn alloc_register(&mut self) -> Register {
        // Assert that we don't exceed 256 registers (u8::MAX + 1)
        assert!(
            self.register_counter < 255,
            "Register overflow: attempted to allocate register {}, but maximum is 255. \
             Consider using register windowing or spill handling.",
            self.register_counter
        );

        let reg = self.register_counter;
        self.register_counter += 1;

        reg
    }

    /// Add a literal value to the literal table, returning its index
    pub fn add_literal(&mut self, value: Value) -> u16 {
        // Check if literal already exists to avoid duplication
        // TODO: Optimize lookup
        for (idx, existing) in self.program.literals.iter().enumerate() {
            if existing == &value {
                return idx as u16;
            }
        }

        let idx = self.program.literals.len() as u16;
        self.program.literals.push(value);
        idx
    }

    /// Push a new variable scope (like the interpreter)
    pub fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    /// Pop the current variable scope (like the interpreter)
    pub fn pop_scope(&mut self) {
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }

    /// Reset input/data registers for a new rule definition
    /// This ensures input and data are loaded only once per rule definition
    pub fn reset_rule_definition_registers(&mut self) {
        self.current_input_register = None;
        self.current_data_register = None;
    }

    /// Push a new compilation context onto the context stack
    pub fn push_context(&mut self, context: CompilationContext) {
        self.context_stack.push(context);
    }

    /// Pop the current compilation context from the context stack
    pub fn pop_context(&mut self) -> Option<CompilationContext> {
        // Don't pop the last context (default RegularRule)
        if self.context_stack.len() > 1 {
            self.context_stack.pop()
        } else {
            None
        }
    }

    /// Emit the appropriate instruction for yielding a value in the current context
    pub fn emit_context_yield(&mut self) -> Result<()> {
        if let Some(context) = self.context_stack.last().cloned() {
            let dest_register = context.dest_register;
            let span = &context.span;
            let value_register = match context.value_expr {
                Some(expr) => self.compile_rego_expr(&expr)?,
                None => {
                    let value_reg = self.alloc_register();
                    self.emit_instruction(
                        Instruction::LoadBool {
                            dest: value_reg,
                            value: true,
                        },
                        span,
                    );
                    value_reg
                }
            };

            let key_register = context
                .key_expr
                .map(|key_expr| self.compile_rego_expr(&key_expr))
                .unwrap_or(Ok(value_register))?;

            match context.context_type {
                ContextType::Comprehension(ComprehensionType::Array) => {
                    self.emit_instruction(
                        Instruction::ComprehensionYield {
                            value_reg: value_register,
                            key_reg: None,
                        },
                        span,
                    );
                }
                ContextType::Comprehension(ComprehensionType::Set) => {
                    self.emit_instruction(
                        Instruction::ComprehensionYield {
                            value_reg: value_register,
                            key_reg: None,
                        },
                        span,
                    );
                }
                ContextType::Rule(RuleType::PartialSet) => {
                    self.emit_instruction(
                        Instruction::SetAdd {
                            set: dest_register,
                            value: value_register,
                        },
                        span,
                    );
                }
                ContextType::Comprehension(ComprehensionType::Object) => {
                    self.emit_instruction(
                        Instruction::ComprehensionYield {
                            value_reg: value_register,
                            key_reg: Some(key_register),
                        },
                        span,
                    );
                }
                ContextType::Rule(RuleType::PartialObject) => {
                    self.emit_instruction(
                        Instruction::ObjectSet {
                            obj: dest_register,
                            key: key_register,
                            value: value_register,
                        },
                        span,
                    );
                }
                ContextType::Rule(RuleType::Complete) => {
                    self.emit_instruction(
                        Instruction::Move {
                            dest: dest_register,
                            src: value_register,
                        },
                        span,
                    );
                }
                ContextType::Every => {
                    // Every quantifiers don't emit any yield instructions
                    // They are assertion-only contexts
                }
            }
            Ok(())
        } else {
            Err(CompilerError::MissingYieldContext)
        }
    }

    /// Get the current scope mutably
    fn current_scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().expect("No active scope")
    }

    /// Add a variable to the current scope (like interpreter's add_variable)
    pub fn add_variable(&mut self, var_name: &str, register: Register) {
        if var_name != "_" {
            // Don't store anonymous variables
            self.current_scope_mut()
                .bound_vars
                .insert(var_name.to_string(), register);
        }
    }

    /// Look up a variable in all scopes starting from innermost (like interpreter's lookup_local_var)
    pub fn lookup_local_var(&self, var_name: &str) -> Option<Register> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.bound_vars.get(var_name).copied())
    }

    pub fn add_unbound_variable(&mut self, var_name: &str) {
        self.current_scope_mut()
            .unbound_vars
            .insert(var_name.to_string());
    }

    pub fn is_unbound_var(&self, var_name: &str) -> bool {
        self.lookup_local_var(var_name).is_none()
            && self
                .scopes
                .iter()
                .rev()
                .any(|scope| scope.unbound_vars.contains(var_name))
    }

    pub fn bind_unbound_variable(&mut self, var_name: &str) {
        self.current_scope_mut().unbound_vars.remove(var_name);
    }

    /// Compile chained reference expressions (Var, RefDot, RefBrack chains)
    /// Uses ReferenceChain to analyze and optimize the access pattern
    fn compile_chained_ref(&mut self, expr: &ExprRef, span: &Span) -> Result<Register> {
        // Parse the expression into a reference chain
        let chain = parse_reference_chain(expr)?;

        match chain.root.as_str() {
            "input" => self.compile_input_chain(&chain, span),
            "data" => self.compile_data_chain(&chain, span),
            _ => self.compile_local_var_chain(&chain, span),
        }
    }

    fn get_statement_loops(&self, stmt: &crate::ast::LiteralStmt) -> Result<Vec<HoistedLoop>> {
        self.policy
            .inner
            .loop_hoisting_table
            .get_statement_loops(self.current_module_index, stmt.sidx)
            .cloned()
            .ok_or_else(|| CompilerError::General {
                message: format!(
                    "missing loop hoisting data for statement at {}:{}",
                    stmt.span.line, stmt.span.col
                ),
            })
    }

    fn get_expr_loops(&self, expr: &ExprRef) -> Vec<HoistedLoop> {
        let module_idx = self.current_module_index;
        let expr_idx = expr.as_ref().eidx();
        self.policy
            .inner
            .loop_hoisting_table
            .get_expr_loops(module_idx, expr_idx)
            .cloned()
            .unwrap_or_default()
    }

    fn get_binding_plan_for_expr(&self, expr: &ExprRef) -> Option<BindingPlan> {
        let module_idx = self.current_module_index;
        let expr_idx = expr.as_ref().eidx();
        self.policy
            .inner
            .loop_hoisting_table
            .get_expr_binding_plan(module_idx, expr_idx)
            .cloned()
    }

    fn expect_binding_plan_for_expr(&self, expr: &ExprRef, context: &str) -> Result<BindingPlan> {
        self.get_binding_plan_for_expr(expr)
            .ok_or_else(|| CompilerError::MissingBindingPlan {
                context: context.to_string(),
            })
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
            return Err(CompilerError::DirectDataAccess);
        }

        // Build the static prefix path components for rule matching
        let static_prefix = chain.get_static_prefix();

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
                // Wildcard matches this exact component - continue to next
            } else {
                // Literal part in pattern must match rule part exactly
                if rule_part != pattern_part {
                    return false;
                }
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
    fn compile_local_var_chain(&mut self, chain: &ReferenceChain, span: &Span) -> Result<Register> {
        // Check if it's a local variable first (precedence over rules)
        if let Some(var_reg) = self.lookup_variable(&chain.root) {
            if chain.components.is_empty() {
                return Ok(var_reg);
            }
            return self.compile_chain_access(var_reg, &chain.components, span);
        }

        // Check if there's a rule in the current package that matches
        let current_pkg_prefix = format!("{}.{}", &self.current_package, &chain.root);

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

        // No rule found - undefined variable
        Err(CompilerError::UndefinedVariable {
            name: chain.root.clone(),
        })
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

    /// Store a variable mapping (backward compatibility)
    /// Look up a variable, first in local scope, then as a rule reference
    fn resolve_variable(&mut self, var_name: &str, span: &Span) -> Result<Register> {
        // Handle special built-in variables first
        match var_name {
            "input" => {
                // Check if input is already loaded in current rule definition
                if let Some(register) = self.current_input_register {
                    return Ok(register);
                }

                // Load input for the first time in this rule definition
                let dest = self.alloc_register();
                self.emit_instruction(Instruction::LoadInput { dest }, span);
                self.current_input_register = Some(dest);
                return Ok(dest);
            }
            "data" => {
                // Check if data is already loaded in current rule definition
                if let Some(register) = self.current_data_register {
                    return Ok(register);
                }

                // Load data for the first time in this rule definition
                // TODO: Fully qualified rule paths.
                // TODO: data overrides rule in same path
                let dest = self.alloc_register();
                self.emit_instruction(Instruction::LoadData { dest }, span);
                self.current_data_register = Some(dest);
                return Ok(dest);
            }
            _ => {
                // Continue with normal variable resolution
            }
        }

        // First check local variables
        if let Some(var_reg) = self.lookup_variable(var_name) {
            return Ok(var_reg);
        }

        let rule_path = format!("{}.{}", &self.current_package, var_name);

        // Always emit CallRule for all rules.
        // TODO: Inline rules
        let rule_index = self.get_or_assign_rule_index(&rule_path)?;
        let dest = self.alloc_register();

        self.emit_instruction(Instruction::CallRule { dest, rule_index }, span);
        Ok(dest)
    }

    fn compute_rule_type(&self, rule_path: &str) -> Result<RuleType> {
        let Some(definitions) = self.policy.inner.rules.get(rule_path) else {
            return Err(CompilerError::General {
                message: format!("no definitions found for rule path '{}'", rule_path),
            });
        };

        let rule_types: BTreeSet<RuleType> = definitions
            .iter()
            .map(|def| {
                if let crate::ast::Rule::Spec { head, .. } = def.as_ref() {
                    let result = match head {
                        crate::ast::RuleHead::Set { .. } => RuleType::PartialSet,
                        crate::ast::RuleHead::Compr { refr, assign, .. } => match refr.as_ref() {
                            crate::ast::Expr::RefBrack { .. } if assign.is_some() => {
                                RuleType::PartialObject
                            }
                            crate::ast::Expr::RefBrack { .. } => RuleType::PartialSet,
                            _ => RuleType::Complete,
                        },
                        _ => RuleType::Complete,
                    };
                    result
                } else {
                    RuleType::Complete
                }
            })
            .collect();

        if rule_types.len() > 1 {
            return Err(CompilerError::General {
                message: alloc::format!(
                    "internal: rule '{}' has multiple types: {:?}",
                    rule_path,
                    rule_types
                ),
            });
        }

        rule_types
            .into_iter()
            .next()
            .ok_or_else(|| CompilerError::RuleTypeNotFound {
                rule_path: rule_path.to_string(),
            })
    }

    /// Get or assign a rule index for CallRule instructions
    fn get_or_assign_rule_index(&mut self, rule_path: &str) -> Result<u16> {
        if let Some(&index) = self.rule_index_map.get(rule_path) {
            Ok(index)
        } else {
            let rule_type = self.compute_rule_type(rule_path)?;

            // Start rule indices from 1 (0 is reserved for main entrypoint)
            // TODO: Revisit this
            let index = self.rule_index_map.len() as u16;

            self.rule_index_map.insert(rule_path.to_string(), index);
            let entry = WorklistEntry::new(rule_path.to_string(), self.current_call_stack.clone());
            self.rule_worklist.push(entry);

            // Initialize rule definitions structure
            // Ensure rule_definitions has enough capacity
            while self.rule_definitions.len() <= index as usize {
                self.rule_definitions.push(Vec::new());
            }

            // Ensure rule_types has enough capacity and record the rule type
            while self.rule_types.len() <= index as usize {
                self.rule_types.push(RuleType::Complete); // Default to non-set rule
            }
            self.rule_types[index as usize] = rule_type;

            // Ensure rule_definition_function_params has enough capacity
            while self.rule_definition_function_params.len() <= index as usize {
                self.rule_definition_function_params.push(Vec::new()); // Default to empty vec for definitions
            }

            // Ensure rule_definition_destructuring_patterns has enough capacity
            while self.rule_definition_destructuring_patterns.len() <= index as usize {
                self.rule_definition_destructuring_patterns.push(Vec::new()); // Default to empty vec for definitions
            }

            // Ensure rule_function_param_count has enough capacity
            while self.rule_function_param_count.len() <= index as usize {
                self.rule_function_param_count.push(None); // Default to None (not a function)
            }

            // Ensure rule_result_registers has enough capacity
            while self.rule_result_registers.len() <= index as usize {
                self.rule_result_registers.push(0); // Default to register 0
            }

            Ok(index)
        }
    }

    fn store_variable(&mut self, var_name: String, register: Register) {
        self.add_variable(&var_name, register);
    }

    /// Look up a variable register (backward compatibility)
    fn lookup_variable(&self, var_name: &str) -> Option<Register> {
        self.lookup_local_var(var_name)
    }

    /// Emit an instruction with span tracking
    pub fn emit_instruction(&mut self, instruction: Instruction, span: &Span) {
        self.program.instructions.push(instruction);

        // Get the source path and find its index (0-based, matching program source table)
        let source_path = span.source.get_path().to_string();
        let source_index = self.get_or_create_source_index(&source_path);

        self.spans
            .push(SpanInfo::from_lexer_span(span, source_index));
    }

    /// Get or create a source index for the given source path (0-based, matching program source table)
    fn get_or_create_source_index(&mut self, source_path: &str) -> usize {
        if let Some(&index) = self.source_to_index.get(source_path) {
            index
        } else {
            // The source index matches what will be in the program's source table (0-based)
            let index = self.source_to_index.len(); // This will be 0-based like program source table
            self.source_to_index.insert(source_path.to_string(), index);
            index
        }
    }

    /// Find which module index contains the given rule
    fn find_module_index_for_rule(&self, rule_ref: &crate::ast::NodeRef<Rule>) -> Result<u32> {
        let rule_ptr = rule_ref.as_ref() as *const Rule;

        // Search through all modules to find which one contains this rule
        for (module_idx, module) in self.policy.get_modules().iter().enumerate() {
            for policy_rule in &module.policy {
                let policy_rule_ptr = policy_rule.as_ref() as *const Rule;
                if policy_rule_ptr == rule_ptr {
                    return Ok(module_idx as u32);
                }
            }
        }

        // If we can't find the module, default to 0
        Ok(0)
    }

    /// Find the module package and index for a rule given its rule path
    fn find_module_package_and_index_for_rule(
        &self,
        rule_path: &str,
        rules: &Map<String, Vec<crate::ast::NodeRef<Rule>>>,
    ) -> Result<(String, u32)> {
        // Get the rule definitions for this rule path
        if let Some(rule_definitions) = rules.get(rule_path) {
            if let Some(first_rule_ref) = rule_definitions.first() {
                // Find which module contains this rule
                let rule_ptr = first_rule_ref.as_ref() as *const Rule;

                for (module_index, module) in self.policy.get_modules().iter().enumerate() {
                    for policy_rule in &module.policy {
                        let policy_rule_ptr = policy_rule.as_ref() as *const Rule;
                        if policy_rule_ptr == rule_ptr {
                            // Found the module, extract its package
                            let package_path =
                                crate::utils::get_path_string(&module.package.refr, Some("data"))
                                    .map_err(|e| CompilerError::General {
                                    message: format!(
                                        "Failed to get package path for module: {}",
                                        e
                                    ),
                                })?;
                            return Ok((package_path, module_index as u32));
                        }
                    }
                }
            }
        }

        // Fallback: extract package from rule path if we can't find the module
        let package = if let Some(last_dot) = rule_path.rfind('.') {
            rule_path[..last_dot].to_string()
        } else {
            "data".to_string()
        };
        // Default to module index 0 for fallback
        Ok((package, 0))
    }

    pub fn emit_return(&mut self, result_reg: Register) {
        // Add return instruction
        self.program
            .instructions
            .push(Instruction::Return { value: result_reg });
        self.spans.push(SpanInfo::new(0, 0, 0, 0)); // Default span for return instruction
    }

    pub fn emit_call_rule(&mut self, dest: Register, rule_index: u16) {
        // Add call rule instruction
        self.program
            .instructions
            .push(Instruction::CallRule { dest, rule_index });
        self.spans.push(SpanInfo::new(0, 0, 0, 0)); // Default span for call rule instruction
    }

    pub fn finish(mut self) -> Result<crate::rvm::program::Program> {
        // Update the program with final values
        self.program.main_entry_point = 0;

        // Calculate register window requirements
        self.program.max_rule_window_size =
            self.rule_num_registers.iter().cloned().max().unwrap_or(0) as usize;
        self.program.dispatch_window_size = self.register_counter as usize;

        // Set the rule definitions from the compiler
        let mut rule_infos_map = BTreeMap::new();

        // First, collect rule indices that need destructuring blocks
        let function_rule_indices: Vec<u16> = self
            .rule_index_map
            .values()
            .copied()
            .filter(|&rule_index| self.rule_function_param_count[rule_index as usize].is_some())
            .collect();

        // Extract destructuring blocks for all function rules
        let mut all_destructuring_blocks = BTreeMap::new();
        for rule_index in function_rule_indices {
            let destructuring_blocks = self.extract_destructuring_blocks(rule_index);
            all_destructuring_blocks.insert(rule_index, destructuring_blocks);
        }

        // Then, collect all rule info without default evaluation
        for (rule_path, &rule_index) in &self.rule_index_map {
            let definitions = self.rule_definitions[rule_index as usize].clone();
            let rule_type = self.rule_types[rule_index as usize].clone();
            let function_param_count = &self.rule_function_param_count[rule_index as usize];
            let result_register = self.rule_result_registers[rule_index as usize];
            let num_registers = self.rule_num_registers[rule_index as usize];

            // Get destructuring blocks if available
            let destructuring_blocks = all_destructuring_blocks
                .get(&rule_index)
                .cloned()
                .unwrap_or_else(|| vec![None; definitions.len()]);

            let mut rule_info = match function_param_count {
                Some(param_count) => {
                    // This is a function rule - use first definition's param names as template
                    let definition_params =
                        &self.rule_definition_function_params[rule_index as usize];
                    let param_names =
                        if let Some(Some(first_def_params)) = definition_params.first() {
                            first_def_params.clone()
                        } else {
                            // Fallback: generate generic parameter names
                            (0..*param_count).map(|i| format!("param_{}", i)).collect()
                        };

                    crate::rvm::program::RuleInfo::new_function(
                        rule_path.clone(),
                        rule_type,
                        crate::Rc::new(definitions),
                        param_names,
                        result_register,
                        num_registers,
                    )
                }
                None => {
                    // This is a regular rule
                    crate::rvm::program::RuleInfo::new(
                        rule_path.clone(),
                        rule_type,
                        crate::Rc::new(definitions),
                        result_register,
                        num_registers,
                    )
                }
            };

            // Set destructuring blocks if available
            rule_info.destructuring_blocks = destructuring_blocks;

            rule_infos_map.insert(rule_index as usize, rule_info);
        }

        // Now evaluate default rules for Complete rules and update their literal indices
        let rule_paths_to_evaluate: Vec<(String, usize)> = self
            .rule_index_map
            .iter()
            .filter_map(|(rule_path, &rule_index)| {
                let rule_type = &self.rule_types[rule_index as usize];
                if *rule_type == crate::rvm::program::RuleType::Complete {
                    Some((rule_path.clone(), rule_index as usize))
                } else {
                    None
                }
            })
            .collect();

        for (rule_path, rule_index) in rule_paths_to_evaluate {
            if let Some(default_literal_index) = self.evaluate_default_rule(&rule_path) {
                if let Some(rule_info) = rule_infos_map.get_mut(&rule_index) {
                    rule_info.set_default_literal_index(default_literal_index);
                }
            }
        }

        self.program.rule_infos = rule_infos_map.into_values().collect();

        // Extract source contents from the policy modules and add them to the program
        for module in self.policy.get_modules().iter() {
            let source = &module.package.refr.span().source;
            let source_path = source.get_path().to_string();
            let source_content = source.get_contents().to_string();
            self.program.add_source(source_path, source_content);
        }

        // Transfer spans to program (they already have correct source indices)
        self.program.instruction_spans = self.spans.into_iter().map(Some).collect();

        // Transfer entry points to program
        self.program.entry_points = self.entry_points;

        // Initialize resolved builtins if we have builtin info
        if !self.program.builtin_info_table.is_empty() {
            self.program.initialize_resolved_builtins()?;
        }

        Ok(self.program)
    }

    /// Compile a Rego expression to RVM instructions
    pub fn compile_rego_expr(&mut self, expr: &ExprRef) -> Result<Register> {
        self.compile_rego_expr_with_span(expr, expr.span(), false)
    }

    /// Compile a Rego expression to RVM instructions with span tracking
    pub fn compile_rego_expr_with_span(
        &mut self,
        expr: &ExprRef,
        span: &Span,
        assert_condition: bool,
    ) -> Result<Register> {
        // TODO: If expr is a loop expr or a loop var, look up.
        if let Some(reg) = self.loop_expr_register_map.get(expr).cloned() {
            let result_reg = reg;
            // If this expression should be asserted as a condition, emit AssertCondition
            if assert_condition {
                self.emit_instruction(
                    Instruction::AssertCondition {
                        condition: result_reg,
                    },
                    span,
                );
            }
            return Ok(result_reg);
        }

        let result_reg = match expr.as_ref() {
            Expr::Number { value, .. } => {
                let dest = self.alloc_register();
                let literal_idx = self.add_literal(value.clone());
                self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
                dest
            }
            Expr::String { value, .. } | Expr::RawString { value, .. } => {
                let dest = self.alloc_register();
                let literal_idx = self.add_literal(value.clone());
                self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
                dest
            }
            Expr::Bool { value, .. } => {
                let dest = self.alloc_register();
                let literal_idx = self.add_literal(value.clone());
                self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
                dest
            }
            Expr::Null { .. } => {
                let dest = self.alloc_register();
                let literal_idx = self.add_literal(Value::Null);
                self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
                dest
            }
            Expr::Array { items, .. } => {
                // Compile all elements first
                let mut element_registers = Vec::new();
                for item in items {
                    // Don't assert conditions for array items
                    let item_reg = self.compile_rego_expr_with_span(item, item.span(), false)?;
                    element_registers.push(item_reg);
                }

                // Create array from elements using ArrayCreate (returns undefined if any element is undefined)
                let dest = self.alloc_register();
                let params = ArrayCreateParams {
                    dest,
                    elements: element_registers,
                };
                let params_index = self
                    .program
                    .instruction_data
                    .add_array_create_params(params);
                self.emit_instruction(Instruction::ArrayCreate { params_index }, span);

                dest
            }
            Expr::Set { items, .. } => {
                // Compile all elements first
                let mut element_registers = Vec::new();
                for item in items {
                    // Don't assert conditions for set items
                    let item_reg = self.compile_rego_expr_with_span(item, item.span(), false)?;
                    element_registers.push(item_reg);
                }

                // Create set from elements using SetCreate (returns undefined if any element is undefined)
                let dest = self.alloc_register();
                let params = SetCreateParams {
                    dest,
                    elements: element_registers,
                };
                let params_index = self.program.instruction_data.add_set_create_params(params);
                self.emit_instruction(Instruction::SetCreate { params_index }, span);

                dest
            }
            Expr::Object { fields, .. } => {
                let dest = self.alloc_register();

                // First pass: compile all values and store in array
                let mut value_regs = Vec::new();
                for (_, _key_expr, value_expr) in fields {
                    let value_reg =
                        self.compile_rego_expr_with_span(value_expr, value_expr.span(), false)?;
                    value_regs.push(value_reg);
                }

                // Second pass: determine keys and categorize them
                let mut literal_key_fields = Vec::new();
                let mut non_literal_key_fields = Vec::new();
                let mut literal_keys = Vec::new();

                for (field_idx, (_, key_expr, _value_expr)) in fields.iter().enumerate() {
                    let value_reg = value_regs[field_idx];

                    // Check if key expression is a literal (String, Number, Bool, Null, etc.)
                    let key_literal = match key_expr.as_ref() {
                        Expr::String { value, .. }
                        | Expr::RawString { value, .. }
                        | Expr::Number { value, .. }
                        | Expr::Bool { value, .. }
                        | Expr::Null { value, .. } => Some(value.clone()),
                        _ => None,
                    };

                    if let Some(key_value) = key_literal {
                        // Key is a literal - add to literal table and use literal key field
                        let literal_idx = self.add_literal(key_value.clone());
                        literal_key_fields.push((literal_idx, value_reg));
                        literal_keys.push(key_value);
                    } else {
                        // Key is not a literal - compile it and use non-literal key field
                        let key_reg =
                            self.compile_rego_expr_with_span(key_expr, key_expr.span(), false)?;
                        non_literal_key_fields.push((key_reg, value_reg));
                    }
                }

                // Always create template object - even if empty for consistency
                let template_literal_idx = {
                    // Collect all literal keys for template
                    let mut template_keys = literal_keys.clone();
                    template_keys.sort();

                    // Create template object with all literal keys set to undefined
                    use alloc::collections::BTreeMap;
                    let mut template_obj = BTreeMap::new();
                    for key in &template_keys {
                        template_obj.insert(key.clone(), Value::Undefined);
                    }

                    let template_value = Value::Object(crate::Rc::new(template_obj));
                    self.add_literal(template_value)
                };

                // Sort literal key fields by literal key value for better performance
                literal_key_fields.sort_by(|a, b| {
                    let key_a = &self.program.literals[a.0 as usize];
                    let key_b = &self.program.literals[b.0 as usize];
                    key_a.cmp(key_b)
                });

                // Create ObjectCreate instruction
                let params = ObjectCreateParams {
                    dest,
                    template_literal_idx,
                    literal_key_fields,
                    fields: non_literal_key_fields,
                };
                let params_index = self
                    .program
                    .instruction_data
                    .add_object_create_params(params);
                self.emit_instruction(Instruction::ObjectCreate { params_index }, span);

                dest
            }
            Expr::ArithExpr { lhs, op, rhs, .. } => {
                // Don't assert conditions for operands
                // TODO: Determine assertion
                let lhs_reg = self.compile_rego_expr_with_span(lhs, lhs.span(), false)?;
                let rhs_reg = self.compile_rego_expr_with_span(rhs, rhs.span(), false)?;
                let dest = self.alloc_register();

                match op {
                    crate::ast::ArithOp::Add => {
                        self.emit_instruction(
                            Instruction::Add {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                    crate::ast::ArithOp::Sub => {
                        self.emit_instruction(
                            Instruction::Sub {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                    crate::ast::ArithOp::Mul => {
                        self.emit_instruction(
                            Instruction::Mul {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                    crate::ast::ArithOp::Div => {
                        self.emit_instruction(
                            Instruction::Div {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                    crate::ast::ArithOp::Mod => {
                        self.emit_instruction(
                            Instruction::Mod {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                }
                dest
            }
            Expr::BoolExpr { lhs, op, rhs, .. } => {
                // Don't assert conditions for operands
                let lhs_reg = self.compile_rego_expr_with_span(lhs, lhs.span(), false)?;
                let rhs_reg = self.compile_rego_expr_with_span(rhs, rhs.span(), false)?;
                let dest = self.alloc_register();

                match op {
                    crate::ast::BoolOp::Eq => {
                        self.emit_instruction(
                            Instruction::Eq {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                    crate::ast::BoolOp::Lt => {
                        self.emit_instruction(
                            Instruction::Lt {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                    crate::ast::BoolOp::Gt => {
                        self.emit_instruction(
                            Instruction::Gt {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                    crate::ast::BoolOp::Ge => {
                        self.emit_instruction(
                            Instruction::Ge {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                    crate::ast::BoolOp::Le => {
                        self.emit_instruction(
                            Instruction::Le {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                    crate::ast::BoolOp::Ne => {
                        self.emit_instruction(
                            Instruction::Ne {
                                dest,
                                left: lhs_reg,
                                right: rhs_reg,
                            },
                            span,
                        );
                    }
                }
                dest
            }
            Expr::AssignExpr { .. } => {
                let binding_plan =
                    self.expect_binding_plan_for_expr(expr, "assignment expression")?;

                let result: Result<Register> = match binding_plan {
                    BindingPlan::Assignment { plan } => self
                        .compile_assignment_plan_using_hoisted_destructuring(&plan, span)
                        .map_err(CompilerError::from),
                    other => Err(CompilerError::UnexpectedBindingPlan {
                        context: "assignment expression".to_string(),
                        found: format!("{other:?}"),
                    }),
                };

                return result;
            }
            Expr::Var { value, .. } => {
                // Check if this is a variable reference that we should resolve
                if let Value::String(_var_name) = value {
                    self.compile_chained_ref(expr, span)?
                } else {
                    // Otherwise, load as literal value
                    let dest = self.alloc_register();
                    let literal_idx = self.add_literal(value.clone());
                    self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
                    dest
                }
            }
            // Use sophisticated chained reference compilation
            Expr::RefDot { .. } => self.compile_chained_ref(expr, span)?,
            Expr::RefBrack { .. } => self.compile_chained_ref(expr, span)?,
            Expr::Membership {
                value, collection, ..
            } => {
                // Compile the value to check (don't assert)
                let value_reg = self.compile_rego_expr_with_span(value, value.span(), false)?;

                // Compile the collection (don't assert)
                let collection_reg =
                    self.compile_rego_expr_with_span(collection, collection.span(), false)?;

                // Check membership using a specialized instruction
                let dest = self.alloc_register();
                self.emit_instruction(
                    Instruction::Contains {
                        dest,
                        collection: collection_reg,
                        value: value_reg,
                    },
                    span,
                );

                dest
            }
            Expr::ArrayCompr { term, query, .. } => {
                self.compile_array_comprehension(term, query, span)?
            }
            Expr::SetCompr { term, query, .. } => {
                self.compile_set_comprehension(term, query, span)?
            }
            Expr::ObjectCompr {
                key, value, query, ..
            } => self.compile_object_comprehension(key, value, query, span)?,
            Expr::Call { fcn, params, .. } => {
                // Compile function call
                self.compile_function_call(fcn, params, span.clone())?
            }
            Expr::UnaryExpr { expr, .. } => {
                // Handle unary minus operator (only for numeric literals)
                match expr.as_ref() {
                    Expr::Number { .. } if !expr.span().text().starts_with('-') => {
                        // Compile the operand
                        let operand_reg =
                            self.compile_rego_expr_with_span(expr, expr.span(), false)?;

                        // Create a zero literal
                        let zero_literal_idx = self.add_literal(Value::from(0));
                        let zero_reg = self.alloc_register();
                        self.emit_instruction(
                            Instruction::Load {
                                dest: zero_reg,
                                literal_idx: zero_literal_idx,
                            },
                            span,
                        );

                        // Subtract operand from zero (0 - operand = -operand)
                        let dest = self.alloc_register();
                        self.emit_instruction(
                            Instruction::Sub {
                                dest,
                                left: zero_reg,
                                right: operand_reg,
                            },
                            span,
                        );
                        dest
                    }
                    _ => {
                        return Err(CompilerError::InvalidUnaryMinus);
                    }
                }
            }
            Expr::BinExpr { op, lhs, rhs, .. } => {
                // Handle binary operators: union (|) and intersection (&)
                // Don't assert conditions for operands
                let lhs_reg = self.compile_rego_expr_with_span(lhs, lhs.span(), false)?;
                let rhs_reg = self.compile_rego_expr_with_span(rhs, rhs.span(), false)?;

                let dest = self.alloc_register();

                match op {
                    crate::ast::BinOp::Union => {
                        // Create builtin call for sets.union
                        let builtin_index = self.get_builtin_index("sets.union")?;
                        let params = crate::rvm::instructions::BuiltinCallParams {
                            dest,
                            builtin_index,
                            num_args: 2,
                            args: [lhs_reg, rhs_reg, 0, 0, 0, 0, 0, 0],
                        };
                        let params_index = self
                            .program
                            .instruction_data
                            .add_builtin_call_params(params);
                        self.emit_instruction(Instruction::BuiltinCall { params_index }, span);
                    }
                    crate::ast::BinOp::Intersection => {
                        // Create builtin call for sets.intersection
                        let builtin_index = self.get_builtin_index("sets.intersection")?;
                        let params = crate::rvm::instructions::BuiltinCallParams {
                            dest,
                            builtin_index,
                            num_args: 2,
                            args: [lhs_reg, rhs_reg, 0, 0, 0, 0, 0, 0],
                        };
                        let params_index = self
                            .program
                            .instruction_data
                            .add_builtin_call_params(params);
                        self.emit_instruction(Instruction::BuiltinCall { params_index }, span);
                    }
                }
                dest
            }
            #[cfg(feature = "rego-extensions")]
            Expr::OrExpr { lhs, rhs, .. } => {
                // Handle logical OR expression: lhs || rhs
                // If lhs is false, null, or undefined, return rhs; otherwise return lhs
                let lhs_reg = self.compile_rego_expr_with_span(lhs, lhs.span(), false)?;
                let rhs_reg = self.compile_rego_expr_with_span(rhs, rhs.span(), false)?;

                let dest = self.alloc_register();

                // Use the Or instruction for logical OR
                self.emit_instruction(
                    Instruction::Or {
                        dest,
                        left: lhs_reg,
                        right: rhs_reg,
                    },
                    span,
                );
                dest
            }
        };

        // If this expression should be asserted as a condition, emit AssertCondition
        if assert_condition {
            self.emit_instruction(
                Instruction::AssertCondition {
                    condition: result_reg,
                },
                span,
            );
        }

        Ok(result_reg)
    }

    /// Compile from a CompiledPolicy to RVM Program
    pub fn compile_from_policy(
        policy: &CompiledPolicy,
        entry_points: &[&str],
    ) -> Result<Arc<Program>> {
        let mut compiler = Compiler::with_policy(policy);
        compiler.current_rule_path = "".to_string(); // Entry point has no caller
        let rules = policy.get_rules();

        // Emit CallRule instructions for each entry point and track their instruction indices
        for &entry_point_name in entry_points {
            let instruction_index = compiler.program.instructions.len();
            let result_reg = compiler.alloc_register();
            let rule_idx = compiler.get_or_assign_rule_index(entry_point_name)?;
            compiler
                .entry_points
                .insert(entry_point_name.to_string(), instruction_index);
            compiler.emit_call_rule(result_reg, rule_idx);

            // Add Return instruction for this entry point
            compiler.emit_return(result_reg);
        }

        compiler.compile_worklist_rules(rules)?;

        let program = Arc::new(compiler.finish()?);
        Ok(program)
    }

    fn compile_worklist_rules(
        &mut self,
        rules: &Map<String, Vec<crate::ast::NodeRef<Rule>>>,
    ) -> Result<()> {
        // Track compiled rules to avoid recompilation
        let mut compiled_rules = BTreeSet::new();
        let mut call_stack = Vec::new(); // Track current call stack for recursion detection

        // Now compile all rules in the worklist (set rules referenced via CallRule)
        while !self.rule_worklist.is_empty() {
            let entry = self.rule_worklist.remove(0);

            // Check for recursion using the call stack stored in the entry
            if let Some(&target_rule_index) = self.rule_index_map.get(&entry.rule_path) {
                if entry.call_stack.contains(&target_rule_index) {
                    // Build the recursive chain for error message
                    let mut chain = Vec::new();
                    let mut found_start = false;
                    for &rule_idx in &entry.call_stack {
                        if rule_idx == target_rule_index {
                            found_start = true;
                        }
                        if found_start {
                            // Find rule path for this index
                            if let Some((rule_path, _)) =
                                self.rule_index_map.iter().find(|(_, &idx)| idx == rule_idx)
                            {
                                chain.push(rule_path.clone());
                            }
                        }
                    }
                    chain.push(entry.rule_path.clone());

                    return Err(CompilerError::General {
                        message: format!(
                            "Compile-time recursion detected in rule call chain: {}",
                            chain.join(" -> ")
                        ),
                    });
                }
            }

            // Skip if already compiled
            if compiled_rules.contains(&entry.rule_path) {
                continue;
            }

            // Get rule index for call stack tracking
            let rule_index = if let Some(&index) = self.rule_index_map.get(&entry.rule_path) {
                index
            } else {
                return Err(CompilerError::General {
                    message: format!("Rule index not found for '{}'", entry.rule_path),
                });
            };

            // Add to call stack
            call_stack.push(entry.rule_path.clone());

            // Set current rule context for tracking caller context
            let old_rule_path = self.current_rule_path.clone();
            let old_call_stack = self.current_call_stack.clone();
            self.current_rule_path = entry.rule_path.clone();
            self.current_call_stack = entry.call_stack.clone();
            self.current_call_stack.push(rule_index);

            let result = self.compile_worklist_rule(&entry.rule_path, rules);

            // Restore previous rule context
            self.current_rule_path = old_rule_path;
            self.current_call_stack = old_call_stack;

            // Remove from call stack
            call_stack.pop();

            result?;
            compiled_rules.insert(entry.rule_path);
        }
        Ok(())
    }

    /// Compile a set rule from the worklist - each variant gets its own entry point
    fn compile_worklist_rule(
        &mut self,
        rule_path: &str,
        rules: &Map<String, Vec<crate::ast::NodeRef<Rule>>>,
    ) -> Result<()> {
        // Find the module that contains this rule and use its package and index
        let (module_package, module_index) =
            self.find_module_package_and_index_for_rule(rule_path, rules)?;

        // Set up compilation context for this rule's package and module
        let saved_package = self.current_package.clone();
        let saved_module_index = self.current_module_index;
        self.current_package = module_package.clone();
        self.current_module_index = module_index;

        let saved_register_counter = self.register_counter;
        if let Some(rule_definitions) = rules.get(rule_path) {
            let rule_index = self.rule_index_map.get(rule_path).copied().ok_or_else(|| {
                CompilerError::General {
                    message: format!(
                        "Rule '{}' not found in rule index map during compilation",
                        rule_path
                    ),
                }
            })?;
            let rule_type = self.rule_types[rule_index as usize].clone();

            // All rules will return their results in register 0.
            let result_register = 0;

            // Store the result register for this rule
            // Ensure rule_result_registers has enough capacity
            while self.rule_result_registers.len() <= rule_index as usize {
                self.rule_result_registers.push(0); // Default to register 0
            }
            self.rule_result_registers[rule_index as usize] = result_register;

            // Ensure rule_definitions vec has space for this rule
            while self.rule_definitions.len() <= rule_index as usize {
                self.rule_definitions.push(Vec::new());
            }

            // Ensure rule_definition_function_params vec has space for this rule
            while self.rule_definition_function_params.len() <= rule_index as usize {
                self.rule_definition_function_params.push(Vec::new());
            }

            // Ensure rule_definition_destructuring_patterns vec has space for this rule
            while self.rule_definition_destructuring_patterns.len() <= rule_index as usize {
                self.rule_definition_destructuring_patterns.push(Vec::new());
            }

            let mut num_registers_used = 0;
            let mut rule_param_count: Option<usize> = None;

            // Compile each definition (Rule::Spec)
            for (def_idx, rule_ref) in rule_definitions.iter().enumerate() {
                core::convert::identity(def_idx);
                if let Rule::Spec { head, bodies, span } = rule_ref.as_ref() {
                    // Set up register window for this rule definition - each rule starts with registers from 0
                    self.push_scope();
                    self.register_counter = 0; // Reset to 0 for this rule's window

                    // Allocate result register within the window (starts at 0)
                    let result_register = self.alloc_register(); // This will be 0

                    // Set the current module index based on which module contains this rule
                    self.current_module_index = self.find_module_index_for_rule(rule_ref)?;

                    let (key_expr, value_expr) = match head {
                        RuleHead::Compr { refr, assign, .. } => {
                            // Store None for non-function definition
                            self.rule_definition_function_params[rule_index as usize].push(None);
                            self.rule_definition_destructuring_patterns[rule_index as usize]
                                .push(None);

                            let output_expr = assign.as_ref().map(|assign| assign.value.clone());
                            let key_expr = match refr.as_ref() {
                                Expr::RefBrack { index, .. } => {
                                    // For RefBrack, the index is the key expression
                                    Some(index.clone())
                                }
                                _ => {
                                    // For non-RefBrack, no key expression
                                    None
                                }
                            };
                            (key_expr, output_expr)
                        }
                        RuleHead::Set { key, .. } => {
                            // Store None for non-function definition
                            self.rule_definition_function_params[rule_index as usize].push(None);
                            self.rule_definition_destructuring_patterns[rule_index as usize]
                                .push(None);

                            // For set rules, no separate key_expr, output_expr is the key
                            (None, key.clone())
                        }
                        RuleHead::Func { assign, args, .. } => {
                            // Set up function parameters for THIS definition
                            let mut param_names = Vec::new();
                            let mut last_param_span: Option<Span> = None;

                            let destructuring_entry = if args.is_empty() {
                                None
                            } else {
                                Some(self.program.instructions.len())
                            };

                            let param_base_register = self.register_counter;
                            self.register_counter =
                                self.register_counter.saturating_add(args.len() as u8);

                            for (arg_idx, arg) in args.iter().enumerate() {
                                let param_reg = param_base_register + arg_idx as u8;

                                let param_name = match arg.as_ref() {
                                    Expr::Var {
                                        value: Value::String(name),
                                        ..
                                    } => name.to_string(),
                                    _ => format!("__param_{}", arg_idx),
                                };
                                param_names.push(param_name);

                                let context_desc = format!("function parameter {arg_idx}");
                                let binding_plan =
                                    self.expect_binding_plan_for_expr(arg, &context_desc)?;

                                if let BindingPlan::Parameter { .. } = &binding_plan {
                                    self.apply_binding_plan(&binding_plan, param_reg, arg.span())
                                        .map_err(CompilerError::from)?;
                                } else {
                                    return Err(CompilerError::UnexpectedBindingPlan {
                                        context: context_desc,
                                        found: format!("{binding_plan:?}"),
                                    });
                                }

                                last_param_span = Some(arg.span().clone());
                            }

                            // Store the parameter names for this definition
                            self.rule_definition_function_params[rule_index as usize]
                                .push(Some(param_names.clone()));

                            if let Some(entry) = destructuring_entry {
                                let success_span = last_param_span.as_ref().unwrap_or(span);
                                self.emit_instruction(
                                    crate::rvm::instructions::Instruction::DestructuringSuccess {},
                                    success_span,
                                );
                                self.rule_definition_destructuring_patterns[rule_index as usize]
                                    .push(Some(entry as u32));
                            } else {
                                self.rule_definition_destructuring_patterns[rule_index as usize]
                                    .push(None);
                            }

                            // Validate and set rule-level parameter count
                            match rule_param_count {
                                None => {
                                    // First definition sets the parameter count
                                    rule_param_count = Some(param_names.len());
                                }
                                Some(expected_count) => {
                                    // Subsequent definitions must have the same parameter count
                                    if param_names.len() != expected_count {
                                        return Err(CompilerError::General {
                                            message: format!(
                                                "Function rule '{}' definition {} has {} parameters but expected {} parameters",
                                                rule_path, def_idx, param_names.len(), expected_count
                                            ),
                                        });
                                    }
                                }
                            }

                            // For function rules, the output expression comes from the assignment
                            match assign {
                                Some(assignment) => (None, Some(assignment.value.clone())),
                                None => (None, None),
                            }
                        }
                    };

                    let span = match (&key_expr, &value_expr) {
                        (_, Some(expr)) => expr.span().clone(),
                        (Some(expr), _) => expr.span().clone(),
                        _ => span.clone(),
                    };

                    let context = CompilationContext {
                        dest_register: result_register,
                        context_type: ContextType::Rule(rule_type.clone()),
                        key_expr,
                        value_expr,
                        span,
                        key_value_loops_hoisted: false,
                    };
                    self.push_context(context);
                    let mut body_entry_points = Vec::new();

                    // Handle rules with no bodies but assignment expressions (like my_set := {1, 2, 3})
                    if bodies.is_empty() {
                        let value_expr_opt = self.context_stack.last().unwrap().value_expr.clone();
                        if let Some(value_expr) = value_expr_opt {
                            // Create a single body entry point for the assignment
                            let body_entry_point = self.program.instructions.len() as u32;
                            body_entry_points.push(body_entry_point);

                            self.push_scope();
                            // Reset input/data registers for this rule body
                            self.reset_rule_definition_registers();

                            self.emit_instruction(
                                Instruction::RuleInit {
                                    result_reg: result_register,
                                    rule_index,
                                },
                                value_expr.span(),
                            );

                            // Compile the assignment expression
                            // Call emit_context_yield to move the result to the result register
                            self.emit_context_yield()?;

                            // Emit Rule Return
                            self.emit_instruction(Instruction::RuleReturn {}, value_expr.span());
                            self.pop_scope();
                        }
                    } else {
                        // Compile each body within this definition
                        for (body_idx, body) in bodies.iter().enumerate() {
                            self.push_scope();

                            // Reset input/data registers for each rule body
                            self.reset_rule_definition_registers();

                            let body_entry_point = self.program.instructions.len() as u32;
                            body_entry_points.push(body_entry_point);

                            core::convert::identity(body_idx);

                            self.emit_instruction(
                                Instruction::RuleInit {
                                    result_reg: result_register,
                                    rule_index,
                                },
                                &body.span,
                            );

                            // 1. Compile the query (with proper loop hoisting)
                            if !body.query.stmts.is_empty() {
                                self.compile_query(&body.query)?;
                            } else {
                                // Check if there's an assignment expression in the rule head (for rules like my_set := {1, 2, 3})
                                let value_expr_opt =
                                    self.context_stack.last().unwrap().value_expr.clone();
                                if let Some(value_expr) = value_expr_opt {
                                    // For rules with empty bodies but assignment expressions
                                    // compile the assignment expression and store it in the result register
                                    let value_reg = self.compile_rego_expr(&value_expr)?;
                                    self.emit_instruction(
                                        Instruction::Move {
                                            dest: result_register,
                                            src: value_reg,
                                        },
                                        value_expr.span(),
                                    );
                                }
                            }

                            // 2. Emit Rule Return
                            self.emit_instruction(Instruction::RuleReturn {}, &body.span);

                            self.pop_scope();
                        }
                    }

                    self.pop_scope();

                    // Store the body entry points for this definition
                    self.rule_definitions[rule_index as usize].push(body_entry_points);

                    if self.register_counter > num_registers_used {
                        num_registers_used = self.register_counter;
                    }
                }
            }

            // Calculate the number of registers used by this rule (window starts at 0)

            // Store the number of registers used by this rule
            // Ensure rule_num_registers has enough capacity
            while self.rule_num_registers.len() <= rule_index as usize {
                self.rule_num_registers.push(0); // Default to 0 registers
            }
            self.rule_num_registers[rule_index as usize] = num_registers_used;

            // Store the rule-level function parameter count
            self.rule_function_param_count[rule_index as usize] = rule_param_count;

            // Add the compiled rule to the rule tree for efficient lookups
            // Skip function rules since they require parameters and cannot be evaluated via virtual data document lookup
            if rule_param_count.is_none() {
                // Parse the rule path to extract package path and rule name
                let rule_path_parts: Vec<&str> = rule_path.split('.').collect();
                if let Some((rule_name, package_parts)) = rule_path_parts.split_last() {
                    let package_path: Vec<String> =
                        package_parts.iter().map(|s| s.to_string()).collect();

                    let _ = self.program.add_rule_to_tree(
                        &package_path,
                        rule_name,
                        rule_index as usize,
                    );
                }
            }

            // Restore the global register counter and package context
            self.register_counter = saved_register_counter;
            self.current_package = saved_package;
            self.current_module_index = saved_module_index;
        }

        Ok(())
    }

    /// Compile a query (statements with proper loop hoisting, similar to interpreter's eval_stmts)
    fn compile_query(&mut self, query: &crate::ast::Query) -> Result<()> {
        // Push a new scope for this query
        self.push_scope();

        let result = {
            let schedule = match &self.policy.inner.schedule {
                Some(s) => s.queries.get(self.current_module_index, query.qidx),
                None => None,
            };

            let ordered_stmts: Vec<&crate::ast::LiteralStmt> = match schedule {
                Some(schedule) => schedule
                    .order
                    .iter()
                    .map(|i| &query.stmts[*i as usize])
                    .collect(),
                None => query.stmts.iter().collect(),
            };
            self.hoist_loops_and_compile_statements(&ordered_stmts)
        };

        // Pop the scope after compilation
        self.pop_scope();

        result
    }

    /// Hoist loops from statements and compile them with proper sequencing (similar to interpreter's eval_stmts)
    fn hoist_loops_and_compile_statements(
        &mut self,
        stmts: &[&crate::ast::LiteralStmt],
    ) -> Result<()> {
        for (idx, stmt) in stmts.iter().enumerate() {
            let loop_exprs = self.get_statement_loops(stmt)?;

            if !loop_exprs.is_empty() {
                return self.compile_hoisted_loops(&stmts[idx..], &loop_exprs);
            }

            if matches!(&stmt.literal, crate::ast::Literal::SomeIn { .. }) {
                if let crate::ast::Literal::SomeIn {
                    ref key,
                    ref value,
                    ref collection,
                    ..
                } = &stmt.literal
                {
                    self.compile_some_in_loop_with_remaining_statements(
                        key,
                        value,
                        collection,
                        &stmts[idx..],
                    )?;
                    return Ok(());
                }
            }

            self.compile_single_statement(stmt)?;
        }

        self.hoist_loops_and_emit_context_yield()
    }

    /// Compile statements within loops (similar to interpreter's eval_stmts_in_loop)
    fn compile_hoisted_loops(
        &mut self,
        stmts: &[&crate::ast::LiteralStmt],
        loops: &[HoistedLoop],
    ) -> Result<()> {
        if loops.is_empty() {
            // No more loops, compile the current statement.
            if !stmts.is_empty() {
                self.compile_single_statement(stmts[0])?;
                // Remaining statements may have loops, so compile them recursively.
                return self.hoist_loops_and_compile_statements(&stmts[1..]);
            } else {
                self.hoist_loops_and_emit_context_yield()?;
            }
        }

        let current_loop = &loops[0];
        let remaining_loops = &loops[1..];

        match current_loop.loop_type {
            LoopType::IndexIteration => {
                // Compile index iteration loop
                self.compile_index_iteration_loop(
                    &current_loop.loop_expr,
                    &current_loop.key,
                    &current_loop.value,
                    &current_loop.collection,
                    stmts,
                    remaining_loops,
                )?;
                Ok(())
            }
            LoopType::Walk => Err(CompilerError::General {
                message: "walk loops are not yet supported in the RVM compiler".to_string(),
            }),
        }
    }

    fn hoist_loops_and_emit_context_yield(&mut self) -> Result<()> {
        // Check if we're in an Every quantifier context - if so, don't emit context yield
        // Every quantifiers are assertions, not value-producing expressions
        if let Some(context) = self.context_stack.last() {
            // Check if this is an Every context that doesn't need context yield
            match &context.context_type {
                ContextType::Every => {
                    // Every quantifiers don't emit context yield
                    return Ok(());
                }
                ContextType::Rule(_) => {
                    // This is a rule context, proceed with normal context yield logic
                }
                ContextType::Comprehension(_) => {
                    // This is a comprehension context, proceed with normal context yield logic
                }
            }
        }

        if let Some(context) = self.context_stack.last_mut() {
            if context.key_value_loops_hoisted {
                // Loops already hoisted, emit context yield
                self.emit_context_yield()
            } else {
                let mut key_value_loops = Vec::new();

                let key_expr = context.key_expr.clone();
                let value_expr = context.value_expr.clone();

                if let Some(expr) = key_expr.as_ref() {
                    key_value_loops.extend(self.get_expr_loops(expr));
                }

                if let Some(expr) = value_expr.as_ref() {
                    key_value_loops.extend(self.get_expr_loops(expr));
                }

                if !key_value_loops.is_empty() {
                    // Mark that we've hoisted loops to prevent infinite recursion
                    self.context_stack
                        .last_mut()
                        .unwrap()
                        .key_value_loops_hoisted = true;

                    // Recursively compile the hoisted loops
                    self.compile_hoisted_loops(&[], &key_value_loops)
                } else {
                    // No loops to hoist, emit context yield
                    self.emit_context_yield()
                }
            }
        } else {
            // No context, just return without error
            Ok(())
        }
    }

    /// Compile an Every quantifier
    fn compile_every_quantifier(
        &mut self,
        key: &Option<crate::lexer::Span>,
        value: &crate::lexer::Span,
        domain: &ExprRef,
        query: &crate::ast::Query,
        span: &crate::lexer::Span,
    ) -> Result<()> {
        // Compile the domain expression
        let collection_reg = self.compile_rego_expr(domain)?;

        // Allocate registers for loop variables
        let key_reg = self.alloc_register();
        let value_reg = self.alloc_register();
        let result_reg = self.alloc_register();

        // Extract variable names from the spans
        let value_var_name = value.text().to_string();
        let key_var_name = key.as_ref().map(|k| k.text().to_string());

        // Check if key is actually needed (not None and not underscore)
        let actual_key_reg =
            if key_var_name.is_none() || key_var_name.as_ref() == Some(&"_".to_string()) {
                value_reg // Set key_reg = value_reg to indicate key not needed
            } else {
                key_reg
            };

        // Generate loop start instruction for Every mode
        let loop_params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::Every,
            collection: collection_reg,
            key_reg: actual_key_reg,
            value_reg,
            result_reg,
            body_start: 0, // Will be updated
            loop_end: 0,   // Will be updated
        });

        self.emit_instruction(
            Instruction::LoopStart {
                params_index: loop_params_index,
            },
            span,
        );

        let body_start = self.program.instructions.len() as u16;

        // Push new scope for loop variables (Every needs explicit scope management)
        self.push_scope();

        // Push Every context - this will prevent context yield emission
        let every_context = CompilationContext {
            context_type: ContextType::Every,
            dest_register: result_reg, // Not used for Every but required
            key_expr: None,
            value_expr: None,
            span: span.clone(),
            key_value_loops_hoisted: false,
        };
        self.push_context(every_context);

        // Add loop variables to scope using their actual names
        self.add_variable(&value_var_name, value_reg);
        if let Some(ref key_name) = key_var_name {
            self.add_variable(key_name, key_reg);
        }

        // Compile the query body using standard query compilation
        // Note: compile_query will push/pop its own additional scope
        self.compile_query(query)?;

        // Pop Every context and scope
        self.pop_context();
        self.pop_scope();

        // Add LoopNext instruction
        self.emit_instruction(
            Instruction::LoopNext {
                body_start,
                loop_end: 0, // Will be updated
            },
            span,
        );

        let loop_end = self.program.instructions.len() as u16;

        // Update the loop parameters with actual body_start and loop_end
        self.program
            .update_loop_params(loop_params_index, |params| {
                params.body_start = body_start;
                params.loop_end = loop_end;
            });

        // Update the LoopNext instruction
        let loop_next_idx = self.program.instructions.len() - 1;
        if let Instruction::LoopNext {
            loop_end: ref mut end,
            ..
        } = &mut self.program.instructions[loop_next_idx]
        {
            *end = loop_end;
        }

        Ok(())
    }

    /// Compile a single statement without loops
    fn compile_single_statement(&mut self, stmt: &crate::ast::LiteralStmt) -> Result<()> {
        match &stmt.literal {
            crate::ast::Literal::Expr { expr, .. } => {
                let assert_condition = !matches!(expr.as_ref(), Expr::AssignExpr { .. });
                let _condition_reg =
                    self.compile_rego_expr_with_span(expr, &stmt.span, assert_condition)?;
            }
            crate::ast::Literal::SomeIn { .. } => {
                // Should have been handled by loop hoisting
                return Err(CompilerError::SomeInNotHoisted);
            }
            crate::ast::Literal::Every {
                key,
                value,
                domain,
                query,
                ..
            } => {
                self.compile_every_quantifier(key, value, domain, query, &stmt.span)?;

                // Every quantifier acts as an assertion - if it succeeds,
                // we continue with the next statement
            }
            crate::ast::Literal::SomeVars { span: _span, vars } => {
                // Add each variable to the current scope's unbound variables
                for var in vars {
                    self.add_unbound_variable(var.text());
                }
            }
            crate::ast::Literal::NotExpr { expr, .. } => {
                // Compile the expression (don't assert it directly)
                let expr_reg = self.compile_rego_expr_with_span(expr, expr.span(), false)?;

                // Negate the expression using the Not instruction
                let negated_reg = self.alloc_register();
                self.emit_instruction(
                    Instruction::Not {
                        dest: negated_reg,
                        operand: expr_reg,
                    },
                    &stmt.span,
                );

                // Assert that the negated expression is true (original expression is false)
                self.emit_instruction(
                    Instruction::AssertCondition {
                        condition: negated_reg,
                    },
                    &stmt.span,
                );
            }
        }
        Ok(())
    }

    /// Compile index iteration loop (for patterns like collection[_], collection[idx], etc.)
    fn compile_index_iteration_loop(
        &mut self,
        loop_expr: &Option<ExprRef>,
        key_var: &Option<ExprRef>,
        _value_var: &ExprRef,
        collection: &ExprRef,
        remaining_stmts: &[&crate::ast::LiteralStmt],
        remaining_loops: &[HoistedLoop],
    ) -> Result<()> {
        // Compile the collection expression
        let collection_reg = self.compile_rego_expr(collection)?;

        // Allocate registers for loop variables
        let key_reg = self.alloc_register(); // index
        let value_reg = self.alloc_register(); // element
        let result_reg = self.alloc_register();

        if let Some(loop_expr) = loop_expr {
            self.loop_expr_register_map
                .insert(loop_expr.clone(), value_reg);
        }
        let mut key_binding_plan: Option<(BindingPlan, Span)> = None;
        if let Some(key_var) = key_var {
            if let Some(binding_plan) = self.get_binding_plan_for_expr(key_var) {
                if let BindingPlan::LoopIndex { .. } = &binding_plan {
                    key_binding_plan = Some((binding_plan, key_var.span().clone()));
                } else {
                    return Err(CompilerError::UnexpectedBindingPlan {
                        context: format!("loop index pattern {}", key_var.span().text()),
                        found: format!("{binding_plan:?}"),
                    });
                }
            } else {
                match key_var.as_ref() {
                    crate::ast::Expr::Var { value, .. } => {
                        let var_name = match value {
                            Value::String(s) => {
                                if s.as_ref() == "_" {
                                    "".to_string()
                                } else {
                                    s.to_string()
                                }
                            }
                            _ => value.to_string(),
                        };
                        if !var_name.is_empty() && var_name != "_" {
                            self.store_variable(var_name, key_reg);
                        }
                    }
                    _ => {
                        return Err(CompilerError::MissingBindingPlan {
                            context: format!("loop index pattern {}", key_var.span().text()),
                        });
                    }
                }
            }
            self.loop_expr_register_map.insert(key_var.clone(), key_reg);
        }

        // Generate loop start instruction
        let loop_params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::ForEach,
            collection: collection_reg,
            key_reg,
            value_reg,
            result_reg,
            body_start: 0, // Will be updated
            loop_end: 0,   // Will be updated
        });
        self.emit_instruction(
            Instruction::LoopStart {
                params_index: loop_params_index,
            },
            collection.span(),
        );

        let body_start = self.program.instructions.len() as u16;

        if let Some((binding_plan, plan_span)) = key_binding_plan.as_ref() {
            self.apply_binding_plan(binding_plan, key_reg, plan_span)
                .map_err(CompilerError::from)?;
        }

        // Include the first statement as part of the loop body, then compile remaining statements.
        let body_stmts = &remaining_stmts[0..];

        // Compile remaining loops and statements as loop body
        self.compile_hoisted_loops(body_stmts, remaining_loops)?;

        // Add LoopNext instruction
        self.emit_instruction(
            Instruction::LoopNext {
                body_start,
                loop_end: 0, // Will be updated
            },
            collection.span(),
        );

        let loop_end = self.program.instructions.len() as u16;

        // Update the loop parameters with actual body_start and loop_end
        self.program
            .update_loop_params(loop_params_index, |params| {
                params.body_start = body_start;
                params.loop_end = loop_end;
            });

        // Update the LoopNext instruction
        let loop_next_idx = self.program.instructions.len() - 1;
        if let Instruction::LoopNext {
            loop_end: ref mut end,
            ..
        } = &mut self.program.instructions[loop_next_idx]
        {
            *end = loop_end;
        }

        Ok(())
    }

    /// Compile SomeIn with remaining statements
    fn compile_some_in_loop_with_remaining_statements(
        &mut self,
        key: &Option<ExprRef>,
        value: &ExprRef,
        collection: &ExprRef,
        remaining_stmts: &[&crate::ast::LiteralStmt],
    ) -> Result<Register> {
        // Use the existing compile_some_in_loop_with_body method but with proper statement handling
        // Skip the first statement (which is the SomeIn) and use the rest as loop body
        let loop_body_stmts = &remaining_stmts[1..];
        let result_reg =
            self.compile_some_in_loop_with_body(key, value, collection, loop_body_stmts)?;
        Ok(result_reg)
    }
}

impl<'a> Compiler<'a> {
    fn compile_some_in_loop_with_body(
        &mut self,
        key: &Option<ExprRef>,
        value: &ExprRef,
        collection: &ExprRef,
        loop_body_stmts: &[&crate::ast::LiteralStmt],
    ) -> Result<Register> {
        // Compile collection expression
        let collection_reg = self.compile_rego_expr(collection)?;

        // Allocate registers for loop variables
        let key_reg = self.alloc_register();
        let value_reg = self.alloc_register();
        let result_reg = self.alloc_register();

        // Start the existential loop - we'll calculate the correct loop_end after compiling the body

        // Add LoopStart instruction with parameters
        let loop_params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::ForEach, // Use ForEach for some...in loops
            collection: collection_reg,
            key_reg,
            value_reg,
            result_reg,
            body_start: 0, // Will be calculated after adding LoopStart
            loop_end: 0,   // Placeholder
        });
        self.emit_instruction(
            Instruction::LoopStart {
                params_index: loop_params_index,
            },
            collection.span(),
        );

        // Calculate body_start after adding LoopStart instruction
        let body_start = self.program.instructions.len() as u16;

        if let Some(binding_plan) = self.get_binding_plan_for_expr(collection) {
            if let BindingPlan::SomeIn {
                key_plan,
                value_plan,
                ..
            } = &binding_plan
            {
                let key_register = key_plan.as_ref().map(|_| key_reg);
                self.apply_some_in_binding_plan(
                    key_plan.as_ref(),
                    key_register,
                    value_plan,
                    value_reg,
                    collection.span(),
                )
                .map_err(CompilerError::from)?;
            } else {
                return Err(CompilerError::UnexpectedBindingPlan {
                    context: format!("some-in binding {}", collection.span().text()),
                    found: format!("{binding_plan:?}"),
                });
            }
        } else {
            if let Some(key_expr) = key {
                match key_expr.as_ref() {
                    crate::ast::Expr::Var {
                        value: var_name, ..
                    } => {
                        let var_name = var_name.as_string()?.to_string();
                        self.store_variable(var_name, key_reg);
                    }
                    _ => {
                        return Err(CompilerError::MissingBindingPlan {
                            context: format!("some-in key pattern {}", key_expr.span().text()),
                        });
                    }
                }
            }

            match value.as_ref() {
                crate::ast::Expr::Var {
                    value: var_name, ..
                } => {
                    let var_name = var_name.as_string()?.to_string();
                    self.store_variable(var_name, value_reg);
                }
                _ => {
                    return Err(CompilerError::MissingBindingPlan {
                        context: format!("some-in value pattern {}", value.span().text()),
                    });
                }
            }
        }

        // Compile the loop body statements
        self.hoist_loops_and_compile_statements(loop_body_stmts)?;

        // Add LoopNext instruction to continue to next iteration
        self.emit_instruction(
            Instruction::LoopNext {
                body_start,
                loop_end: 0, // Will be updated
            },
            collection.span(),
        );

        // Calculate the correct loop_end (points to instruction after LoopNext)
        let loop_end = self.program.instructions.len() as u16;

        // Update the loop parameters with actual body_start and loop_end
        self.program
            .update_loop_params(loop_params_index, |params| {
                params.body_start = body_start;
                params.loop_end = loop_end;
            });

        // Update the LoopNext instruction with the correct loop_end
        let loop_next_idx = self.program.instructions.len() - 1;
        if let Instruction::LoopNext {
            loop_end: ref mut end,
            ..
        } = &mut self.program.instructions[loop_next_idx]
        {
            *end = loop_end;
        }

        Ok(result_reg)
    }

    /// Shared implementation for compiling comprehensions
    fn compile_comprehension(
        &mut self,
        mode: ComprehensionMode,
        context_type: ComprehensionType,
        key_expr: Option<&ExprRef>,
        value_expr: Option<&ExprRef>,
        query: &crate::ast::Query,
        span: &Span,
    ) -> Result<Register> {
        // Allocate result register and initialize comprehension
        let result_reg = self.alloc_register();

        // For now, we still need to determine key_reg, value_reg dynamically
        // This is a simplified implementation - a full implementation would need to analyze the query
        // to determine these registers properly based on the iteration patterns
        let key_reg = self.alloc_register();
        let value_reg = self.alloc_register();

        let comprehension_params_index =
            self.program
                .add_comprehension_begin_params(ComprehensionBeginParams {
                    mode,
                    collection_reg: result_reg, // The result register is the collection being built
                    result_reg,
                    key_reg,
                    value_reg,
                    body_start: 0, // Will be filled in after emitting ComprehensionBegin
                    comprehension_end: 0, // Will be filled in after compiling query
                });

        self.emit_instruction(
            Instruction::ComprehensionBegin {
                params_index: comprehension_params_index,
            },
            span,
        );

        // Set body_start to the next instruction after ComprehensionBegin
        let body_start = self.program.instructions.len() as u16;

        // Push comprehension context with the appropriate expressions
        let comprehension_context = CompilationContext {
            context_type: ContextType::Comprehension(context_type),
            dest_register: result_reg,
            key_expr: key_expr.cloned(),
            value_expr: value_expr.cloned(),
            span: span.clone(),
            key_value_loops_hoisted: false,
        };
        self.push_context(comprehension_context);

        // Compile the query - this will push/pop its own scope
        self.compile_query(query)?;

        // Pop context
        self.pop_context();

        // Emit ComprehensionEnd instruction
        self.emit_instruction(Instruction::ComprehensionEnd {}, span);

        // Set comprehension_end to the current instruction position
        let comprehension_end = self.program.instructions.len() as u16;

        // Update the comprehension parameters with actual addresses
        self.program
            .update_comprehension_begin_params(comprehension_params_index, |params| {
                params.body_start = body_start;
                params.comprehension_end = comprehension_end;
            });

        Ok(result_reg)
    }

    /// Compile array comprehension [term | query]
    fn compile_array_comprehension(
        &mut self,
        term: &ExprRef,
        query: &crate::ast::Query,
        span: &Span,
    ) -> Result<Register> {
        self.compile_comprehension(
            ComprehensionMode::Array,
            ComprehensionType::Array,
            None,
            Some(term),
            query,
            span,
        )
    }

    /// Compile set comprehension {term | query}
    fn compile_set_comprehension(
        &mut self,
        term: &ExprRef,
        query: &crate::ast::Query,
        span: &Span,
    ) -> Result<Register> {
        self.compile_comprehension(
            ComprehensionMode::Set,
            ComprehensionType::Set,
            None,
            Some(term),
            query,
            span,
        )
    }

    /// Compile object comprehension {key: value | query}
    fn compile_object_comprehension(
        &mut self,
        key: &ExprRef,
        value: &ExprRef,
        query: &crate::ast::Query,
        span: &Span,
    ) -> Result<Register> {
        self.compile_comprehension(
            ComprehensionMode::Object,
            ComprehensionType::Object,
            Some(key),
            Some(value),
            query,
            span,
        )
    }

    /// Compile a function call expression
    fn compile_function_call(
        &mut self,
        fcn: &ExprRef,
        params: &[ExprRef],
        span: Span,
    ) -> Result<Register> {
        // Get the function path
        let fcn_path =
            get_path_string(fcn, None).map_err(|_| CompilerError::InvalidFunctionExpression)?;

        // Try to find user-defined function first with the original path
        let original_fcn_path = fcn_path.clone();
        let full_fcn_path = if self.policy.inner.rules.contains_key(&fcn_path) {
            fcn_path
        } else {
            // If not found, try with current package prefix
            get_path_string(fcn, Some(&self.current_package))
                .map_err(|_| CompilerError::InvalidFunctionExpressionWithPackage)?
        };

        // Compile all parameter expressions first
        let mut arg_regs = Vec::new();
        for param in params.iter() {
            let param_reg = self.compile_rego_expr_with_span(param, param.span(), false)?;
            arg_regs.push(param_reg);
        }

        // Allocate destination register for the result
        let dest = self.alloc_register();

        // First check if this is a user-defined function rule
        if self.is_user_defined_function(&full_fcn_path) {
            // Get the function rule index for user-defined functions
            let rule_index = self.get_or_assign_rule_index(&full_fcn_path)?;

            // Create function call parameters with fixed-size array
            let mut args_array = [0u8; 8];
            let num_args = arg_regs.len().min(8) as u8; // Limit to 8 arguments
            for (i, &reg) in arg_regs.iter().take(8).enumerate() {
                args_array[i] = reg;
            }

            let params_index = self.program.add_function_call_params(
                crate::rvm::instructions::FunctionCallParams {
                    func_rule_index: rule_index,
                    dest,
                    num_args,
                    args: args_array,
                },
            );

            // Emit the FunctionCall instruction
            self.emit_instruction(Instruction::FunctionCall { params_index }, &span);
        } else if self.is_builtin(&original_fcn_path) {
            // Get builtin index
            let builtin_index = self.get_builtin_index(&original_fcn_path)?;

            // Create builtin call parameters with fixed-size array
            let mut args_array = [0u8; 8];
            let num_args = arg_regs.len().min(8) as u8; // Limit to 8 arguments
            for (i, &reg) in arg_regs.iter().take(8).enumerate() {
                args_array[i] = reg;
            }

            let params_index =
                self.program
                    .add_builtin_call_params(crate::rvm::instructions::BuiltinCallParams {
                        dest,
                        builtin_index,
                        num_args,
                        args: args_array,
                    });

            // Emit the BuiltinCall instruction
            self.emit_instruction(Instruction::BuiltinCall { params_index }, &span);
        } else {
            return Err(CompilerError::UnknownFunction {
                name: original_fcn_path.to_string(),
            });
        }

        Ok(dest)
    }

    /// Evaluate simple literal default rules and store results in literal table
    fn evaluate_default_rule(&mut self, rule_path: &str) -> Option<u16> {
        // Check if there are default rules for this path in the compiled policy
        if !self.policy.inner.default_rules.contains_key(rule_path) {
            return None;
        }

        // Create an interpreter to evaluate the default rule
        let mut interpreter = Interpreter::new_from_compiled_policy(self.policy.inner.clone());

        // Use the compiler-specific function to evaluate the default rule and get its value
        match interpreter.eval_default_rule_for_compiler(rule_path) {
            Ok(computed_value) => {
                if computed_value != Value::Undefined {
                    // Add the computed value to the literal table
                    let literal_index = self.add_literal(computed_value);
                    return Some(literal_index);
                }
            }
            Err(_e) => {}
        }

        None
    }

    /// Extract destructuring block entry points from the compiled patterns
    fn extract_destructuring_blocks(&self, rule_index: u16) -> Vec<Option<u32>> {
        self.rule_definition_destructuring_patterns[rule_index as usize].clone()
    }
}
