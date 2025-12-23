#![allow(
    missing_debug_implementations,
    clippy::missing_const_for_fn,
    clippy::option_if_let_else,
    clippy::if_then_some_else_none,
    clippy::unused_self
)] // compiler internals do not require Debug

mod comprehensions;
mod core;
mod destructuring;
mod error;
mod expressions;
mod function_calls;
mod loops;
mod program;
mod queries;
mod references;
mod rules;

pub use error::{CompilerError, Result, SpannedCompilerError};

use crate::ast::ExprRef;
use crate::lexer::Span;
use crate::rvm::program::{Program, RuleType, SpanInfo};
use crate::CompiledPolicy;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use indexmap::IndexMap;

pub type Register = u8;

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
    pub(super) context_type: ContextType,
    pub(super) dest_register: Register,
    pub(super) key_expr: Option<ExprRef>,
    pub(super) value_expr: Option<ExprRef>,
    pub(super) span: Span,
    pub(super) key_value_loops_hoisted: bool,
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
    program: Program,
    spans: Vec<SpanInfo>,
    register_counter: Register,
    scopes: Vec<Scope>,
    policy: &'a CompiledPolicy,
    current_package: String,
    current_module_index: u32,
    rule_index_map: BTreeMap<String, u16>,
    rule_worklist: Vec<WorklistEntry>,
    rule_definitions: Vec<Vec<Vec<u32>>>,
    rule_definition_function_params: Vec<Vec<Option<Vec<String>>>>,
    rule_definition_destructuring_patterns: Vec<Vec<Option<u32>>>,
    rule_types: Vec<RuleType>,
    rule_function_param_count: Vec<Option<usize>>,
    rule_result_registers: Vec<u8>,
    rule_num_registers: Vec<u8>,
    context_stack: Vec<CompilationContext>,
    loop_expr_register_map: BTreeMap<ExprRef, Register>,
    source_to_index: BTreeMap<String, usize>,
    builtin_index_map: BTreeMap<String, u16>,
    current_input_register: Option<Register>,
    current_data_register: Option<Register>,
    current_rule_path: String,
    current_call_stack: Vec<u16>,
    entry_points: IndexMap<String, usize>,
    soft_assert_mode: bool,
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
            current_package: String::new(),
            current_module_index: 0,
            rule_index_map: BTreeMap::new(),
            rule_worklist: Vec::new(),
            rule_definitions: Vec::new(),
            rule_definition_function_params: Vec::new(),
            rule_definition_destructuring_patterns: Vec::new(),
            rule_types: Vec::new(),
            rule_function_param_count: Vec::new(),
            rule_result_registers: Vec::new(),
            rule_num_registers: Vec::new(),
            context_stack: vec![],
            loop_expr_register_map: BTreeMap::new(),
            source_to_index: BTreeMap::new(),
            builtin_index_map: BTreeMap::new(),
            current_input_register: None,
            current_data_register: None,
            current_rule_path: String::new(),
            current_call_stack: Vec::new(),
            entry_points: IndexMap::new(),
            soft_assert_mode: false,
        }
    }

    pub(super) fn with_soft_assert_mode<F, R>(&mut self, enabled: bool, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let previous = self.soft_assert_mode;
        self.soft_assert_mode = enabled;
        let result = f(self);
        self.soft_assert_mode = previous;
        result
    }
}
