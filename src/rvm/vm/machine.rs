// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    missing_debug_implementations,
    clippy::missing_const_for_fn,
    clippy::pattern_type_mismatch
)] // VM structs are not debug printed

use crate::rvm::program::Program;
use crate::value::Value;
use crate::CompiledPolicy;
use alloc::collections::{btree_map::Entry, BTreeMap, VecDeque};
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use super::context::{CallRuleContext, ComprehensionContext, LoopContext};
use super::errors::{Result, VmError};
use super::execution_model::{
    BreakpointSet, ExecutionMode, ExecutionStack, ExecutionState, SuspendReason,
};

/// The Rego Virtual Machine
pub struct RegoVM {
    /// Registers for storing values during execution
    pub(super) registers: Vec<Value>,

    /// Program counter
    pub(super) pc: usize,

    /// The compiled program containing instructions, literals, and metadata
    pub(super) program: Arc<Program>,

    /// Reference to the compiled policy for default rule access
    pub(super) compiled_policy: Option<CompiledPolicy>,

    /// Rule execution cache: rule_index -> (computed: bool, result: Value)
    pub(super) rule_cache: Vec<(bool, Value)>,

    /// Global data object
    pub(super) data: Value,

    /// Global input object
    pub(super) input: Value,

    /// Loop execution stack
    /// Note: Loops are either at the outermost level (rule body) or within the topmost comprehension.
    /// Loops never contain comprehensions - it's always the other way around.
    pub(super) loop_stack: Vec<LoopContext>,

    /// Call rule execution stack for managing nested rule calls
    pub(super) call_rule_stack: Vec<CallRuleContext>,

    /// Register stack for isolated register spaces during rule calls
    pub(super) register_stack: Vec<Vec<Value>>,

    /// Comprehension execution stack for tracking active comprehensions
    /// Note: Comprehensions can be nested within each other, forming a proper nesting hierarchy.
    /// Any loops within a comprehension belong to the topmost (current) comprehension context.
    pub(super) comprehension_stack: Vec<ComprehensionContext>,

    /// Base register window size for the main execution context
    pub(super) base_register_count: usize,

    /// Object pools for performance optimization
    /// Pool of register windows for reuse during rule calls
    pub(super) register_window_pool: Vec<Vec<Value>>,

    /// Maximum number of instructions to execute (default: 25000)
    pub(super) max_instructions: usize,

    /// Current count of executed instructions
    pub(super) executed_instructions: usize,

    /// Cache for evaluated paths in virtual data document lookup
    /// Structure: evaluated[path_component1][path_component2]...[Undefined] = result_value
    pub(super) evaluated: Value,

    /// Counter for cache hits during virtual data document lookup evaluation
    pub(super) cache_hits: usize,

    /// Explicit execution stack used when running in suspendable mode
    pub(super) execution_stack: ExecutionStack,

    /// Current execution state of the VM
    pub(super) execution_state: ExecutionState,

    /// Active breakpoints for the suspendable engine
    pub(super) breakpoints: BreakpointSet,

    /// Flag indicating whether single-step mode is active
    pub(super) step_mode: bool,

    /// Preloaded responses for HostAwait in run-to-completion execution keyed by identifier
    pub(super) host_await_responses: BTreeMap<Value, VecDeque<Value>>,

    /// Current execution mode (run-to-completion vs suspendable)
    pub(super) execution_mode: ExecutionMode,

    /// Tracks whether the current top-of-stack frame PC was explicitly set by an instruction
    pub(super) frame_pc_overridden: bool,

    /// Whether builtins should raise errors strictly or return undefined on failure
    pub(super) strict_builtin_errors: bool,

    /// Cache for builtin calls that must stay deterministic across a single evaluation
    pub(super) builtins_cache: BTreeMap<(&'static str, Vec<Value>), Value>,
}

impl Default for RegoVM {
    fn default() -> Self {
        Self::new()
    }
}

impl RegoVM {
    /// Create a new virtual machine
    pub fn new() -> Self {
        RegoVM {
            registers: Vec::new(), // Start with no registers - will be resized when program is loaded
            pc: 0,
            program: Arc::new(Program::default()),
            compiled_policy: None,
            rule_cache: Vec::new(),
            data: Value::Null,
            input: Value::Null,
            loop_stack: Vec::new(),
            call_rule_stack: Vec::new(),
            register_stack: Vec::new(),
            comprehension_stack: Vec::new(),
            base_register_count: 2, // Default to 2 registers for basic operations
            register_window_pool: Vec::new(), // Initialize register window pool
            max_instructions: 25000, // Default maximum instruction limit
            executed_instructions: 0,
            evaluated: Value::new_object(), // Initialize evaluation cache
            cache_hits: 0,                  // Initialize cache hit counter
            execution_stack: ExecutionStack::new(),
            execution_state: ExecutionState::Ready,
            breakpoints: BreakpointSet::new(),
            step_mode: false,
            host_await_responses: BTreeMap::new(),
            execution_mode: ExecutionMode::RunToCompletion,
            frame_pc_overridden: false,
            strict_builtin_errors: false,
            builtins_cache: BTreeMap::new(),
        }
    }

    /// Create a new virtual machine with compiled policy for default rule support
    pub fn new_with_policy(compiled_policy: CompiledPolicy) -> Self {
        let mut vm = Self::new();
        vm.compiled_policy = Some(compiled_policy);
        vm
    }

    /// Load a complete program for execution
    pub fn load_program(&mut self, program: Arc<Program>) {
        self.program = program.clone();

        // Use the dispatch window size from the program for initial register allocation
        let dispatch_size = program.dispatch_window_size.max(2); // Ensure at least 2 registers
        self.base_register_count = dispatch_size;

        // Resize registers to match program requirements
        self.registers.clear();
        self.registers.resize(dispatch_size, Value::Undefined);

        // Initialize rule cache
        self.rule_cache = vec![(false, Value::Undefined); program.rule_infos.len()];

        // Set PC to main entry point
        self.pc = program.main_entry_point;
        self.executed_instructions = 0; // Reset instruction counter
    }

    /// Set the compiled policy for default rule evaluation
    pub fn set_compiled_policy(&mut self, compiled_policy: CompiledPolicy) {
        self.compiled_policy = Some(compiled_policy);
    }

    /// Set the maximum number of instructions that can be executed
    pub fn set_max_instructions(&mut self, max: usize) {
        self.max_instructions = max;
    }

    /// Set the base register count for the main execution context
    /// This determines how many registers are available in the root register window
    pub fn set_base_register_count(&mut self, count: usize) {
        self.base_register_count = count.max(1); // Ensure at least 1 register
        if !self.registers.is_empty() {
            self.registers
                .resize(self.base_register_count, Value::Undefined);
        }
    }

    /// Set the global data object
    pub fn set_data(&mut self, data: Value) -> Result<()> {
        // Check for conflicts between rule tree and data
        self.program.check_rule_data_conflicts(&data)?;

        self.data = data;
        Ok(())
    }

    /// Set the global input object
    pub fn set_input(&mut self, input: Value) {
        self.input = input;
    }

    /// Get the number of entry points available
    pub fn get_entry_point_count(&self) -> usize {
        self.program.entry_points.len()
    }

    /// Get all entry point names
    pub fn get_entry_point_names(&self) -> Vec<String> {
        self.program.entry_points.keys().cloned().collect()
    }

    // Public getters for visualization
    pub fn get_pc(&self) -> usize {
        self.pc
    }

    pub fn get_registers(&self) -> &Vec<Value> {
        &self.registers
    }

    pub fn get_program(&self) -> &Arc<Program> {
        &self.program
    }

    pub fn get_call_stack(&self) -> &Vec<CallRuleContext> {
        &self.call_rule_stack
    }

    pub fn get_loop_stack(&self) -> &Vec<LoopContext> {
        &self.loop_stack
    }

    pub fn get_cache_hits(&self) -> usize {
        self.cache_hits
    }

    /// Set the execution mode for the VM
    pub fn set_execution_mode(&mut self, mode: ExecutionMode) {
        self.execution_mode = mode;
    }

    /// Configure whether builtin operations should raise errors strictly
    pub fn set_strict_builtin_errors(&mut self, strict: bool) {
        self.strict_builtin_errors = strict;
    }

    /// Returns whether builtin operations raise errors strictly
    pub fn strict_builtin_errors(&self) -> bool {
        self.strict_builtin_errors
    }

    /// Enable or disable single-step execution for suspendable runs
    pub fn set_step_mode(&mut self, enabled: bool) {
        self.step_mode = enabled;
    }

    /// Configure the sequence of HostAwait responses for run-to-completion execution
    pub fn set_host_await_responses<I, J>(&mut self, responses: I)
    where
        I: IntoIterator<Item = (Value, J)>,
        J: IntoIterator<Item = Value>,
    {
        self.host_await_responses.clear();

        for (identifier, values) in responses {
            let mut queue = VecDeque::new();
            queue.extend(values);

            match self.host_await_responses.entry(identifier) {
                Entry::Vacant(entry) => {
                    entry.insert(queue);
                }
                Entry::Occupied(mut entry) => {
                    entry.get_mut().extend(queue);
                }
            }
        }
    }

    pub(super) fn next_host_await_response(
        &mut self,
        identifier: &Value,
        dest: u8,
    ) -> Result<Value> {
        let missing_error = || VmError::HostAwaitResponseMissing {
            dest,
            identifier: identifier.clone(),
        };

        let (response, should_remove) = {
            let queue = self
                .host_await_responses
                .get_mut(identifier)
                .ok_or_else(missing_error)?;

            let response = queue.pop_front().ok_or_else(missing_error)?;
            let should_remove = queue.is_empty();
            (response, should_remove)
        };

        if should_remove {
            self.host_await_responses.remove(identifier);
        }

        Ok(response)
    }

    /// Get the current execution mode
    pub fn get_execution_mode(&self) -> ExecutionMode {
        self.execution_mode
    }

    /// Get the current execution state of the VM
    pub fn execution_state(&self) -> &ExecutionState {
        &self.execution_state
    }

    /// Get the suspend reason if the VM is currently suspended
    pub fn suspend_reason(&self) -> Option<&SuspendReason> {
        match &self.execution_state {
            ExecutionState::Suspended { reason, .. } => Some(reason),
            _ => None,
        }
    }
}
