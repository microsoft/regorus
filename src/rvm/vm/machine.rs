// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::program::Program;
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
use crate::utils::limits;
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
use crate::utils::limits::MemoryBudgetAccount;
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
use crate::utils::limits::MemoryBudgetConfig;
use crate::utils::limits::{
    fallback_execution_timer_config, monotonic_now, ExecutionTimer, ExecutionTimerConfig,
    LimitError,
};
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
use crate::value::ResumeJsonError;
use crate::value::Value;
use crate::CompiledPolicy;
use alloc::collections::{btree_map::Entry, BTreeMap, VecDeque};
use alloc::ffi::CString;
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
use alloc::format;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::time::Duration;

use super::context::{CallRuleContext, ComprehensionContext, LoopContext};
use super::errors::{Result, VmError};
use super::execution_model::{
    BreakpointSet, ExecutionMode, ExecutionStack, ExecutionState, SuspendReason,
};

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum MemoryBudgetLifecycle {
    Inactive,
    ImplicitExecution,
    FfiResultSerialization,
    SuspendableExecution,
}

/// The Rego Virtual Machine
#[derive(Debug)]
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

    /// Evaluation context: host-supplied ambient data available via LoadContext
    pub(super) context: Value,

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

    #[cfg(test)]
    pub(super) memory_check_count: usize,

    #[cfg(all(test, feature = "allocator-memory-limits", not(miri)))]
    last_memory_budget_usage_for_test: Option<u64>,

    #[cfg(all(test, feature = "allocator-memory-limits", not(miri)))]
    ffi_output_start_usage_for_test: Option<u64>,

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

    /// Execution mode selected for the next initial execution.
    pub(super) next_execution_mode: ExecutionMode,

    /// Tracks whether the current top-of-stack frame PC was explicitly set by an instruction
    pub(super) frame_pc_overridden: bool,

    /// Whether builtins should raise errors strictly or return undefined on failure
    pub(super) strict_builtin_errors: bool,

    /// Cache for builtin calls that must stay deterministic across a single evaluation.
    ///
    /// Two-level structure: outer BTreeMap keyed by builtin name, inner Vec of
    /// (args, result) pairs scanned linearly. This avoids allocating a composite
    /// key on every lookup (which a single-level BTreeMap<(name, Vec<Value>), Value>
    /// would require). Linear scan is fast for the small number of entries per
    /// builtin (typically <10). Can be revisited with a HashMap if `Value` gains
    /// a `Hash` implementation.
    pub(super) builtins_cache: BTreeMap<&'static str, Vec<(Vec<Value>, Value)>>,

    /// Optional override for the execution timer configuration
    pub(super) execution_timer_config: Option<ExecutionTimerConfig>,

    /// Cooperative execution timer used to enforce wall-clock limits
    pub(super) execution_timer: ExecutionTimer,

    /// Elapsed wall-clock time recorded when the VM entered a suspended state
    pub(super) execution_timer_elapsed_at_suspend: Option<Duration>,

    /// Optional budget selected for the next initial execution.
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) memory_budget_config: Option<MemoryBudgetConfig>,

    /// Budget snapshotted for the currently active execution.
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) active_memory_budget_config: Option<MemoryBudgetConfig>,

    /// Requested-byte account retained across suspendable execution segments.
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) suspendable_memory_budget_account: Option<MemoryBudgetAccount>,

    /// Current-thread live-byte baseline captured at execution start
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) memory_budget_baseline: i64,

    /// Owner of the current memory-budget baseline.
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) memory_budget_lifecycle: MemoryBudgetLifecycle,

    /// Keeps an FFI segment active through immediate native result serialization.
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) ffi_memory_budget_scope_active: bool,

    /// Cached dummy span for builtin calls (avoids Source::from_contents per call)
    pub(super) dummy_span: Option<crate::lexer::Span>,

    /// Cached dummy expressions for builtin calls (avoids Rc<Expr> allocs per call)
    pub(super) dummy_exprs: Vec<crate::ast::Ref<crate::ast::Expr>>,

    /// Cached args Vec for builtin calls (avoids Vec allocation per call)
    pub(super) cached_builtin_args: Vec<Value>,

    /// When `true`, a loop over a value that is not treated as a collection
    /// (null, strings, numbers, objects, and similar non-array values) uses
    /// Azure Policy-compatible semantics.  `Every` behaves as if iterating
    /// over a single virtual element whose value is `Null`, instead of being
    /// vacuously `true` over an empty collection.  This matches Azure Policy
    /// semantics where `field[*]` on a non-array value produces a single
    /// `Null` element (which typically causes the condition to evaluate to
    /// `false`).  Automatically set from `program.metadata.language`.
    pub(super) virtual_element_on_non_collection: bool,

    /// Cached `Value` representation of `program.metadata`, computed once in
    /// `load_program()` and reused by `LoadMetadata` instructions.
    pub(super) metadata_value: Value,
}

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
struct FfiResultSerializationBudget<'a> {
    vm: &'a mut RegoVM,
}

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
impl FfiResultSerializationBudget<'_> {
    const fn vm(&mut self) -> &mut RegoVM {
        self.vm
    }
}

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
impl Drop for FfiResultSerializationBudget<'_> {
    fn drop(&mut self) {
        self.vm.finish_ffi_result_serialization_memory_budget();
    }
}

impl Default for RegoVM {
    fn default() -> Self {
        Self::new()
    }
}

impl RegoVM {
    /// Create a new virtual machine
    pub fn new() -> Self {
        let fallback_timer = fallback_execution_timer_config();

        RegoVM {
            registers: Vec::new(), // Start with no registers - will be resized when program is loaded
            pc: 0,
            program: Arc::new(Program::default()),
            compiled_policy: None,
            rule_cache: Vec::new(),
            data: Value::Null,
            input: Value::Null,
            context: Value::Undefined,
            loop_stack: Vec::new(),
            call_rule_stack: Vec::new(),
            register_stack: Vec::new(),
            comprehension_stack: Vec::new(),
            base_register_count: 2, // Default to 2 registers for basic operations
            register_window_pool: Vec::new(), // Initialize register window pool
            max_instructions: 25000, // Default maximum instruction limit
            executed_instructions: 0,
            #[cfg(test)]
            memory_check_count: 0,
            #[cfg(all(test, feature = "allocator-memory-limits", not(miri)))]
            last_memory_budget_usage_for_test: None,
            #[cfg(all(test, feature = "allocator-memory-limits", not(miri)))]
            ffi_output_start_usage_for_test: None,
            evaluated: Value::new_object(), // Initialize evaluation cache
            cache_hits: 0,                  // Initialize cache hit counter
            execution_stack: ExecutionStack::new(),
            execution_state: ExecutionState::Ready,
            breakpoints: BreakpointSet::new(),
            step_mode: false,
            host_await_responses: BTreeMap::new(),
            execution_mode: ExecutionMode::RunToCompletion,
            next_execution_mode: ExecutionMode::RunToCompletion,
            frame_pc_overridden: false,
            strict_builtin_errors: false,
            builtins_cache: BTreeMap::new(),
            execution_timer_config: None,
            execution_timer: ExecutionTimer::new(fallback_timer),
            execution_timer_elapsed_at_suspend: None,
            #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
            memory_budget_config: None,
            #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
            active_memory_budget_config: None,
            #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
            suspendable_memory_budget_account: None,
            #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
            memory_budget_baseline: 0,
            #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
            memory_budget_lifecycle: MemoryBudgetLifecycle::Inactive,
            #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
            ffi_memory_budget_scope_active: false,
            dummy_span: None,
            dummy_exprs: Vec::new(),
            cached_builtin_args: Vec::new(),
            virtual_element_on_non_collection: false,
            metadata_value: Value::Undefined,
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
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        if matches!(
            self.memory_budget_lifecycle,
            MemoryBudgetLifecycle::SuspendableExecution
        ) {
            self.release_previous_execution_state();
            self.finish_active_memory_budget_execution();
        }

        self.program = program.clone();

        // Use the dispatch window size from the program for initial register allocation
        let dispatch_size = usize::from(program.dispatch_window_size).max(2); // Ensure at least 2 registers
        self.base_register_count = dispatch_size;

        // Resize registers to match program requirements
        self.registers.clear();
        self.registers.resize(dispatch_size, Value::Undefined);

        // Initialize rule cache
        self.rule_cache = vec![(false, Value::Undefined); program.rule_infos.len()];

        // Set PC to main entry point
        self.pc = usize::try_from(program.main_entry_point).unwrap_or(0);
        self.executed_instructions = 0; // Reset instruction counter

        // Azure Policy: loop over non-collection iterates a virtual Null element
        // (instead of vacuously succeeding over an empty collection).
        self.virtual_element_on_non_collection = program.metadata.language == "azure_policy";

        // Cache the metadata as a Value for LoadMetadata instructions
        self.metadata_value = program.metadata.to_value();
    }

    /// Set the compiled policy for default rule evaluation
    pub fn set_compiled_policy(&mut self, compiled_policy: CompiledPolicy) {
        self.compiled_policy = Some(compiled_policy);
    }

    /// Set the maximum number of instructions that can be executed
    pub const fn set_max_instructions(&mut self, max: usize) {
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

    /// Set the evaluation context (host-supplied ambient data)
    pub fn set_context(&mut self, context: Value) {
        self.context = context;
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
    pub const fn get_pc(&self) -> usize {
        self.pc
    }

    pub const fn get_registers(&self) -> &Vec<Value> {
        &self.registers
    }

    pub const fn get_program(&self) -> &Arc<Program> {
        &self.program
    }

    pub const fn get_call_stack(&self) -> &Vec<CallRuleContext> {
        &self.call_rule_stack
    }

    pub const fn get_loop_stack(&self) -> &Vec<LoopContext> {
        &self.loop_stack
    }

    pub const fn get_cache_hits(&self) -> usize {
        self.cache_hits
    }

    /// Set the execution mode for the VM
    pub const fn set_execution_mode(&mut self, mode: ExecutionMode) {
        self.next_execution_mode = mode;
    }

    /// Configure whether builtin operations should raise errors strictly
    pub const fn set_strict_builtin_errors(&mut self, strict: bool) {
        self.strict_builtin_errors = strict;
    }

    /// Returns whether builtin operations raise errors strictly
    pub const fn strict_builtin_errors(&self) -> bool {
        self.strict_builtin_errors
    }

    /// Enable or disable single-step execution for suspendable runs
    pub const fn set_step_mode(&mut self, enabled: bool) {
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
            pc: self.pc,
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

    /// Get the execution mode selected for the next initial execution.
    pub const fn get_execution_mode(&self) -> ExecutionMode {
        self.next_execution_mode
    }

    /// Configure the execution timer to use the supplied configuration, or fall back to the global
    /// default when `None` is provided.
    pub fn set_execution_timer_config(&mut self, config: Option<ExecutionTimerConfig>) {
        self.execution_timer_config = config;
        self.reset_execution_timer_state();
    }

    /// Returns the currently configured execution timer, if any.
    pub const fn execution_timer_config(&self) -> Option<ExecutionTimerConfig> {
        self.execution_timer_config
    }

    /// Configure a fresh memory budget for the next initial execution.
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    #[cfg_attr(docsrs, doc(cfg(feature = "allocator-memory-limits")))]
    pub const fn set_memory_budget_config(&mut self, config: Option<MemoryBudgetConfig>) {
        self.memory_budget_config = config;
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) fn begin_suspendable_memory_budget_execution(&mut self) {
        self.active_memory_budget_config = self.memory_budget_config;
        self.memory_budget_baseline = 0;
        self.suspendable_memory_budget_account = self
            .active_memory_budget_config
            .map(|_| MemoryBudgetAccount::new());
        self.memory_budget_lifecycle = if self.suspendable_memory_budget_account.is_some() {
            MemoryBudgetLifecycle::SuspendableExecution
        } else {
            MemoryBudgetLifecycle::Inactive
        };
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) fn reset_memory_budget_state(&mut self) {
        if matches!(
            self.memory_budget_lifecycle,
            MemoryBudgetLifecycle::FfiResultSerialization
        ) {
            return;
        }

        self.suspendable_memory_budget_account = None;
        self.active_memory_budget_config = self.memory_budget_config;
        self.memory_budget_baseline = if self.active_memory_budget_config.is_some() {
            limits::current_thread_live_bytes()
        } else {
            0
        };
        self.memory_budget_lifecycle = if self.ffi_memory_budget_scope_active {
            MemoryBudgetLifecycle::FfiResultSerialization
        } else if self.active_memory_budget_config.is_some() {
            MemoryBudgetLifecycle::ImplicitExecution
        } else {
            MemoryBudgetLifecycle::Inactive
        };
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) const fn finish_implicit_memory_budget_execution(&mut self) {
        if matches!(
            self.memory_budget_lifecycle,
            MemoryBudgetLifecycle::ImplicitExecution
        ) {
            self.memory_budget_baseline = 0;
            self.active_memory_budget_config = None;
            self.memory_budget_lifecycle = MemoryBudgetLifecycle::Inactive;
        }
    }

    #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
    #[allow(clippy::unused_self)]
    pub(super) const fn finish_implicit_memory_budget_execution(&mut self) {}

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    fn begin_ffi_result_serialization_memory_budget(&mut self) {
        self.ffi_memory_budget_scope_active = true;
        if matches!(
            self.memory_budget_lifecycle,
            MemoryBudgetLifecycle::SuspendableExecution
        ) || matches!(self.next_execution_mode, ExecutionMode::Suspendable)
        {
            return;
        }

        self.active_memory_budget_config = self.memory_budget_config;
        self.suspendable_memory_budget_account = None;
        self.memory_budget_baseline = if self.active_memory_budget_config.is_some() {
            limits::current_thread_live_bytes()
        } else {
            0
        };
        self.memory_budget_lifecycle = MemoryBudgetLifecycle::FfiResultSerialization;
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    fn finish_ffi_result_serialization_memory_budget(&mut self) {
        self.ffi_memory_budget_scope_active = false;
        if matches!(
            self.memory_budget_lifecycle,
            MemoryBudgetLifecycle::FfiResultSerialization
        ) || (matches!(
            self.memory_budget_lifecycle,
            MemoryBudgetLifecycle::SuspendableExecution
        ) && !matches!(self.execution_state, ExecutionState::Suspended { .. }))
        {
            self.finish_active_memory_budget_execution();
        }
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) fn finish_active_memory_budget_execution(&mut self) {
        self.memory_budget_baseline = 0;
        self.active_memory_budget_config = None;
        self.suspendable_memory_budget_account = None;
        self.memory_budget_lifecycle = MemoryBudgetLifecycle::Inactive;
    }

    /// Execute and serialize a main entry point for the native FFI.
    ///
    /// This is an internal binding hook, not a general-purpose budget scope. It starts the
    /// execution budget after data, input, context, and program loading have completed, then
    /// keeps that budget active only through immediate native JSON and C-string production.
    #[doc(hidden)]
    pub fn execute_to_c_string_for_ffi(&mut self) -> Result<CString> {
        self.execute_to_c_string_for_ffi_with(Self::execute)
    }

    /// Execute and serialize a named entry point for the native FFI.
    #[doc(hidden)]
    pub fn execute_entry_point_by_name_to_c_string_for_ffi(
        &mut self,
        name: &str,
    ) -> Result<CString> {
        self.execute_to_c_string_for_ffi_with(|vm| vm.execute_entry_point_by_name(name))
    }

    /// Execute and serialize an indexed entry point for the native FFI.
    #[doc(hidden)]
    pub fn execute_entry_point_by_index_to_c_string_for_ffi(
        &mut self,
        index: usize,
    ) -> Result<CString> {
        self.execute_to_c_string_for_ffi_with(|vm| vm.execute_entry_point_by_index(index))
    }

    /// Parse a native resume value, resume the VM, and serialize the result under one budget.
    #[doc(hidden)]
    pub fn resume_to_c_string_for_ffi<F>(&mut self, parse_resume_json: F) -> Result<CString>
    where
        F: FnOnce() -> Result<Option<String>>,
    {
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        {
            self.begin_ffi_result_serialization_memory_budget();
            let mut budget = FfiResultSerializationBudget { vm: self };
            let account = budget.vm().suspendable_memory_budget_account.clone();

            let process = || {
                let resume_json = match parse_resume_json() {
                    Ok(value) => value,
                    Err(error) => {
                        if let Err(budget_error) = budget.vm().check_memory_budget() {
                            return Err(budget.vm().fail_suspendable_execution(budget_error));
                        }
                        let error = budget.vm().apply_memory_budget_precedence(error);
                        if matches!(
                            error,
                            VmError::MemoryBudgetExceeded { .. }
                                | VmError::MemoryLimitExceeded { .. }
                        ) {
                            return Err(budget.vm().fail_suspendable_execution(error));
                        }
                        return Err(error);
                    }
                };
                let resume_value = match resume_json {
                    Some(json) => match Value::from_json_str_for_resume(&json) {
                        Ok(value) => Some(value),
                        Err(ResumeJsonError::Malformed(error)) => {
                            return Err(VmError::from(error));
                        }
                        Err(ResumeJsonError::Other(error)) => {
                            let error = VmError::from(error);
                            if let Err(budget_error) = budget.vm().check_memory_budget() {
                                return Err(budget.vm().fail_suspendable_execution(budget_error));
                            }
                            let error = budget.vm().apply_memory_budget_precedence(error);
                            if matches!(
                                error,
                                VmError::MemoryBudgetExceeded { .. }
                                    | VmError::MemoryLimitExceeded { .. }
                            ) {
                                return Err(budget.vm().fail_suspendable_execution(error));
                            }
                            return Err(error);
                        }
                    },
                    None => None,
                };

                let value = budget.vm().resume(resume_value)?;
                let output = (|| {
                    #[cfg(test)]
                    {
                        budget.vm().ffi_output_start_usage_for_test = budget
                            .vm()
                            .suspendable_memory_budget_account
                            .as_ref()
                            .map(|sampled_account| sampled_account.live_bytes());
                    }
                    let json = value.to_json_str().map_err(VmError::from)?;
                    let output = CString::new(json).map_err(|_| VmError::Internal {
                        message: String::from("RVM JSON result contained an interior NUL byte"),
                        pc: budget.vm().pc,
                    })?;
                    budget.vm().check_memory_budget()?;
                    Ok(output)
                })();

                match output {
                    Ok(output) => Ok(output),
                    Err(error) => {
                        let error = budget.vm().apply_memory_budget_precedence(error);
                        Err(budget.vm().fail_suspendable_execution(error))
                    }
                }
            };

            if let Some(account) = account.as_ref() {
                account.with_scope(process)
            } else {
                crate::utils::limits::without_memory_budget_scope(process)
            }
        }

        #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
        {
            crate::utils::limits::without_memory_budget_scope(|| {
                let resume_value = parse_resume_json()?
                    .map(|json| Value::from_json_str(&json).map_err(VmError::from))
                    .transpose()?;
                let value = self.resume(resume_value)?;
                let json = value.to_json_str().map_err(VmError::from)?;
                CString::new(json).map_err(|_| VmError::Internal {
                    message: String::from("RVM JSON result contained an interior NUL byte"),
                    pc: self.pc,
                })
            })
        }
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    fn execute_to_c_string_for_ffi_with<F>(&mut self, execute: F) -> Result<CString>
    where
        F: FnOnce(&mut Self) -> Result<Value>,
    {
        self.begin_ffi_result_serialization_memory_budget();
        let mut budget = FfiResultSerializationBudget { vm: self };
        let output = (|| {
            let value = execute(budget.vm())?;
            let account = budget.vm().suspendable_memory_budget_account.clone();
            let serialize = || {
                #[cfg(test)]
                {
                    budget.vm().ffi_output_start_usage_for_test =
                        account.as_ref().map(|account| account.live_bytes());
                }
                let json = value.to_json_str().map_err(VmError::from)?;
                let output = CString::new(json).map_err(|_| VmError::Internal {
                    message: String::from("RVM JSON result contained an interior NUL byte"),
                    pc: budget.vm().pc,
                })?;
                budget.vm().check_memory_budget()?;
                Ok(output)
            };
            if let Some(account) = account.as_ref() {
                account.with_scope(serialize)
            } else {
                crate::utils::limits::without_memory_budget_scope(serialize)
            }
        })();

        match output {
            Ok(output) => Ok(output),
            Err(error) => Err(budget.vm().fail_run_to_completion(error)),
        }
    }

    #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
    fn execute_to_c_string_for_ffi_with<F>(&mut self, execute: F) -> Result<CString>
    where
        F: FnOnce(&mut Self) -> Result<Value>,
    {
        let output = (|| {
            let value = execute(self)?;
            let json = value.to_json_str().map_err(VmError::from)?;
            CString::new(json).map_err(|_| VmError::Internal {
                message: String::from("RVM JSON result contained an interior NUL byte"),
                pc: self.pc,
            })
        })();

        match output {
            Ok(output) => Ok(output),
            Err(error) => Err(self.fail_run_to_completion(error)),
        }
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) const fn ensure_memory_budget_execution_mode() -> Result<()> {
        Ok(())
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) const fn ensure_memory_budget_resume_supported() -> Result<()> {
        Ok(())
    }

    #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
    pub(super) const fn ensure_memory_budget_execution_mode() -> Result<()> {
        Ok(())
    }

    #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
    pub(super) const fn ensure_memory_budget_resume_supported() -> Result<()> {
        Ok(())
    }

    /// Check the configured budget against the active execution baseline.
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) fn check_memory_budget(&mut self) -> Result<()> {
        let Some(config) = self.active_memory_budget_config else {
            return Ok(());
        };

        let usage = match self.memory_budget_lifecycle {
            MemoryBudgetLifecycle::Inactive => return Ok(()),
            MemoryBudgetLifecycle::SuspendableExecution => self
                .suspendable_memory_budget_account
                .as_ref()
                .ok_or_else(|| VmError::Internal {
                    message: String::from("active suspendable memory budget has no account"),
                    pc: self.pc,
                })?
                .live_bytes(),
            MemoryBudgetLifecycle::ImplicitExecution
            | MemoryBudgetLifecycle::FfiResultSerialization => {
                let current = limits::current_thread_live_bytes();
                self.memory_budget_baseline = self.memory_budget_baseline.min(current);
                current
                    .saturating_sub(self.memory_budget_baseline)
                    .unsigned_abs()
            }
        };
        #[cfg(test)]
        {
            self.last_memory_budget_usage_for_test = Some(usage);
        }
        let budget = config.limit.get();
        if usage > budget {
            return Err(VmError::MemoryBudgetExceeded {
                usage,
                budget,
                pc: self.pc,
            });
        }

        Ok(())
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) fn apply_memory_budget_precedence(&mut self, err: VmError) -> VmError {
        if matches!(err, VmError::MemoryLimitExceeded { .. }) {
            self.check_memory_budget().err().unwrap_or(err)
        } else {
            err
        }
    }

    #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
    #[allow(clippy::unused_self)]
    pub(super) const fn check_memory_budget(&mut self) -> Result<()> {
        Ok(())
    }

    #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
    #[allow(clippy::unused_self)]
    pub(super) fn apply_memory_budget_precedence(&mut self, err: VmError) -> VmError {
        err
    }

    pub(super) fn reset_execution_timer_state(&mut self) {
        let config = self.effective_execution_timer_config();
        self.execution_timer = ExecutionTimer::new(config);
        self.execution_timer_elapsed_at_suspend = None;

        if config.is_none() {
            return;
        }

        if let Some(now) = monotonic_now() {
            self.execution_timer.start(now);
        }
    }

    fn effective_execution_timer_config(&self) -> Option<ExecutionTimerConfig> {
        self.execution_timer_config
            .or_else(fallback_execution_timer_config)
    }

    pub(super) fn execution_timer_tick(&mut self, work_units: u32) -> Result<()> {
        if !self.execution_timer.accumulate(work_units) {
            return Ok(());
        }

        let Some(now) = monotonic_now() else {
            return Ok(());
        };

        self.execution_timer
            .check_now(now)
            .map_err(|err| match err {
                LimitError::TimeLimitExceeded { elapsed, limit } => VmError::TimeLimitExceeded {
                    elapsed,
                    limit,
                    pc: self.pc,
                },
                LimitError::MemoryLimitExceeded { usage, limit } => VmError::MemoryLimitExceeded {
                    usage,
                    limit,
                    pc: self.pc,
                },
                LimitError::RegexSizeLimitExceeded { limit } => {
                    VmError::RegexSizeLimitExceeded { limit, pc: self.pc }
                }
            })
    }

    pub(super) fn snapshot_execution_timer_on_suspend(&mut self) {
        if self.execution_timer.config().is_none() {
            self.execution_timer_elapsed_at_suspend = None;
            return;
        }

        let Some(now) = monotonic_now() else {
            self.execution_timer_elapsed_at_suspend = None;
            return;
        };

        self.execution_timer_elapsed_at_suspend = self.execution_timer.elapsed(now);
    }

    pub(super) fn restore_execution_timer_after_resume(&mut self) {
        if self.execution_timer.config().is_none() {
            self.execution_timer_elapsed_at_suspend = None;
            return;
        }

        let Some(elapsed) = self.execution_timer_elapsed_at_suspend.take() else {
            return;
        };

        let Some(now) = monotonic_now() else {
            return;
        };

        self.execution_timer.resume_from_elapsed(now, elapsed);
    }

    /// Get the current execution state of the VM
    pub const fn execution_state(&self) -> &ExecutionState {
        &self.execution_state
    }

    /// Get the suspend reason if the VM is currently suspended
    pub const fn suspend_reason(&self) -> Option<&SuspendReason> {
        match self.execution_state {
            ExecutionState::Suspended { ref reason, .. } => Some(reason),
            _ => None,
        }
    }

    /// Get the HostAwait argument if the VM is suspended due to a HostAwait instruction.
    /// Returns `None` if the VM is not in a HostAwait-suspended state.
    pub const fn get_host_await_argument(&self) -> Option<&Value> {
        match self.execution_state {
            ExecutionState::Suspended {
                reason: SuspendReason::HostAwait { ref argument, .. },
                ..
            } => Some(argument),
            _ => None,
        }
    }

    /// Get the HostAwait identifier if the VM is suspended due to a HostAwait instruction.
    /// Returns `None` if the VM is not in a HostAwait-suspended state.
    pub const fn get_host_await_identifier(&self) -> Option<&Value> {
        match self.execution_state {
            ExecutionState::Suspended {
                reason: SuspendReason::HostAwait { ref identifier, .. },
                ..
            } => Some(identifier),
            _ => None,
        }
    }

    #[inline]
    #[allow(dead_code)]
    pub(super) fn get_register(&self, index: u8) -> Result<&Value> {
        self.registers
            .get(usize::from(index))
            .ok_or(VmError::RegisterIndexOutOfBounds {
                index,
                pc: self.pc,
                register_count: self.registers.len(),
            })
    }

    /// Take ownership of a register value, replacing it with `Value::Undefined`.
    /// This avoids bumping the Rc refcount that a clone would cause, keeping the
    /// refcount at 1 so that subsequent `Rc::make_mut` calls can mutate in place.
    #[inline]
    #[allow(dead_code)]
    pub(super) fn take_register(&mut self, index: u8) -> Result<Value> {
        let register_count = self.registers.len();

        let slot = self.registers.get_mut(usize::from(index)).ok_or(
            VmError::RegisterIndexOutOfBounds {
                index,
                pc: self.pc,
                register_count,
            },
        )?;
        Ok(core::mem::replace(slot, Value::Undefined))
    }

    #[inline]
    #[allow(dead_code)]
    pub(super) fn set_register(&mut self, index: u8, value: Value) -> Result<()> {
        let register_count = self.registers.len();

        let slot = self.registers.get_mut(usize::from(index)).ok_or(
            VmError::RegisterIndexOutOfBounds {
                index,
                pc: self.pc,
                register_count,
            },
        )?;
        *slot = value;
        Ok(())
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) fn memory_check(&mut self) -> Result<()> {
        #[cfg(test)]
        {
            self.memory_check_count = self.memory_check_count.saturating_add(1);
        }
        self.check_memory_budget()?;
        limits::check_memory_limit_if_needed()
            .map_err(|err| match err {
                LimitError::MemoryLimitExceeded { usage, limit } => VmError::MemoryLimitExceeded {
                    usage,
                    limit,
                    pc: self.pc,
                },
                other => VmError::Internal {
                    message: format!("unexpected limit error: {other}"),
                    pc: self.pc,
                },
            })
            .map_err(|err| self.apply_memory_budget_precedence(err))
    }

    #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
    #[allow(clippy::unused_self, clippy::missing_const_for_fn)]
    pub(super) fn memory_check(&mut self) -> Result<()> {
        #[cfg(test)]
        {
            self.memory_check_count = self.memory_check_count.saturating_add(1);
        }
        Ok(())
    }

    /// Get or create the cached dummy span for builtin calls.
    pub(super) fn get_dummy_span(&mut self) -> Result<&crate::lexer::Span> {
        if self.dummy_span.is_none() {
            let source = crate::lexer::Source::from_contents("<builtin>".into(), String::new())
                .map_err(|e| VmError::Internal {
                    message: alloc::format!("failed to create dummy source: {e}"),
                    pc: self.pc,
                })?;
            self.dummy_span = Some(crate::lexer::Span {
                source,
                line: 1,
                col: 1,
                start: 0,
                end: 0,
            });
        }
        // SAFETY: we just ensured it's Some above
        self.dummy_span.as_ref().ok_or(VmError::Internal {
            message: String::from("dummy span not initialized"),
            pc: self.pc,
        })
    }

    /// Ensure the cached dummy_exprs vec has at least `count` elements.
    pub(super) fn ensure_dummy_exprs(&mut self, count: usize) -> Result<()> {
        if self.dummy_exprs.len() >= count {
            return Ok(());
        }
        let span = self.get_dummy_span()?.clone();
        while self.dummy_exprs.len() < count {
            self.dummy_exprs
                .push(crate::ast::Ref::new(crate::ast::Expr::Null {
                    span: span.clone(),
                    value: Value::Null,
                    eidx: 0,
                }));
        }
        Ok(())
    }
}

#[cfg(all(test, feature = "allocator-memory-limits", not(miri)))]
mod memory_budget_tests {
    use super::RegoVM;
    use super::VmError;
    use crate::languages::rego::compiler::Compiler;
    use crate::rvm::vm::ExecutionMode;
    use crate::MemoryBudgetConfig;
    use crate::{Engine, Rc, Value};
    use alloc::ffi::CString;
    use alloc::string::String;
    use alloc::sync::Arc;
    use alloc::vec;
    use core::num::NonZeroU64;

    const NATIVE_RESUME_OUTPUT_BYTES: usize = 128 * 1024;
    const NATIVE_OUTPUT_TEST_CAP_BYTES: u64 = 1024 * 1024;
    const NATIVE_RESUME_OUTPUT_POLICY: &str = r#"
package limit
import rego.v1

result := sprintf("%s%s", [
    __builtin_host_await(input.value, "first"),
    data.limit.large_text
])
"#;

    fn native_resume_output_vm(
        program: &Arc<crate::rvm::program::Program>,
        data: &Value,
        budget: u64,
    ) -> anyhow::Result<RegoVM> {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_input(Value::from_json_str(r#"{"value":"request"}"#)?);
        vm.set_memory_budget_config(Some(MemoryBudgetConfig {
            limit: NonZeroU64::new(budget).unwrap_or(NonZeroU64::MIN),
        }));
        Ok(vm)
    }

    fn compile_native_resume_output_fixture(
    ) -> anyhow::Result<(Arc<crate::rvm::program::Program>, Value)> {
        let data_json = alloc::format!(
            r#"{{"limit":{{"large_text":"{}"}}}}"#,
            "x".repeat(NATIVE_RESUME_OUTPUT_BYTES)
        );
        let data = Value::from_json_str(&data_json)?;

        let mut engine = Engine::new();
        engine.add_policy(
            "memory_budget.rego".into(),
            NATIVE_RESUME_OUTPUT_POLICY.into(),
        )?;
        let entry_point = Rc::from("data.limit.result");
        let compiled = engine.compile_with_entrypoint(&entry_point)?;
        let program = Compiler::compile_from_policy(&compiled, &[entry_point.as_ref()])?;

        Ok((program, data))
    }

    fn resume_to_large_native_output(
        mut vm: RegoVM,
    ) -> anyhow::Result<(RegoVM, core::result::Result<CString, VmError>)> {
        let initial = vm.execute_entry_point_by_name_to_c_string_for_ffi("data.limit.result")?;
        anyhow::ensure!(initial.as_bytes_with_nul() == b"\"<undefined>\"\0");
        anyhow::ensure!(matches!(
            vm.execution_state,
            super::super::execution_model::ExecutionState::Suspended { .. }
        ));

        let response = String::from("\"ok\"");
        let output = vm.resume_to_c_string_for_ffi(move || Ok(Some(response)));
        Ok((vm, output))
    }

    #[allow(clippy::expect_used)]
    #[test]
    fn native_resume_output_allows_exact_budget_and_rejects_one_byte_over() -> anyhow::Result<()> {
        let (program, data) = compile_native_resume_output_fixture()?;
        let vm = native_resume_output_vm(&program, &data, NATIVE_OUTPUT_TEST_CAP_BYTES)?;
        let (vm, output) = resume_to_large_native_output(vm)?;
        let output = output.expect("budgeted native resume output succeeds");
        anyhow::ensure!(output.as_bytes().len() == NATIVE_RESUME_OUTPUT_BYTES.saturating_add(4));
        let expected_output = output.as_bytes().to_vec();
        let sampled_usage = vm
            .last_memory_budget_usage_for_test
            .expect("final native output check should record its live usage");
        anyhow::ensure!(sampled_usage >= u64::try_from(NATIVE_RESUME_OUTPUT_BYTES)?);
        anyhow::ensure!(sampled_usage <= NATIVE_OUTPUT_TEST_CAP_BYTES);
        std::println!(
            "native_resume_final_output_check_usage={sampled_usage}; output_json_bytes={}",
            output.as_bytes().len()
        );

        let exact_vm = native_resume_output_vm(&program, &data, sampled_usage)?;
        let (exact_vm, exact_output) = resume_to_large_native_output(exact_vm)?;
        let exact_output = exact_output.expect("usage equal to budget succeeds");
        anyhow::ensure!(exact_output.as_bytes() == expected_output);
        anyhow::ensure!(
            exact_vm.last_memory_budget_usage_for_test == Some(sampled_usage)
        );

        let one_byte_over_budget = sampled_usage
            .checked_sub(1)
            .expect("fixture usage must exceed zero");
        anyhow::ensure!(sampled_usage == one_byte_over_budget.saturating_add(1));
        let over_budget_vm = native_resume_output_vm(&program, &data, one_byte_over_budget)?;
        let (mut over_budget_vm, over_budget_output) =
            resume_to_large_native_output(over_budget_vm)?;
        anyhow::ensure!(matches!(
            over_budget_output,
            Err(VmError::MemoryBudgetExceeded { usage, budget, .. })
                if usage == sampled_usage && budget == one_byte_over_budget
        ));
        anyhow::ensure!(matches!(
            &over_budget_vm.execution_state,
            super::super::execution_model::ExecutionState::Error {
                error: VmError::MemoryBudgetExceeded { usage, budget, .. }
            } if *usage == sampled_usage && *budget == one_byte_over_budget
        ));
        anyhow::ensure!(over_budget_vm.execution_stack.is_empty());
        anyhow::ensure!(over_budget_vm.host_await_responses.is_empty());
        anyhow::ensure!(over_budget_vm.suspendable_memory_budget_account.is_none());
        anyhow::ensure!(matches!(
            over_budget_vm.memory_budget_lifecycle,
            super::MemoryBudgetLifecycle::Inactive
        ));
        anyhow::ensure!(!matches!(
            &over_budget_vm.execution_state,
            super::super::execution_model::ExecutionState::Completed { .. }
        ));

        let further_resume =
            over_budget_vm.resume_to_c_string_for_ffi(|| Ok(Some(String::from("\"retry\""))));
        further_resume
            .err()
            .ok_or_else(|| anyhow::anyhow!("further resume unexpectedly succeeded"))?;
        anyhow::ensure!(matches!(
            &over_budget_vm.execution_state,
            super::super::execution_model::ExecutionState::Error { .. }
        ));

        let plus_one_vm =
            native_resume_output_vm(&program, &data, sampled_usage.saturating_add(1))?;
        let (_, plus_one_output) = resume_to_large_native_output(plus_one_vm)?;
        anyhow::ensure!(
            plus_one_output
                .expect("budget one byte above usage succeeds")
                .as_bytes()
                == expected_output
        );
        Ok(())
    }

    #[allow(clippy::expect_used)]
    #[test]
    fn large_native_resume_output_fails_at_the_final_check_and_allows_reuse() -> anyhow::Result<()>
    {
        let (program, data) = compile_native_resume_output_fixture()?;
        let calibration_vm =
            native_resume_output_vm(&program, &data, NATIVE_OUTPUT_TEST_CAP_BYTES)?;
        let (calibration_vm, calibration_output) = resume_to_large_native_output(calibration_vm)?;
        calibration_output.expect("calibration output succeeds under large cap");
        let output_start_usage = calibration_vm
            .ffi_output_start_usage_for_test
            .expect("resume records live usage before native output construction");
        let final_usage = calibration_vm
            .last_memory_budget_usage_for_test
            .expect("calibration records final native output check usage");
        anyhow::ensure!(output_start_usage < final_usage);

        let mut vm = native_resume_output_vm(&program, &data, output_start_usage)?;
        let initial = vm
            .execute_entry_point_by_name_to_c_string_for_ffi("data.limit.result")
            .expect("initial HostAwait output");
        anyhow::ensure!(initial.as_bytes_with_nul() == b"\"<undefined>\"\0");
        anyhow::ensure!(matches!(
            vm.execution_state,
            super::super::execution_model::ExecutionState::Suspended { .. }
        ));
        let before_resume_usage = vm
            .suspendable_memory_budget_account
            .as_ref()
            .expect("suspended execution has an account")
            .live_bytes();
        anyhow::ensure!(before_resume_usage < output_start_usage);

        let response = String::from("\"ok\"");
        let error = vm
            .resume_to_c_string_for_ffi(move || Ok(Some(response)))
            .expect_err("native JSON and C-string production exceeds the cap");
        let observed_output_start = vm
            .ffi_output_start_usage_for_test
            .expect("native output stage was reached");
        let sampled_usage = vm
            .last_memory_budget_usage_for_test
            .expect("final output check should record live usage");
        anyhow::ensure!(observed_output_start == output_start_usage);
        anyhow::ensure!(sampled_usage > output_start_usage);
        anyhow::ensure!(matches!(
            error,
            VmError::MemoryBudgetExceeded { usage, budget, .. }
                if usage == sampled_usage && budget == output_start_usage
        ));
        anyhow::ensure!(matches!(
            &vm.execution_state,
            super::super::execution_model::ExecutionState::Error {
                error: VmError::MemoryBudgetExceeded { usage, budget, .. }
            } if *usage == sampled_usage && *budget == output_start_usage
        ));
        anyhow::ensure!(vm.execution_stack.is_empty());
        anyhow::ensure!(vm.host_await_responses.is_empty());
        anyhow::ensure!(vm.suspendable_memory_budget_account.is_none());
        anyhow::ensure!(matches!(
            vm.memory_budget_lifecycle,
            super::MemoryBudgetLifecycle::Inactive
        ));
        let further_resume = vm.resume_to_c_string_for_ffi(|| Ok(Some(String::from("\"retry\""))));
        further_resume
            .err()
            .ok_or_else(|| anyhow::anyhow!("further resume unexpectedly succeeded"))?;
        anyhow::ensure!(matches!(
            &vm.execution_state,
            super::super::execution_model::ExecutionState::Error { .. }
        ));

        vm.set_memory_budget_config(Some(MemoryBudgetConfig {
            limit: NonZeroU64::new(NATIVE_OUTPUT_TEST_CAP_BYTES).unwrap_or(NonZeroU64::MIN),
        }));
        let (_, reused_output) = resume_to_large_native_output(vm)?;
        anyhow::ensure!(
            reused_output
                .expect("independent execution completes under its own budget")
                .as_bytes()
                .len()
                == NATIVE_RESUME_OUTPUT_BYTES.saturating_add(4)
        );
        Ok(())
    }

    #[allow(clippy::expect_used)]
    #[test]
    fn one_byte_native_resume_budget_fails_and_terminalizes() -> anyhow::Result<()> {
        let (program, data) = compile_native_resume_output_fixture()?;
        let mut vm = native_resume_output_vm(&program, &data, 1)?;
        let error = vm
            .execute_entry_point_by_name_to_c_string_for_ffi("data.limit.result")
            .expect_err("one-byte budget must not reach a valid HostAwait continuation");
        anyhow::ensure!(matches!(error, VmError::MemoryBudgetExceeded { .. }));
        anyhow::ensure!(matches!(
            &vm.execution_state,
            super::super::execution_model::ExecutionState::Error {
                error: VmError::MemoryBudgetExceeded { .. }
            }
        ));
        anyhow::ensure!(vm.execution_stack.is_empty());
        anyhow::ensure!(vm.host_await_responses.is_empty());
        anyhow::ensure!(vm.suspendable_memory_budget_account.is_none());
        anyhow::ensure!(matches!(
            vm.memory_budget_lifecycle,
            super::MemoryBudgetLifecycle::Inactive
        ));
        Ok(())
    }

    #[test]
    fn foreign_free_observed_before_allocation_does_not_grant_budget_credit() -> anyhow::Result<()>
    {
        const FOREIGN_ALLOCATION_BYTES: usize = 512 * 1024;
        const LOCAL_ALLOCATION_BYTES: usize = 256 * 1024;
        const BUDGET_BYTES: u64 = 128 * 1024;

        let foreign_allocation =
            std::thread::spawn(|| vec![0_u8; FOREIGN_ALLOCATION_BYTES].into_boxed_slice())
                .join()
                .map_err(|_| anyhow::anyhow!("allocation thread panicked"))?;

        let mut vm = RegoVM::new();
        vm.set_memory_budget_config(Some(MemoryBudgetConfig {
            limit: NonZeroU64::new(BUDGET_BYTES).unwrap_or(NonZeroU64::MIN),
        }));
        vm.reset_memory_budget_state();

        drop(foreign_allocation);
        vm.check_memory_budget()?;

        let local_allocation = vec![0_u8; LOCAL_ALLOCATION_BYTES];
        core::hint::black_box(&local_allocation);

        match vm.check_memory_budget() {
            Err(VmError::MemoryBudgetExceeded { .. }) => Ok(()),
            Err(err) => Err(anyhow::anyhow!("unexpected memory budget error: {err}")),
            Ok(()) => Err(anyhow::anyhow!("expected memory budget exhaustion")),
        }
    }

    #[test]
    fn memory_budget_error_takes_precedence_over_global_limit_error() {
        const ALLOCATION_BYTES: usize = 256 * 1024;
        const ALLOCATION_BYTES_U64: u64 = 256 * 1024;
        const BUDGET_BYTES: u64 = 128 * 1024;

        let mut vm = RegoVM::new();
        vm.set_memory_budget_config(Some(MemoryBudgetConfig {
            limit: NonZeroU64::new(BUDGET_BYTES).unwrap_or(NonZeroU64::MIN),
        }));
        vm.reset_memory_budget_state();

        let allocation = vec![0_u8; ALLOCATION_BYTES];
        core::hint::black_box(&allocation);

        assert!(matches!(
            vm.apply_memory_budget_precedence(VmError::MemoryLimitExceeded {
                usage: ALLOCATION_BYTES_U64,
                limit: BUDGET_BYTES,
                pc: 0,
            }),
            VmError::MemoryBudgetExceeded { .. }
        ));
    }

    #[allow(clippy::expect_used)]
    #[test]
    fn ffi_result_serialization_window_cleans_up_on_terminal_paths() {
        let mut program = crate::rvm::program::Program::new();
        program.entry_points.insert("main".into(), 0);
        program.instructions =
            alloc::vec![crate::rvm::instructions::Instruction::Return { value: 0 }];
        program.instruction_spans = alloc::vec![None];

        let mut vm = RegoVM::new();
        vm.load_program(alloc::sync::Arc::new(program));
        vm.set_memory_budget_config(Some(MemoryBudgetConfig {
            limit: NonZeroU64::new(1024 * 1024).unwrap_or(NonZeroU64::MIN),
        }));

        assert_eq!(
            vm.execute_to_c_string_for_ffi()
                .expect("main FFI serialization succeeds")
                .as_bytes_with_nul(),
            b"\"<undefined>\"\0"
        );
        assert_eq!(
            vm.execute_entry_point_by_name_to_c_string_for_ffi("main")
                .expect("named FFI serialization succeeds")
                .as_bytes_with_nul(),
            b"\"<undefined>\"\0"
        );
        assert_eq!(
            vm.execute_entry_point_by_index_to_c_string_for_ffi(0)
                .expect("indexed FFI serialization succeeds")
                .as_bytes_with_nul(),
            b"\"<undefined>\"\0"
        );
        assert!(matches!(
            vm.memory_budget_lifecycle,
            super::MemoryBudgetLifecycle::Inactive
        ));

        vm.set_max_instructions(0);
        assert!(matches!(
            vm.execute_to_c_string_for_ffi(),
            Err(VmError::InstructionLimitExceeded { .. })
        ));
        assert!(matches!(
            vm.execution_state,
            super::super::execution_model::ExecutionState::Error {
                error: VmError::InstructionLimitExceeded { .. }
            }
        ));
        assert!(matches!(
            vm.memory_budget_lifecycle,
            super::MemoryBudgetLifecycle::Inactive
        ));
    }

    #[allow(clippy::panic)]
    #[test]
    fn ffi_result_serialization_window_deactivates_during_unwind() {
        let mut vm = RegoVM::new();
        vm.set_memory_budget_config(Some(MemoryBudgetConfig {
            limit: NonZeroU64::new(1024 * 1024).unwrap_or(NonZeroU64::MIN),
        }));

        let unwind = std::panic::catch_unwind(core::panic::AssertUnwindSafe(|| {
            vm.begin_ffi_result_serialization_memory_budget();
            let _budget = super::FfiResultSerializationBudget { vm: &mut vm };
            panic!("FFI serialization cleanup regression");
        }));

        assert!(unwind.is_err());
        assert!(matches!(
            vm.memory_budget_lifecycle,
            super::MemoryBudgetLifecycle::Inactive
        ));
    }
}
