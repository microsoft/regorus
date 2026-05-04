// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::program::Program;
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
use crate::utils::limits;
use crate::utils::limits::{
    fallback_execution_timer_config, monotonic_now, ExecutionTimer, ExecutionTimerConfig,
    LimitError,
};
use crate::value::Value;
use crate::CompiledPolicy;
use alloc::collections::{btree_map::Entry, BTreeMap, VecDeque};
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
            execution_timer_config: None,
            execution_timer: ExecutionTimer::new(fallback_timer),
            execution_timer_elapsed_at_suspend: None,
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
        self.execution_mode = mode;
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

    /// Get the current execution mode
    pub const fn get_execution_mode(&self) -> ExecutionMode {
        self.execution_mode
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
        limits::check_memory_limit_if_needed().map_err(|err| match err {
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
    }

    #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
    #[allow(clippy::unused_self, clippy::missing_const_for_fn)]
    pub(super) fn memory_check(&mut self) -> Result<()> {
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
