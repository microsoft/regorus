// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;
use alloc::vec::Vec;

use super::errors::{Result, VmError};
use super::execution_model::ExecutionState;
use super::machine::RegoVM;

impl RegoVM {
    /// Release values retained by the previous execution before capturing a new memory baseline.
    pub(super) fn reset_run_to_completion_state(&mut self) -> Result<()> {
        self.release_previous_execution_state();
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        if matches!(
            self.memory_budget_lifecycle,
            super::machine::MemoryBudgetLifecycle::FfiResultSerialization
        ) {
            // The internal FFI serialization window owns the baseline. Observe the
            // post-release trough before initialization so fresh state allocations are
            // charged to that execution.
            self.check_memory_budget()?;
        } else {
            self.reset_memory_budget_state();
        }
        self.initialize_execution_state();
        Ok(())
    }

    pub(super) fn release_previous_execution_state(&mut self) {
        self.evaluated = Value::Undefined;
        self.execution_state = ExecutionState::Ready;
        self.execution_stack.clear();
        self.return_to_pools();
        self.rule_cache.clear();
        self.registers.clear();
        self.builtins_cache.clear();
        self.cached_builtin_args.clear();
    }

    /// Release values retained by a failed run-to-completion execution and record its error.
    ///
    pub(super) fn fail_run_to_completion(&mut self, error: VmError) -> VmError {
        self.release_previous_execution_state();
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        {
            self.finish_active_memory_budget_execution();
        }
        self.execution_state = ExecutionState::Error {
            error: error.clone(),
        };
        error
    }

    /// Publish an initial suspendable execution error without discarding legacy unbudgeted state.
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) fn fail_initial_suspendable_execution(&mut self, error: VmError) -> VmError {
        if self.active_memory_budget_config.is_some() {
            return self.fail_suspendable_execution(error);
        }

        self.execution_state = ExecutionState::Error {
            error: error.clone(),
        };
        error
    }

    #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
    pub(super) fn fail_initial_suspendable_execution(&mut self, error: VmError) -> VmError {
        self.execution_state = ExecutionState::Error {
            error: error.clone(),
        };
        error
    }

    /// Release state after a failed budgeted suspendable execution.
    ///
    /// Unbudgeted executions preserve their legacy error state.
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    pub(super) fn fail_suspendable_execution(&mut self, error: VmError) -> VmError {
        if self.active_memory_budget_config.is_none() {
            return error;
        }

        self.release_previous_execution_state();
        self.finish_active_memory_budget_execution();
        self.execution_state = ExecutionState::Error {
            error: error.clone(),
        };
        error
    }

    #[cfg(any(miri, not(feature = "allocator-memory-limits")))]
    #[allow(clippy::unused_self)]
    pub(super) fn fail_suspendable_execution(&mut self, error: VmError) -> VmError {
        error
    }

    pub(super) fn initialize_execution_state(&mut self) {
        // Reset basic execution state
        self.executed_instructions = 0;
        self.pc = 0;
        self.evaluated = Value::new_object();
        self.cache_hits = 0;

        self.execution_state = ExecutionState::Ready;

        // Reset rule cache
        self.rule_cache = alloc::vec![(false, Value::Undefined); self.program.rule_infos.len()];

        // Reset registers to clean state
        self.registers
            .resize(self.base_register_count, Value::Undefined);

        // Postcondition: every stack/cache that `reset_execution_state` touches
        // must be in its documented "clean" shape. This catches accidental
        // omissions in future edits to this function.
        #[cfg(debug_assertions)]
        self.debug_assert_state_is_clean();
    }

    /// Debug-only postcondition for `reset_execution_state`.
    ///
    /// Asserts the invariants every caller of `reset_execution_state` relies on
    /// before starting a fresh execution. The body is fully gated by
    /// `#[cfg(debug_assertions)]` so this is a zero-cost no-op in release.
    #[inline]
    #[cfg(debug_assertions)]
    pub(super) fn debug_assert_state_is_clean(&self) {
        // --- Stacks: every per-execution stack must be drained. ---
        debug_assert!(
            self.execution_stack.is_empty(),
            "reset_execution_state postcondition: execution_stack must be empty"
        );
        debug_assert!(
            self.loop_stack.is_empty(),
            "reset_execution_state postcondition: loop_stack must be empty"
        );
        debug_assert!(
            self.comprehension_stack.is_empty(),
            "reset_execution_state postcondition: comprehension_stack must be empty"
        );
        debug_assert!(
            self.call_rule_stack.is_empty(),
            "reset_execution_state postcondition: call_rule_stack must be empty"
        );
        debug_assert!(
            self.register_stack.is_empty(),
            "reset_execution_state postcondition: register_stack must be empty"
        );

        // --- Caches: cleared so a new program/input cannot read stale entries. ---
        debug_assert!(
            self.builtins_cache.is_empty(),
            "reset_execution_state postcondition: builtins_cache must be empty"
        );

        // --- Registers: window resized to the program's base count and zeroed. ---
        debug_assert_eq!(
            self.registers.len(),
            self.base_register_count,
            "reset_execution_state postcondition: registers must be sized to base_register_count"
        );
        debug_assert!(
            self.registers.iter().all(|v| matches!(v, Value::Undefined)),
            "reset_execution_state postcondition: all registers must be Undefined"
        );

        // --- Rule cache: sized to the current program and marked uncomputed. ---
        debug_assert_eq!(
            self.rule_cache.len(),
            self.program.rule_infos.len(),
            "reset_execution_state postcondition: rule_cache size must match program rule_infos"
        );
        debug_assert!(
            self.rule_cache.iter().all(|entry| !entry.0),
            "reset_execution_state postcondition: rule_cache entries must be uncomputed"
        );

        // --- Counters and execution-state machine: zeroed and back to Ready. ---
        debug_assert_eq!(
            self.pc, 0,
            "reset_execution_state postcondition: pc must be 0"
        );
        debug_assert_eq!(
            self.executed_instructions, 0,
            "reset_execution_state postcondition: executed_instructions must be 0"
        );
        debug_assert!(
            matches!(self.execution_state, ExecutionState::Ready),
            "reset_execution_state postcondition: execution_state must be Ready"
        );
    }

    /// Per-opcode VM invariants checked from the inner dispatch loop.
    ///
    /// These hold every time control re-enters the dispatch loop with another
    /// instruction to execute. Only conditions that are *purely VM-internal*
    /// (i.e. cannot be made false by any host-supplied program or out-of-order
    /// API call) are asserted here — anything reachable from `load_program`
    /// input must surface as a typed `VmError` instead, to avoid panicking in
    /// debug builds and poisoning the engine across FFI.
    ///
    /// Fully `#[cfg(debug_assertions)]`-gated so the method body compiles out
    /// in release.
    #[inline]
    #[cfg(debug_assertions)]
    pub(super) fn assert_vm_invariants(&self) {
        // The dispatch loop only runs while execution is live. Once the VM
        // has transitioned to a terminal state (Suspended/Completed/Error)
        // the loop must have exited. Note `Ready` is also valid here because
        // some entry points (e.g. `execute_entry_point_by_index` in
        // RunToCompletion mode) drive `jump_to` without flipping the state.
        // `execution_state` is mutated only inside the VM and is not
        // host-controllable.
        debug_assert!(
            matches!(
                self.execution_state,
                ExecutionState::Ready | ExecutionState::Running
            ),
            "vm invariant: execution_state must be Ready or Running inside the dispatch loop, was {:?}",
            self.execution_state
        );

        // Rule cache is sized once at reset (against the currently loaded
        // program) and the VM does not resize it mid-execution. Any
        // mismatch here would indicate an internal accounting bug rather
        // than malformed input.
        debug_assert_eq!(
            self.rule_cache.len(),
            self.program.rule_infos.len(),
            "vm invariant: rule_cache size must equal program.rule_infos size"
        );

        // NOTE: `!registers.is_empty()` and an `execution_stack` depth
        // ceiling were intentionally *not* asserted here: both can be
        // triggered by a host-loaded program (registers via
        // `RuleInfo::num_registers == 0`; stack depth via deeply nested
        // rules/loops/comprehensions) and would therefore panic in debug
        // and poison the engine across FFI. Register access is already
        // guarded by `VmError::RegisterIndexOutOfBounds`; runaway recursion
        // is bounded in production by `set_max_instructions` and
        // `memory_check`.
    }

    /// Return all active objects to their respective pools for reuse
    pub(super) fn return_to_pools(&mut self) {
        // Clear stacks - these are small structs that don't need pooling
        self.loop_stack.clear();
        self.call_rule_stack.clear();
        self.comprehension_stack.clear();

        // Return register windows to pool for reuse
        while let Some(registers) = self.register_stack.pop() {
            self.return_register_window(registers);
        }
    }

    /// Get a register window from the pool or create a new one
    pub(super) fn new_register_window(&mut self) -> Vec<Value> {
        self.register_window_pool.pop().unwrap_or_default()
    }

    /// Return a register window to the pool for reuse
    pub(super) fn return_register_window(&mut self, mut window: Vec<Value>) {
        window.clear(); // Clear contents for reuse
        self.register_window_pool.push(window);
    }

    /// Validate VM state consistency for debugging
    pub(super) fn validate_vm_state(&self) -> Result<()> {
        // Check register bounds
        if self.registers.len() < self.base_register_count {
            return Err(VmError::RegisterCountBelowBase {
                register_count: self.registers.len(),
                base_count: self.base_register_count,
                pc: self.pc,
            });
        }

        // Check PC bounds
        if self.pc >= self.program.instructions.len() {
            return Err(VmError::ProgramCounterOutOfBounds {
                pc: self.pc,
                instruction_count: self.program.instructions.len(),
            });
        }

        // Check rule cache bounds
        if self.rule_cache.len() != self.program.rule_infos.len() {
            return Err(VmError::RuleCacheSizeMismatch {
                cache_size: self.rule_cache.len(),
                rule_info_count: self.program.rule_infos.len(),
                pc: self.pc,
            });
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    use super::super::machine::MemoryBudgetLifecycle;
    use super::{ExecutionState, RegoVM, Value, VmError};
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    use crate::rvm::program::{RuleInfo, RuleType};
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    use crate::rvm::{instructions::Instruction, program::Program};
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    use crate::MemoryBudgetConfig;
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    use alloc::sync::Arc;
    use alloc::vec;
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    use core::num::NonZeroU64;

    #[test]
    fn failed_run_to_completion_releases_retained_values() {
        let mut vm = RegoVM::new();
        let retained = Value::from("retained");
        vm.evaluated = retained.clone();
        vm.registers = vec![retained.clone()];
        vm.rule_cache = vec![(true, retained.clone())];
        vm.register_stack.push(vec![retained.clone()]);
        vm.cached_builtin_args = vec![retained.clone()];
        vm.execution_state = ExecutionState::Completed { result: retained };
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        {
            vm.memory_budget_lifecycle = MemoryBudgetLifecycle::ImplicitExecution;
        }

        let error = VmError::MemoryBudgetExceeded {
            usage: 2,
            budget: 1,
            pc: 3,
        };

        assert_eq!(vm.fail_run_to_completion(error.clone()), error);
        assert!(matches!(vm.evaluated, Value::Undefined));
        assert!(vm.registers.is_empty());
        assert!(vm.rule_cache.is_empty());
        assert!(vm.register_stack.is_empty());
        assert!(vm
            .register_window_pool
            .iter()
            .all(alloc::vec::Vec::is_empty));
        assert!(vm.cached_builtin_args.is_empty());
        assert_eq!(
            vm.execution_state,
            ExecutionState::Error {
                error: error.clone()
            }
        );
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        assert!(matches!(
            vm.memory_budget_lifecycle,
            MemoryBudgetLifecycle::Inactive
        ));
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    #[allow(clippy::expect_used)]
    #[test]
    fn successful_ordinary_executions_finish_their_implicit_memory_budget() {
        let mut program = Program::new();
        program.entry_points.insert("main".into(), 0);
        program.instructions = vec![Instruction::Return { value: 0 }];
        program.instruction_spans = vec![None];

        let mut vm = RegoVM::new();
        vm.load_program(Arc::new(program));
        vm.set_memory_budget_config(Some(MemoryBudgetConfig {
            limit: NonZeroU64::new(1024 * 1024).unwrap_or(NonZeroU64::MIN),
        }));

        assert_eq!(
            vm.execute().expect("main execution succeeds"),
            Value::Undefined
        );
        assert!(matches!(
            vm.memory_budget_lifecycle,
            MemoryBudgetLifecycle::Inactive
        ));

        assert_eq!(
            vm.execute_entry_point_by_name("main")
                .expect("named execution succeeds"),
            Value::Undefined
        );
        assert!(matches!(
            vm.memory_budget_lifecycle,
            MemoryBudgetLifecycle::Inactive
        ));

        assert_eq!(
            vm.execute_entry_point_by_index(0)
                .expect("indexed execution succeeds"),
            Value::Undefined
        );
        assert!(matches!(
            vm.memory_budget_lifecycle,
            MemoryBudgetLifecycle::Inactive
        ));
    }

    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    #[test]
    fn ffi_result_serialization_counts_fresh_initialization_after_releasing_previous_state() {
        let rule_info = RuleInfo::new(
            "unused".into(),
            RuleType::Complete,
            crate::Rc::new(alloc::vec![]),
            0,
            0,
        );
        let mut program = Program::new();
        program.dispatch_window_size = 1;
        program.max_rule_window_size = 1;
        program.entry_points.insert("main".into(), 0);
        program.rule_infos = alloc::vec![rule_info; Program::MAX_RULES];
        program.instructions = alloc::vec![Instruction::Return { value: 0 }];
        program.instruction_spans = alloc::vec![None];

        let mut vm = RegoVM::new();
        vm.load_program(Arc::new(program));
        // Model a reused VM whose completed result is released before fresh
        // execution-state allocation. The FFI window must observe that trough,
        // then charge the fresh rule-cache allocation.
        vm.rule_cache = alloc::vec![];
        let retained = Value::from(
            (0..(Program::MAX_RULES * 4))
                .map(Value::from)
                .collect::<alloc::vec::Vec<_>>(),
        );
        vm.evaluated = retained.clone();
        vm.execution_state = ExecutionState::Completed { result: retained };
        vm.set_memory_budget_config(Some(MemoryBudgetConfig {
            limit: NonZeroU64::new(32 * 1024).unwrap_or(NonZeroU64::MIN),
        }));

        assert!(matches!(
            vm.execute_to_c_string_for_ffi(),
            Err(VmError::MemoryBudgetExceeded { .. })
        ));
        assert!(matches!(
            vm.execution_state,
            ExecutionState::Error {
                error: VmError::MemoryBudgetExceeded { .. }
            }
        ));
    }
}
