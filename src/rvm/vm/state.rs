// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;
use alloc::vec::Vec;

use super::errors::{Result, VmError};
use super::execution_model::ExecutionState;
use super::machine::RegoVM;

impl RegoVM {
    /// Reset all execution state and return objects to pools for reuse
    pub(super) fn reset_execution_state(&mut self) {
        // Reset basic execution state
        self.executed_instructions = 0;
        self.pc = 0;
        self.evaluated = Value::new_object();
        self.cache_hits = 0;

        // Reset suspendable execution state
        self.execution_stack.clear();
        self.execution_state = ExecutionState::Ready;

        // Return objects to pools and clear stacks
        self.return_to_pools();

        // Reset rule cache
        self.rule_cache = alloc::vec![(false, Value::Undefined); self.program.rule_infos.len()];

        // Reset registers to clean state
        self.registers.clear();
        self.registers
            .resize(self.base_register_count, Value::Undefined);

        // Builtin cache entries only live for a single execution
        self.builtins_cache.clear();

        // Postcondition: every stack/cache that `reset_execution_state` touches
        // must be in its documented "clean" shape. This catches accidental
        // omissions in future edits to this function.
        self.debug_assert_state_is_clean();
    }

    /// Debug-only postcondition for `reset_execution_state`.
    ///
    /// Asserts the invariants every caller of `reset_execution_state` relies on
    /// before starting a fresh execution. The body is fully gated by
    /// `#[cfg(debug_assertions)]` so this is a zero-cost no-op in release.
    #[inline]
    pub(super) fn debug_assert_state_is_clean(&self) {
        #[cfg(debug_assertions)]
        {
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
    pub(super) fn assert_vm_invariants(&self) {
        #[cfg(debug_assertions)]
        {
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
