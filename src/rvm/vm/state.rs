// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;
use alloc::string::String;
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
            return Err(VmError::Internal(alloc::format!(
                "Register count {} < base count {}",
                self.registers.len(),
                self.base_register_count
            )));
        }

        // Check PC bounds
        if self.pc >= self.program.instructions.len() {
            return Err(VmError::Internal(alloc::format!(
                "PC {} >= instruction count {}",
                self.pc,
                self.program.instructions.len()
            )));
        }

        // Check rule cache bounds
        if self.rule_cache.len() != self.program.rule_infos.len() {
            return Err(VmError::Internal(alloc::format!(
                "Rule cache size {} != rule info count {}",
                self.rule_cache.len(),
                self.program.rule_infos.len()
            )));
        }

        Ok(())
    }

    /// Get current VM state for debugging
    pub(super) fn get_debug_state(&self) -> String {
        alloc::format!(
            "VM State: PC={}, registers={}, executed={}/{}, stacks: loop={}, call={}, register={}, comprehension={}",
            self.pc,
            self.registers.len(),
            self.executed_instructions,
            self.max_instructions,
            self.loop_stack.len(),
            self.call_rule_stack.len(),
            self.register_stack.len(),
            self.comprehension_stack.len()
        )
    }
}
