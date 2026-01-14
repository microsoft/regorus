// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::program::RuleType;
use crate::value::Value;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use super::context::{ComprehensionContext, LoopContext};
use super::errors::VmError;

/// Represents a single execution context (frame) in the VM
#[derive(Debug, Clone)]
pub(super) struct ExecutionFrame {
    /// Program counter for this frame
    pub(super) pc: usize,
    /// Frame-specific payload
    pub(super) kind: FrameKind,
}

impl ExecutionFrame {
    pub(super) const fn new(pc: usize, kind: FrameKind) -> Self {
        Self { pc, kind }
    }

    pub(super) const fn main(pc: usize, return_register: u8) -> Self {
        Self {
            pc,
            kind: FrameKind::Main {
                return_value_register: return_register,
            },
        }
    }
}

/// Different categories of execution frames managed by the stackless engine
#[derive(Debug, Clone)]
pub(super) enum FrameKind {
    /// Main entry frame used when executing the program start point
    Main { return_value_register: u8 },
    /// Rule execution frame (replaces recursive jump_to calls)
    Rule(RuleFrameData),
    /// Loop iteration frame
    Loop {
        return_pc: usize,
        context: LoopContext,
    },
    /// Comprehension frame
    Comprehension {
        return_pc: usize,
        context: ComprehensionContext,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RuleFramePhase {
    Initializing,
    ExecutingDestructuring,
    ExecutingBody,
    Finalizing,
}

#[derive(Debug, Clone)]
pub(super) struct RuleFrameData {
    pub(super) return_pc: usize,
    pub(super) dest_reg: u8,
    pub(super) rule_index: u16,
    pub(super) current_definition_index: usize,
    pub(super) current_body_index: usize,
    pub(super) total_definitions: usize,
    pub(super) phase: RuleFramePhase,
    pub(super) accumulated_result: Option<Value>,
    pub(super) any_body_succeeded: bool,
    pub(super) rule_failed_due_to_inconsistency: bool,
    pub(super) rule_type: RuleType,
    pub(super) result_reg: u8,
    pub(super) is_function_rule: bool,
    pub(super) num_registers: usize,
    pub(super) num_retained_registers: usize,
    pub(super) saved_registers: Vec<Value>,
    pub(super) saved_loop_stack: Vec<LoopContext>,
    pub(super) saved_comprehension_stack: Vec<ComprehensionContext>,
}

/// Explicit execution stack replacing the Rust call stack
#[derive(Debug, Clone, Default)]
pub(super) struct ExecutionStack {
    frames: Vec<ExecutionFrame>,
}

impl ExecutionStack {
    pub const fn new() -> Self {
        Self { frames: Vec::new() }
    }

    pub fn push(&mut self, frame: ExecutionFrame) {
        self.frames.push(frame);
    }

    pub fn pop(&mut self) -> Option<ExecutionFrame> {
        self.frames.pop()
    }

    pub fn last(&self) -> Option<&ExecutionFrame> {
        self.frames.last()
    }

    pub fn last_mut(&mut self) -> Option<&mut ExecutionFrame> {
        self.frames.last_mut()
    }

    pub const fn is_empty(&self) -> bool {
        self.frames.is_empty()
    }

    pub const fn len(&self) -> usize {
        self.frames.len()
    }

    pub fn get(&self, index: usize) -> Option<&ExecutionFrame> {
        self.frames.get(index)
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut ExecutionFrame> {
        self.frames.get_mut(index)
    }

    pub fn clear(&mut self) {
        self.frames.clear();
    }
}

/// Represents the current execution state of the VM
#[derive(Debug, Clone, PartialEq, Default)]
pub enum ExecutionState {
    #[default]
    Ready,
    Running,
    Suspended {
        reason: SuspendReason,
        pc: usize,
        last_result: Value,
    },
    Completed {
        result: Value,
    },
    Error {
        error: VmError,
    },
}

/// Reasons why execution may suspend
#[derive(Debug, Clone, PartialEq)]
pub enum SuspendReason {
    SuspendInstruction,
    Breakpoint {
        pc: usize,
    },
    Step,
    InstructionLimit,
    External,
    HostAwait {
        dest: u8,
        argument: Value,
        identifier: Value,
    },
}

/// Execution mode controls whether the VM runs straight through or supports suspension
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionMode {
    /// Execute in a single pass without exposing suspension points
    RunToCompletion,
    /// Execute cooperatively, allowing host-visible suspension and resume
    Suspendable,
}

/// Set of breakpoints used by the suspendable engine
pub(super) type BreakpointSet = BTreeSet<usize>;
