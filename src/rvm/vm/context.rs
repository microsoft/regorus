// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::{ComprehensionMode, LoopMode};
use crate::value::Value;
use crate::Rc;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

/// Loop execution context for managing iteration state
#[derive(Debug, Clone)]
pub struct LoopContext {
    pub mode: LoopMode,
    pub iteration_state: IterationState,
    pub key_reg: u8,
    pub value_reg: u8,
    pub result_reg: u8,
    pub body_start: u16,
    pub loop_end: u16,
    pub loop_next_pc: u16, // PC of the LoopNext instruction to avoid searching
    pub body_resume_pc: usize,
    pub success_count: usize,
    pub total_iterations: usize,
    pub current_iteration_failed: bool, // Track if current iteration had condition failures
}

/// Iterator state for different collection types
#[derive(Debug, Clone)]
pub enum IterationState {
    Array {
        items: Rc<Vec<Value>>,
        index: usize,
    },
    Object {
        obj: Rc<BTreeMap<Value, Value>>,
        current_key: Option<Value>,
        first_iteration: bool,
    },
    Set {
        items: Rc<BTreeSet<Value>>,
        current_item: Option<Value>,
        first_iteration: bool,
    },
}

impl IterationState {
    pub(super) const fn advance(&mut self) {
        match *self {
            Self::Array { ref mut index, .. } => {
                *index = index.saturating_add(1);
            }
            Self::Object {
                ref mut first_iteration,
                ..
            }
            | Self::Set {
                ref mut first_iteration,
                ..
            } => {
                *first_iteration = false;
            }
        }
    }
}

#[allow(unused)]
#[derive(Debug, Clone)]
pub struct CallRuleContext {
    pub return_pc: usize,
    pub dest_reg: u8,
    pub result_reg: u8,
    pub rule_index: u16,
    pub rule_type: crate::rvm::program::RuleType,
    pub current_definition_index: usize,
    pub current_body_index: usize,
}

/// Context for tracking active comprehensions
#[derive(Debug, Clone)]
pub(super) struct ComprehensionContext {
    /// Type of comprehension (Array, Set, Object)
    pub(super) mode: ComprehensionMode,
    /// Register storing the comprehension result collection
    pub(super) result_reg: u8,
    /// Register holding the current iteration key
    pub(super) key_reg: u8,
    /// Register holding the current iteration value
    pub(super) value_reg: u8,
    /// Jump target for comprehension body start
    pub(super) body_start: u16,
    /// Jump target for comprehension end
    pub(super) comprehension_end: u16,
    /// Iteration state when comprehension manages iteration itself (None when driven by LoopStart/LoopNext)
    pub(super) iteration_state: Option<IterationState>,
    /// Resume location for the parent frame once this comprehension completes
    pub(super) resume_pc: usize,
}
