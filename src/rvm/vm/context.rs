// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::{ComprehensionMode, LoopMode};
use crate::value::Value;
use crate::value::{Object, ObjectCursor};
use crate::Rc;
use alloc::collections::BTreeSet;
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

/// Iterator state for different collection types.
///
/// Snapshot independence for `Object` is provided by the shared
/// `Rc<Object>` — `Rc::make_mut` on an aliased Rc allocates a new
/// collection, leaving the iterator's Rc pointing at the original
/// pre-mutation state. The `ObjectCursor` is opaque and resumes in
/// O(log n) for the BTree backend.
///
/// `Set` continues to use the pre-existing snapshot-by-cloned-key
/// approach (`current_item` + `first_iteration`); migration of `Set`
/// to a cursor-based iterator ships with the `Set` storage abstraction
/// in a follow-up PR.
#[derive(Debug, Clone)]
pub enum IterationState {
    Array {
        items: Rc<Vec<Value>>,
        index: usize,
    },
    Object {
        obj: Rc<Object>,
        cursor: ObjectCursor,
    },
    Set {
        items: Rc<BTreeSet<Value>>,
        current_item: Option<Value>,
        first_iteration: bool,
    },
    /// Virtual single-element iteration for non-collection values.
    /// Used by Azure Policy's `[*]` on scalar/null fields: presents a single
    /// "virtual" element to iterate over, which is always `Null` regardless
    /// of the underlying source value.
    Single {
        consumed: bool,
    },
}

impl IterationState {
    pub(super) const fn advance(&mut self) {
        match *self {
            Self::Array { ref mut index, .. } => {
                // Array iteration uses `usize` as the cursor and advances via
                // `saturating_add(1)`. A cursor already at `usize::MAX` here
                // means a stuck (non-progressing) iteration was emitted by
                // malformed bytecode; assert in debug to surface it loudly.
                debug_assert!(
                    *index < usize::MAX,
                    "IterationState::Array index already at usize::MAX on advance"
                );
                *index = index.saturating_add(1);
            }
            // For Object the cursor advances inside `setup_next_iteration`
            // when it pulls the next item via `Object::next`, so `advance`
            // is a no-op for the cursor-backed Object variant.
            Self::Object { .. } => {}
            Self::Set {
                ref mut first_iteration,
                ..
            } => {
                *first_iteration = false;
            }
            Self::Single {
                ref mut consumed, ..
            } => {
                // `Single` yields exactly once; advancing a consumed Single
                // means the compiler emitted a redundant LoopNext.
                debug_assert!(
                    !*consumed,
                    "IterationState::Single advanced after consumption"
                );
                *consumed = true;
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

#[cfg(test)]
#[allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::unreachable,
    clippy::pattern_type_mismatch,
    clippy::shadow_unrelated,
    clippy::panic
)]
mod tests {
    use super::*;
    use crate::value::Object;

    /// IterationState::Object holds an `Rc<Object>` plus an opaque cursor.
    /// Mutating an aliased Rc via `Rc::make_mut` allocates a new collection
    /// (CoW) so the in-flight iterator's source is unaffected.
    #[test]
    fn iteration_state_object_is_snapshot_independent_of_source() {
        let mut obj = Object::new();
        obj.insert(Value::from("a"), Value::from(1));
        obj.insert(Value::from("b"), Value::from(2));
        obj.insert(Value::from("c"), Value::from(3));

        let source = Value::Object(Rc::new(obj));

        let snapshot_obj = match &source {
            Value::Object(o) => Rc::clone(o),
            _ => unreachable!(),
        };
        let state = IterationState::Object {
            obj: Rc::clone(&snapshot_obj),
            cursor: snapshot_obj.cursor(),
        };

        // Mutate a clone of the source mid-iteration.
        let mut alias = source.clone();
        let inner = alias.as_object_mut().expect("object");
        inner.insert(Value::from("a"), Value::from(999));
        inner.insert(Value::from("d"), Value::from(4));
        inner.remove(&Value::from("b"));

        // Drain the snapshot via the cursor — must still report the original
        // 3 entries with original values.
        let mut collected: Vec<(Value, Value)> = Vec::new();
        if let IterationState::Object {
            ref obj,
            mut cursor,
        } = state
        {
            while let Some((k, v)) = obj.next(&mut cursor) {
                collected.push((k.clone(), v.clone()));
            }
        } else {
            unreachable!();
        }
        assert_eq!(collected.len(), 3);
        assert!(collected.contains(&(Value::from("a"), Value::from(1))));
        assert!(collected.contains(&(Value::from("b"), Value::from(2))));
        assert!(collected.contains(&(Value::from("c"), Value::from(3))));
        assert!(!collected.iter().any(|kv| kv.0 == Value::from("d")));

        // The original source Value (untouched) is also unchanged.
        let src_obj = source.as_object().expect("object");
        assert_eq!(src_obj.len(), 3);
        assert_eq!(src_obj.get(&Value::from("a")), Some(&Value::from(1)));
    }
}
