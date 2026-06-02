// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! See [`Set`].

mod iter;
mod serde;

use alloc::collections::BTreeSet;
use core::cmp::Ordering;
use core::fmt;
use core::ops::Bound;

use crate::value::Value;

#[allow(unused_imports)] // surface for downstream PRs
pub use iter::{IntoIter, Iter};

/// Opaque, ordered set of [`Value`]s.
///
/// The current backing storage is `BTreeSet<Value>`. The inner field is
/// private so the representation can change (hash-backed, lazy, bloom-fronted,
/// FFI-backed) without touching call sites.
///
/// # Iteration
///
/// - [`Set::iter`] — implementation-defined order; non-resumable.
/// - [`Set::iter_sorted`] — sorted by `Value::Ord`; non-resumable.
/// - [`Set::cursor`] / [`Set::next`] — implementation-defined order,
///   resumable; cheapest per-step cost. Used by interpreter/RVM when iteration
///   must yield mid-flight.
#[derive(Default, Clone, Eq, PartialEq)]
pub struct Set {
    inner: BTreeSet<Value>,
}

impl Set {
    /// Create an empty `Set`.
    #[inline]
    pub const fn new() -> Self {
        Self {
            inner: BTreeSet::new(),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[inline]
    pub fn contains(&self, value: &Value) -> bool {
        self.inner.contains(value)
    }

    #[inline]
    pub fn get(&self, value: &Value) -> Option<&Value> {
        self.inner.get(value)
    }

    /// First element in sorted order (by `Value::Ord`).
    #[inline]
    pub fn first(&self) -> Option<&Value> {
        self.iter_sorted().next()
    }

    /// Last element in sorted order (by `Value::Ord`).
    #[inline]
    pub fn last(&self) -> Option<&Value> {
        self.iter_sorted().next_back()
    }

    /// Iteration in implementation-defined order. Non-resumable.
    ///
    /// For the current BTree-backed storage this happens to be sorted, but
    /// callers MUST NOT depend on that. Use [`Set::iter_sorted`] when
    /// deterministic order is required, or [`Set::cursor`] when iteration
    /// must yield and resume.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &Value> + '_ {
        self.inner.iter()
    }

    /// Iteration in sorted order (by `Value::Ord`). Non-resumable.
    ///
    /// Use this for serialization, snapshots, hashing, `Debug`, etc.
    #[inline]
    pub fn iter_sorted(&self) -> Iter<'_> {
        // BTree backend iterates sorted natively.
        Iter {
            inner: self.inner.iter(),
        }
    }

    /// Insert `value`. Returns `true` if the value was newly inserted.
    #[inline]
    pub fn insert(&mut self, value: Value) -> bool {
        self.inner.insert(value)
    }

    #[inline]
    pub fn remove(&mut self, value: &Value) -> bool {
        self.inner.remove(value)
    }

    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&Value) -> bool,
    {
        self.inner.retain(f);
    }

    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    #[inline]
    pub fn append(&mut self, other: &mut Set) {
        self.inner.append(&mut other.inner);
    }

    /// Set intersection. Returns a new `Set` containing the elements
    /// present in both `self` and `other`.
    pub fn intersection(&self, other: &Set) -> Set {
        Set {
            inner: self.inner.intersection(&other.inner).cloned().collect(),
        }
    }

    /// Set union. Returns a new `Set` containing the elements present in
    /// either `self` or `other`.
    pub fn union(&self, other: &Set) -> Set {
        Set {
            inner: self.inner.union(&other.inner).cloned().collect(),
        }
    }

    /// Set difference. Returns a new `Set` containing the elements present
    /// in `self` but not in `other`.
    pub fn difference(&self, other: &Set) -> Set {
        Set {
            inner: self.inner.difference(&other.inner).cloned().collect(),
        }
    }

    #[inline]
    pub fn is_subset(&self, other: &Set) -> bool {
        self.inner.is_subset(&other.inner)
    }

    /// Wrap into a `Value::Set`.
    #[inline]
    pub fn into_value(self) -> Value {
        Value::Set(crate::Rc::new(self.inner))
    }

    /// Create a resumable cursor over elements in implementation-defined
    /// order. Stable for the lifetime of `&self`. O(1).
    ///
    /// The cursor is fully self-owned (it stores a clone of the last-seen
    /// element, not a reference) so it can be stored as a field of a
    /// long-lived state struct — e.g. an RVM iteration frame that persists
    /// across instruction dispatches. As a consequence, mutating the `Set`
    /// between `next()` calls is not rejected by the borrow checker; the
    /// resulting iteration order in that case is unspecified.
    #[inline]
    pub const fn cursor(&self) -> SetCursor {
        SetCursor {
            inner: SetCursorInner::BTree(None),
        }
    }

    /// Advance `cursor` and yield the next element. O(log n) for the BTree
    /// backend (range probe); future hash/inline variants may be O(1).
    pub fn next<'a>(&'a self, cursor: &mut SetCursor) -> Option<&'a Value> {
        let SetCursorInner::BTree(ref mut last) = cursor.inner;
        let next = last.as_ref().map_or_else(
            || self.inner.iter().next(),
            |prev| {
                // `(Bound<&T>, Bound<&T>)` impls `RangeBounds<T>` — no clone
                // needed to build the resume bound.
                self.inner
                    .range((Bound::Excluded(prev), Bound::Unbounded))
                    .next()
            },
        );
        let v = next?;
        *last = Some(v.clone());
        Some(v)
    }
}

/// Opaque resumable cursor over a [`Set`]'s elements in
/// implementation-defined order.
///
/// Self-owned: holds no borrow on the `Set`, so it can be stored as a
/// field of a long-lived state struct (e.g. an RVM iteration frame).
#[derive(Debug, Clone)]
pub struct SetCursor {
    inner: SetCursorInner,
}

#[derive(Debug, Clone)]
enum SetCursorInner {
    /// BTree backend cursor: tracks last-seen element. `None` means "before start".
    BTree(Option<Value>),
}

// ---- Hand-written Ord/PartialOrd ----------------------------------------
//
// Implemented in terms of `iter_sorted()` so ordering is consistent with the
// canonical (sorted) view of the elements and is therefore independent of
// the storage variant.

impl Ord for Set {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter_sorted().cmp(other.iter_sorted())
    }
}

impl PartialOrd for Set {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Set {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Use sorted iteration so Debug output is stable across storage
        // variants.
        f.debug_set().entries(self.iter_sorted()).finish()
    }
}

impl Extend<Value> for Set {
    fn extend<I: IntoIterator<Item = Value>>(&mut self, iter: I) {
        self.inner.extend(iter);
    }
}

impl FromIterator<Value> for Set {
    fn from_iter<I: IntoIterator<Item = Value>>(iter: I) -> Self {
        Self {
            inner: BTreeSet::from_iter(iter),
        }
    }
}

impl From<BTreeSet<Value>> for Set {
    #[inline]
    fn from(set: BTreeSet<Value>) -> Self {
        Self { inner: set }
    }
}

impl From<Set> for Value {
    #[inline]
    fn from(s: Set) -> Self {
        s.into_value()
    }
}
