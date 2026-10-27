// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! See [`Object`].
//!
//! `Object` uses private storage variants tuned for memory and mutation cost.
//! `Frozen` means compact boxed-slice storage, not semantic immutability:
//! mutable APIs such as [`Object::insert`], [`Object::remove`], and
//! [`Object::get_mut`] may update values in place or thaw storage
//! transparently. `Empty`, `Frozen`, and `BTree` are optimization
//! details and callers must not depend on which representation is selected.
//!
//! The implementation is split across sibling modules that share the private
//! `repr` field: [`mutate`] (insert/remove/retain/get_or_insert_with),
//! [`freeze`] (freeze/thaw transitions), and [`cursor`] (resumable iteration).

mod cursor;
mod freeze;
mod iter;
mod mutate;
mod serde;

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use core::cmp::Ordering;
use core::fmt;

use crate::value::Value;
use vstd::prelude::verus_verify;

#[cfg(feature = "rvm")]
pub use cursor::ObjectCursor;
pub use iter::{IntoIter, Iter, IterMut};

/// Opaque, ordered key-value map keyed by [`Value`].
///
/// Backed by a three-variant representation: empty objects use zero-allocation
/// storage, mutable objects use `BTreeMap`, and read-mostly objects freeze to an
/// exact-size boxed slice. The representation is private so it can change
/// without touching call sites.
///
/// # Iteration
///
/// - [`Object::iter`] — implementation-defined order; non-resumable.
/// - [`Object::iter_sorted`] — sorted by `Value::Ord`; non-resumable.
/// - [`Object::cursor`] / [`Object::next`] — implementation-defined order,
///   resumable; cheapest per-step cost. Used by interpreter/RVM when iteration
///   must yield mid-flight.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Default, Clone)]
pub struct Object {
    pub(super) repr: Repr,
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone)]
pub(super) enum Repr {
    Empty,
    /// Compact sorted, deduplicated entries with no spare capacity.
    ///
    /// Release-critical invariant: Frozen keys are strictly sorted and deduplicated.
    /// `get`/`insert`/cursor resume use binary search in all builds, so every construction
    /// path must preserve this before entering `Repr::Frozen`.
    Frozen(Box<[(Value, Value)]>),
    BTree(BTreeMap<Value, Value>),
}

impl Default for Repr {
    #[inline]
    fn default() -> Self {
        Repr::Empty
    }
}

impl Object {
    /// Create an empty `Object`.
    #[inline]
    pub const fn new() -> Self {
        Self { repr: Repr::Empty }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match &self.repr {
            Repr::Empty => 0,
            Repr::Frozen(v) => v.len(),
            Repr::BTree(m) => m.len(),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, key: &Value) -> Option<&Value> {
        match &self.repr {
            Repr::Empty => None,
            Repr::Frozen(v) => match v.binary_search_by(|(k, _)| k.cmp(key)) {
                Ok(i) => Some(&v[i].1),
                Err(_) => None,
            },
            Repr::BTree(m) => m.get(key),
        }
    }

    #[inline]
    pub fn contains_key(&self, key: &Value) -> bool {
        self.get(key).is_some()
    }

    pub fn get_mut(&mut self, key: &Value) -> Option<&mut Value> {
        // Returning `&mut Value` for an existing key is a value-only mutation:
        // it never reorders or removes keys, so `Frozen` storage is preserved
        // in place rather than thawed (mirrors `insert`/`get_or_insert_with`).
        match &mut self.repr {
            Repr::Empty => None,
            Repr::Frozen(v) => match v.binary_search_by(|(k, _)| k.cmp(key)) {
                Ok(i) => Some(&mut v[i].1),
                Err(_) => None,
            },
            Repr::BTree(m) => m.get_mut(key),
        }
    }

    /// Iteration in implementation-defined order. Non-resumable.
    ///
    /// For both current backends this happens to be sorted by `Value::Ord`,
    /// but callers MUST NOT depend on that. Use [`Object::iter_sorted`] when
    /// deterministic order is required, or [`Object::cursor`] when iteration
    /// must yield and resume.
    pub fn iter(&self) -> impl Iterator<Item = (&Value, &Value)> + '_ {
        self.iter_sorted()
    }

    /// Iteration in sorted key order (by `Value::Ord`). Non-resumable.
    ///
    /// Use this for serialization, snapshots, hashing, `Debug`, the
    /// `object.keys` builtin, etc.
    #[inline]
    pub fn iter_sorted(&self) -> Iter<'_> {
        Iter {
            inner: match &self.repr {
                Repr::Empty => iter::IterInner::Empty,
                Repr::Frozen(v) => iter::IterInner::Frozen(v.iter()),
                Repr::BTree(m) => iter::IterInner::BTree(m.iter()),
            },
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = &Value> + '_ {
        self.iter_sorted().map(|(k, _)| k)
    }

    pub fn keys_sorted(&self) -> impl Iterator<Item = &Value> + '_ {
        self.iter_sorted().map(|(k, _)| k)
    }

    pub fn values(&self) -> impl Iterator<Item = &Value> + '_ {
        self.iter_sorted().map(|(_, v)| v)
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_> {
        // Frozen storage is read-only, so thaw it in place before handing out
        // mutable element references. After this, repr is never Frozen.
        self.thaw();
        IterMut {
            inner: match &mut self.repr {
                // `thaw` above guarantees repr is not Frozen here; the Frozen
                // arm is dead, but yielding an empty iterator keeps the match
                // total without a panic.
                Repr::Empty | Repr::Frozen(_) => iter::IterMutInner::Empty,
                Repr::BTree(m) => iter::IterMutInner::BTree(m.iter_mut()),
            },
        }
    }
}

// ---- Hand-written PartialEq/Eq/Ord -------------------------------------
//
// Defined in terms of `iter_sorted()` so equality and ordering are
// consistent with the canonical (sorted) view of the entries and are
// therefore independent of the storage variant. A derived PartialEq on
// `Repr` would incorrectly distinguish `Frozen` from `BTree` even when they
// hold identical entries.

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        self.iter_sorted().eq(other.iter_sorted())
    }
}

impl Eq for Object {}

impl Ord for Object {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter_sorted().cmp(other.iter_sorted())
    }
}

impl PartialOrd for Object {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter_sorted()).finish()
    }
}

impl Extend<(Value, Value)> for Object {
    fn extend<I: IntoIterator<Item = (Value, Value)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl FromIterator<(Value, Value)> for Object {
    fn from_iter<I: IntoIterator<Item = (Value, Value)>>(iter: I) -> Self {
        let mut o = Object::new();
        for (k, v) in iter {
            o.insert(k, v);
        }
        o
    }
}

impl From<BTreeMap<Value, Value>> for Object {
    fn from(map: BTreeMap<Value, Value>) -> Self {
        if map.is_empty() {
            Self { repr: Repr::Empty }
        } else {
            Self {
                repr: Repr::BTree(map),
            }
        }
    }
}

impl From<Object> for Value {
    #[inline]
    fn from(o: Object) -> Self {
        o.into_value()
    }
}

#[cfg(verus_keep_ghost)]
mod verify {
    use super::*;
    use vstd::prelude::*;

    verus! {
        pub open spec fn frozen_map(entries: Seq<(Value, Value)>) -> Map<Value, Value>
            decreases entries.len(),
        {
            if entries.len() == 0 { Map::empty() }
            else {
                frozen_map(entries.drop_last()).insert(entries.last().0, entries.last().1)
            }
        }

        proof fn lemma_frozen_entry(entries: Seq<(Value, Value)>, key: Value)
            requires frozen_map(entries).contains_key(key),
            ensures exists|i: int| 0 <= i < entries.len()
                && entries[i] == (key, frozen_map(entries)[key]),
            decreases entries.len(),
        {
            if entries.last().0 == key {
                assert(entries[entries.len() - 1] == (key, frozen_map(entries)[key]));
            } else {
                lemma_frozen_entry(entries.drop_last(), key);
                let i = choose|i: int| 0 <= i < entries.drop_last().len()
                    && entries.drop_last()[i] == (key, frozen_map(entries.drop_last())[key]);
                assert(entries[i] == (key, frozen_map(entries)[key]));
            }
        }

        impl View for Object {
            type V = Map<Value, Value>;
            closed spec fn view(&self) -> Map<Value, Value> {
                match self.repr {
                    Repr::Empty => Map::empty(),
                    Repr::Frozen(entries) => frozen_map(entries@),
                    Repr::BTree(map) => map@,
                }
            }
        }

        impl Object {
            pub proof fn lemma_entries_smaller(o: crate::Rc<Object>)
                ensures forall|k: Value| o@.contains_key(k)
                    ==> is_smaller_than(k, Value::Object(o))
                        && is_smaller_than(o@[k], Value::Object(o)),
            {
                broadcast use vstd::std_specs::btree::group_btree_axioms;
                broadcast use vstd::set::group_set_lemmas;
                reveal(<Object as View>::view);
                let bound = Value::Object(o);
                let field: crate::Rc<Object> = get_variant_field(bound, "Object", "0");
                assert(is_smaller_than(field, bound));
                assert(is_smaller_than((*o).repr, o));
                assert forall|k: Value| o@.contains_key(k)
                    implies is_smaller_than(k, bound) && is_smaller_than(o@[k], bound) by {
                    match (*o).repr {
                        Repr::Empty => {},
                        Repr::Frozen(entries) => {
                            lemma_frozen_entry(entries@, k);
                            let i = choose|i: int| 0 <= i < entries@.len()
                                && entries@[i] == (k, frozen_map(entries@)[k]);
                            assert(is_smaller_than(entries, (*o).repr));
                            assert(is_smaller_than(entries@, entries));
                            assert(is_smaller_than(entries@[i], entries@));
                            assert(is_smaller_than(entries@[i].0, entries@[i]));
                            assert(is_smaller_than(entries@[i].1, entries@[i]));
                        },
                        Repr::BTree(map) => {
                            assert(is_smaller_than(map, (*o).repr));
                            assert(is_smaller_than(map@, map));
                            vstd::map::axiom_map_decreases_to_entry(map@, k);
                            let entry = (k, map@[k]);
                            assert(is_smaller_than(entry, map@));
                            assert(is_smaller_than(entry.0, entry));
                            assert(is_smaller_than(entry.1, entry));
                        },
                    }
                }
            }
        }
    }
}
