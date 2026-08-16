// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! In-place mutation of an [`Object`]: insert/remove/retain/clear/append and
//! the entry-style `get_or_insert_with`. These operations may thaw `Frozen`
//! storage to `BTree` transparently.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use super::{Object, Repr};
use crate::value::Value;

impl Object {
    /// Insert a key-value pair. Returns the previous value if any.
    pub fn insert(&mut self, key: Value, value: Value) -> Option<Value> {
        match core::mem::take(&mut self.repr) {
            Repr::Empty => {
                let mut m = BTreeMap::new();
                m.insert(key, value);
                self.repr = Repr::BTree(m);
                None
            }
            Repr::Frozen(mut v) => {
                // Value-only mutation preserves sorted keys and keeps compact Frozen storage.
                // Structural mutation (new key or remove) thaws below.
                if let Ok(i) = v.binary_search_by(|(k, _)| k.cmp(&key)) {
                    let prev = core::mem::replace(&mut v[i].1, value);
                    self.repr = Repr::Frozen(v);
                    return Some(prev);
                }
                self.repr = Self::thawed_repr(v);
                self.insert(key, value)
            }
            Repr::BTree(mut m) => {
                let prev = m.insert(key, value);
                self.repr = Repr::BTree(m);
                prev
            }
        }
    }

    pub fn remove(&mut self, key: &Value) -> Option<Value> {
        match core::mem::take(&mut self.repr) {
            Repr::Empty => {
                self.repr = Repr::Empty;
                None
            }
            Repr::Frozen(v) => {
                // Absent key: keep compact Frozen storage untouched.
                // Present key: thaw to a mutable representation, then remove.
                if v.binary_search_by(|(k, _)| k.cmp(key)).is_err() {
                    self.repr = Repr::Frozen(v);
                    return None;
                }
                self.repr = Self::thawed_repr(v);
                self.remove(key)
            }
            Repr::BTree(mut m) => {
                let prev = m.remove(key);
                self.repr = Repr::BTree(m);
                prev
            }
        }
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Value, &mut Value) -> bool,
    {
        match core::mem::take(&mut self.repr) {
            Repr::Empty => {
                self.repr = Repr::Empty;
            }
            Repr::Frozen(v) => {
                self.repr = Self::thawed_repr(v);
                self.retain(f);
            }
            Repr::BTree(mut m) => {
                m.retain(|k, v| f(k, v));
                self.repr = Repr::BTree(m);
            }
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.repr = Repr::Empty;
    }

    pub fn append(&mut self, other: &mut Object) {
        let drained: Vec<(Value, Value)> = match core::mem::take(&mut other.repr) {
            Repr::Empty => Vec::new(),
            Repr::Frozen(v) => Vec::from(v),
            Repr::BTree(m) => m.into_iter().collect(),
        };
        other.repr = Repr::Empty;
        for (k, v) in drained {
            self.insert(k, v);
        }
    }

    /// Gets a mutable reference to the value associated with `key`, inserting
    /// the result of `default()` if absent.
    pub fn get_or_insert_with<F: FnOnce() -> Value>(
        &mut self,
        key: Value,
        default: F,
    ) -> &mut Value {
        self.repr.get_or_insert_with(key, default)
    }
}

impl Repr {
    /// Entry-style lookup that inserts `default()` when the key is absent.
    ///
    /// An existing key in `Frozen` storage returns its value slot in place, keeping
    /// the compact representation. Otherwise storage is normalized to `BTree` before
    /// inserting. Recursion is bounded to at most 3 frames: each call advances the repr
    /// state toward the terminal `BTree` arm (`Frozen` -> `Empty`/`BTree`, `Empty` ->
    /// `BTree`), never on data depth, so there is no stack-overflow risk on any input.
    fn get_or_insert_with<F: FnOnce() -> Value>(&mut self, key: Value, default: F) -> &mut Value {
        // Locate an existing key in Frozen storage up front (scoped borrow, yields an
        // index by value). Splitting this from the in-place return below sidesteps NLL
        // problem case 3, where a conditionally-returned borrow would block the thaw.
        let frozen_index = match self {
            Repr::Frozen(v) => v.binary_search_by(|(k, _)| k.cmp(&key)).ok(),
            _ => None,
        };

        // Absent key (or non-Frozen storage): normalize to `BTree`, thawing Frozen on
        // the way, then insert. This branch always returns, so no borrow reaches below.
        if frozen_index.is_none() {
            match self {
                Repr::Empty => *self = Repr::BTree(BTreeMap::new()),
                Repr::BTree(m) => return m.entry(key).or_insert_with(default),
                Repr::Frozen(_) => {
                    let repr = core::mem::take(self);
                    *self = match repr {
                        Repr::Frozen(v) => Object::thawed_repr(v),
                        other => other,
                    };
                }
            }
            return self.get_or_insert_with(key, default);
        }

        // Existing key in Frozen storage: return its value slot in place, keeping the
        // compact representation (keys are unchanged, so the sort order still holds).
        match (self, frozen_index) {
            (Repr::Frozen(v), Some(i)) => &mut v[i].1,
            (this, _) => this.get_or_insert_with(key, default),
        }
    }
}
