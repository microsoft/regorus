// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Thread-local interning of object **keys** during JSON deserialization.
//!
//! [`Value::from_json_str`](crate::Value::from_json_str) installs a thread-local
//! [`InternTable`] for the duration of the parse (see [`InternGuard`]). Object
//! keys parsed while a table is installed are deduplicated: a homogeneous array
//! of `N` objects sharing `K` keys allocates `K` key strings instead of
//! `N * K`, and every later occurrence becomes a reference-count clone. Only
//! keys are interned -- string *values* are left untouched, since their
//! cardinality is unbounded and interning them can cost more than it saves.
//!
//! The table lives only for the parse and is torn down when the guard drops, so
//! there is no unbounded, thread-lifetime cache. This module is std-only: it
//! relies on `thread_local!`.

use core::cell::RefCell;
use std::collections::HashSet;

/// A content-addressed interning table scoped to a single deserialization call.
///
/// Stores each distinct key's own `Rc<str>` (the allocation serde already made),
/// so interning a repeated key returns a reference-count clone of that existing
/// allocation and never copies the key bytes a second time.
struct InternTable {
    set: HashSet<crate::Rc<str>>,
}

impl InternTable {
    fn new() -> Self {
        Self {
            set: HashSet::new(),
        }
    }

    /// Return an interned handle equal to `rc`. The first time a given key is
    /// seen its own allocation is retained and returned; later occurrences reuse
    /// that allocation and the caller's `rc` is dropped.
    fn intern(&mut self, rc: crate::Rc<str>) -> crate::Rc<str> {
        if let Some(existing) = self.set.get(rc.as_ref()) {
            return crate::Rc::clone(existing);
        }
        self.set.insert(crate::Rc::clone(&rc));
        rc
    }
}

std::thread_local! {
    static TABLE: RefCell<Option<InternTable>> = const { RefCell::new(None) };
}

/// RAII guard that installs a thread-local [`InternTable`] for the duration of a
/// deserialization call. Re-entrant: if a table is already installed (e.g. a
/// nested parse), this guard reuses it and does not tear it down on drop.
pub struct InternGuard {
    installed_by_us: bool,
}

impl InternGuard {
    /// Install a fresh intern table for the current thread, unless one is
    /// already installed (in which case the existing table is reused).
    pub fn install() -> Self {
        let installed_by_us = TABLE.with(|t| {
            let mut slot = t.borrow_mut();
            if slot.is_none() {
                *slot = Some(InternTable::new());
                true
            } else {
                false
            }
        });
        Self { installed_by_us }
    }
}

impl Drop for InternGuard {
    fn drop(&mut self) {
        if self.installed_by_us {
            TABLE.with(|t| {
                *t.borrow_mut() = None;
            });
        }
    }
}

/// Intern `rc` using the current thread's active [`InternTable`], if one is
/// installed. Outside a parse (no guard active) the original `rc` is returned
/// unchanged, so callers keep their allocation with no interning overhead.
pub fn intern_key(rc: crate::Rc<str>) -> crate::Rc<str> {
    TABLE.with(|t| match t.borrow_mut().as_mut() {
        Some(table) => table.intern(rc),
        None => rc,
    })
}

/// Test-only probe: whether an intern table is currently installed on this thread.
#[cfg(test)]
pub fn is_installed() -> bool {
    TABLE.with(|t| t.borrow().is_some())
}
