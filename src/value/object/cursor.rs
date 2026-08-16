// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Resumable, self-owned cursor over an [`Object`]'s entries.

use core::ops::Bound;

use super::{Object, Repr};
use crate::value::Value;

impl Object {
    /// Create a resumable cursor over entries in implementation-defined
    /// order. Stable for the lifetime of `&self`. O(1).
    #[inline]
    pub const fn cursor(&self) -> ObjectCursor {
        ObjectCursor {
            inner: ObjectCursorInner::Start,
        }
    }

    /// Advance `cursor` and yield the next entry.
    pub fn next<'a>(&'a self, cursor: &mut ObjectCursor) -> Option<(&'a Value, &'a Value)> {
        match (&self.repr, &mut cursor.inner) {
            (Repr::Empty, _) => None,
            (Repr::Frozen(v), ObjectCursorInner::Start) => {
                if let Some((k, val)) = v.first() {
                    cursor.inner = ObjectCursorInner::Key(k.clone());
                    Some((k, val))
                } else {
                    None
                }
            }
            (Repr::Frozen(v), ObjectCursorInner::Key(prev)) => {
                let i = match v.binary_search_by(|(k, _)| k.cmp(prev)) {
                    Ok(i) => i.saturating_add(1),
                    Err(i) => i,
                };
                if let Some((k, val)) = v.get(i) {
                    cursor.inner = ObjectCursorInner::Key(k.clone());
                    Some((k, val))
                } else {
                    None
                }
            }
            (Repr::BTree(m), ObjectCursorInner::Start) => {
                let (k, val) = m.iter().next()?;
                cursor.inner = ObjectCursorInner::Key(k.clone());
                Some((k, val))
            }
            (Repr::BTree(m), ObjectCursorInner::Key(prev)) => {
                let (k, val) = m
                    .range((Bound::Excluded(prev.clone()), Bound::Unbounded))
                    .next()?;
                cursor.inner = ObjectCursorInner::Key(k.clone());
                Some((k, val))
            }
        }
    }
}

/// Opaque resumable cursor over an [`Object`]'s entries in
/// implementation-defined order.
///
/// Self-owned: holds no borrow on the `Object`, so it can be stored as a
/// field of a long-lived state struct (e.g. an RVM iteration frame).
#[derive(Debug, Clone)]
pub struct ObjectCursor {
    inner: ObjectCursorInner,
}

#[derive(Debug, Clone)]
enum ObjectCursorInner {
    Start,
    Key(Value),
}
