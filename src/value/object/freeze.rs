// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Freeze/thaw transitions between mutable `BTree` storage and compact
//! read-mostly `Frozen` boxed-slice storage.

use alloc::boxed::Box;
use alloc::vec::Vec;

use super::{Object, Repr};
use crate::value::Value;

impl Object {
    /// Convert to the immutable boxed-slice representation.
    pub(crate) fn freeze(mut self) -> Self {
        self.freeze_in_place();
        self
    }

    /// Wrap into a `Value::Object`.
    #[inline]
    pub fn into_value(self) -> Value {
        Value::Object(crate::Rc::new(self.freeze()))
    }

    #[cfg(test)]
    #[doc(hidden)]
    pub(crate) const fn storage_variant_for_memory_diagnostics(&self) -> &'static str {
        match &self.repr {
            Repr::Empty => "Empty",
            Repr::Frozen(_) => "Frozen",
            Repr::BTree(_) => "BTree",
        }
    }

    fn freeze_in_place(&mut self) {
        match core::mem::take(&mut self.repr) {
            Repr::Empty => {
                self.repr = Repr::Frozen(Box::new([]));
            }
            Repr::Frozen(v) => {
                debug_assert_sorted_dedup(&v);
                self.repr = Repr::Frozen(v);
            }
            Repr::BTree(m) => {
                let boxed = m.into_iter().collect::<Vec<_>>().into_boxed_slice();
                // Release-critical invariant: BTreeMap iteration is sorted and deduplicated
                // before Frozen binary-search storage is constructed.
                debug_assert_sorted_dedup(&boxed);
                self.repr = Repr::Frozen(boxed);
            }
        }
    }

    pub(super) fn thawed_repr(v: Box<[(Value, Value)]>) -> Repr {
        debug_assert_sorted_dedup(&v);
        if v.is_empty() {
            Repr::Empty
        } else {
            Repr::BTree(Vec::from(v).into_iter().collect())
        }
    }

    pub(super) fn thaw(&mut self) {
        let repr = core::mem::take(&mut self.repr);
        self.repr = match repr {
            Repr::Frozen(v) => Self::thawed_repr(v),
            other => other,
        };
    }
}

#[cfg(debug_assertions)]
fn debug_assert_sorted_dedup(v: &[(Value, Value)]) {
    // This debug-only check documents a release-critical invariant: Frozen storage is
    // always sorted and deduplicated by construction, and release binary searches depend on it.
    for pair in v.windows(2) {
        debug_assert!(
            pair[0].0.cmp(&pair[1].0).is_lt(),
            "Object Frozen entries must be strictly sorted and deduplicated; \
             TODO(Number): revisit NaN ordering/equality semantics in src/number.rs:290-316"
        );
    }
}

#[cfg(not(debug_assertions))]
#[inline]
fn debug_assert_sorted_dedup(_: &[(Value, Value)]) {}
