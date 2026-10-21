// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// Upstream: https://github.com/verus-lang/verus/issues/3298 (follow-up to #2689 / #2693).
//
// Minimized Verus reproducer: an impl method that inherits `ensures` from an
// external-trait-extension (`ExPartialEq::eq`) can be verified before the
// concrete spec helpers it needs (`Item::eq_spec`, `Item::obeys_eq_spec`).
//
// Run (stock Verus 0.2026.10.04.426d8b0, vstd 0.0.0-2026-09-06-0133):
//   verus verification/verus/inherited_ensures_order.rs
// Actual:   `postcondition not satisfied` (cmp.rs `Self::obeys_eq_spec() ==> r == self.eq_spec(other)`)
//           on `Item::eq`; 2 verified, 1 errors.
// Expected: 3 verified, 0 errors.
//
// Cause: vir/src/context.rs adds no call-graph edge from `Item::eq` to the
// concrete helpers referenced by its inherited ensures. Ordering is then a
// tie: `early` is inserted first, and Tarjan's DFS from it reaches `Item::eq`
// (via `impl Key for Item` -> `key_eq` -> `==`) before `Item::eq_spec`, so the
// helper axioms are emitted after `Item::eq` is checked.
//
// Each of these controls verifies (3 verified, 0 errors):
//   - delete `early`;
//   - move `early` below the `PartialEqSpecImpl`;
//   - make `key_eq` return `self.value == other.value` instead of `self == other`.
//
// In Regorus the same pattern is graph::verify::tables_space_wf ->
// HashKey impl key_eq -> Primitive::eq -> Term::eq (src/builtins/history/kernel.rs).

use vstd::prelude::*;

verus! {

pub trait Key {
    fn key_eq(&self, other: &Self) -> bool;
}

pub open spec fn uses_key<K: Key>() -> bool { true }

pub open spec fn early() -> bool { uses_key::<Item>() }

pub struct Item { pub value: u32 }

impl Key for Item {
    fn key_eq(&self, other: &Self) -> bool { self == other }
}

impl PartialEq for Item {
    fn eq(&self, other: &Self) -> bool { self.value == other.value }
}

impl vstd::std_specs::cmp::PartialEqSpecImpl for Item {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, other: &Self) -> bool { self.value == other.value }
}

fn main() {}

} // verus!
