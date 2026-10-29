//! Native hashbrown leaves; representatives model Eq classes, not Rust identity.

use core::hash::Hash;
use hashbrown::HashMap;
use junco_core::error::HistoryError;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
pub(crate) struct NativeMap<K: Copy + Eq + Hash> {
    inner: HashMap<K, u64>,
}

/// These are precisely the finite representatives stored by this native map.
pub(crate) uninterp spec fn representatives<K: Copy + Eq + Hash>(map: NativeMap<K>) -> Seq<(K, u64)>;

/// Native Hash/Eq coherence is an obligation, never inferred for opaque user types.
pub(crate) uninterp spec fn hash_coherent<K: Copy + Eq + Hash>() -> bool;

pub(crate) open(crate) spec fn key_obligations<K: Copy + Eq + Hash>() -> bool {
    K::obeys_eq_spec() && hash_coherent::<K>()
        && (forall|a: K| #[trigger] a.eq_spec(&a))
        && (forall|a: K, b: K| #[trigger] a.eq_spec(&b) == b.eq_spec(&a))
        && (forall|a: K, b: K, c: K| #[trigger] a.eq_spec(&b)
            && #[trigger] b.eq_spec(&c) ==> a.eq_spec(&c))
}

impl<K: Copy + Eq + Hash> NativeMap<K> {
    #[verifier::external_body]
    pub(super) fn new() -> (result: Self)
        ensures representatives(result) == Seq::<(K, u64)>::empty(),
    {
        Self { inner: HashMap::new() }
    }

    #[verifier::external_body]
    pub(super) fn lookup(&self, key: &K) -> (result: Option<u64>)
        ensures key_obligations::<K>() ==> match result {
            Some(id) => exists|i: int| 0 <= i < representatives(*self).len()
                && representatives(*self)[i].1 == id
                && key.eq_spec(&representatives(*self)[i].0),
            None => forall|i: int| 0 <= i < representatives(*self).len()
                ==> !key.eq_spec(&representatives(*self)[i].0),
        },
    {
        self.inner.get(key).copied()
    }

    #[verifier::external_body]
    pub(super) fn reserve_one(&mut self) -> (result: Result<(), HistoryError>)
        ensures representatives(*final(self)) == representatives(*old(self)),
    {
        #[cfg(any(test, feature = "test-util"))]
        junco_core::observation::reservation_checkpoint()
            .map_err(|_| HistoryError::AllocationFailed)?;
        self.inner.try_reserve(1).map_err(|_| HistoryError::AllocationFailed)
    }

    #[verifier::external_body]
    pub(super) fn insert_fresh(&mut self, key: K, id: u64)
        requires key_obligations::<K>() ==> forall|i: int|
            0 <= i < representatives(*old(self)).len()
                ==> !key.eq_spec(&representatives(*old(self))[i].0),
        ensures key_obligations::<K>() ==>
            representatives(*final(self)) == representatives(*old(self)).push((key, id)),
    {
        self.inner.insert(key, id);
    }
}
}
