//! Verified `eq_spec`-keyed map: entries in insertion order behind a chained hash index on
//! `KeyHash::key_hash`. Under `key_laws` `find` is a lookup on `eq_spec` classes, by proof;
//! nothing here assumes anything about `std::hash::Hash`.
//!
//! Keys are user component types, so user `Eq`/`KeyHash` code runs under the store lock. A panic
//! there unwinds through the lock and is outside the trusted base: Verus assumes the lock
//! invariant on re-entry, and the contracts below hold only for code that returns.

use alloc::vec::Vec;
use hashconsius::index::Buckets;
use history_syntax::KeyHash;
#[cfg(verus_keep_ghost)]
use history_syntax::key_hash::specs::KeyHashSpec;
use junco_core::errors::HistoryError;
#[cfg(verus_keep_ghost)]
use junco_core::spec::hypotheses::key_laws;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use vstd::std_specs::vec::group_vec_axioms;

/// `index` is `None` only while the map is empty, so `new` allocates nothing and mutation can
/// swap the whole table out (Verus checks the type invariant after every `&mut` field call).
pub struct KeyedMap<K: Eq + KeyHash, V> {
    entries: Vec<(K, V)>,
    hashes: Vec<u64>,
    index: Option<Buckets>,
}

impl<K: Eq + KeyHash, V> View for KeyedMap<K, V> {
    type V = Seq<(K, V)>;
    closed spec fn view(&self) -> Seq<(K, V)> { self.entries@ }
}

impl<K: Eq + KeyHash, V> KeyedMap<K, V> {
    #[verifier::type_invariant]
    closed spec fn inv(&self) -> bool {
        &&& self.hashes@.len() == self.entries@.len()
        &&& match self.index {
            Some(index) => index.inv(self.hashes@),
            None => self.entries@.len() == 0,
        }
        &&& K::obeys_hash_spec() ==> forall|j: int| 0 <= j < self.entries@.len()
            ==> #[trigger] self.hashes@[j] == self.entries@[j].0.hash_spec()
    }

    #[allow(clippy::new_without_default)]
    pub fn new() -> (m: Self)
        ensures m@ == Seq::<(K, V)>::empty(),
    {
        Self { entries: Vec::new(), hashes: Vec::new(), index: None }
    }

    /// Index of an entry whose key is `eq_spec`-equal to `key`, if any.
    pub fn find(&self, key: &K) -> (r: Option<usize>)
        ensures
            r matches Some(i) ==> i < self@.len(),
            key_laws::<K>() ==> match r {
                Some(i) => key.eq_spec(&self@[i as int].0),
                None => forall|i: int| 0 <= i < self@.len() ==> !key.eq_spec(&self@[i].0),
            },
    {
        proof { use_type_invariant(&*self); }
        let index = match &self.index {
            Some(index) => index,
            None => { return None; },
        };
        let h = key.key_hash();
        proof {
            index.lemma_nonempty(self.hashes@);
            vstd::std_specs::vec::axiom_spec_len(&self.entries);
        }
        let bucket = index.bucket(h);
        let mut j = 0;
        while j < bucket.len()
            invariant
                self.inv(), self.index == Some(*index), index.nb() > 0, self@.len() <= usize::MAX,
                K::obeys_hash_spec() ==> h == key.hash_spec(),
                bucket@ == index.bucket_of(h),
                0 <= j <= bucket@.len(),
                forall|k: int| 0 <= k < j ==> (#[trigger] bucket@[k].1 < self@.len()
                    && (K::obeys_eq_spec()
                        ==> !(bucket@[k].0 == h && key.eq_spec(&self@[bucket@[k].1 as int].0)))),
            decreases bucket@.len() - j,
        {
            let (bh, u) = bucket[j];
            proof { index.lemma_sound(self.hashes@, h, j as int); }
            if bh == h && *key == self.entries[u].0 {
                return Some(u);
            }
            j += 1;
        }
        proof {
            if key_laws::<K>() {
                assert forall|i: int| 0 <= i < self@.len() implies !key.eq_spec(&self@[i].0) by {
                    if key.eq_spec(&self@[i].0) {
                        assert(self.hashes@[i] == self@[i].0.hash_spec());
                        assert(self.hashes@[i] == h);
                        index.lemma_complete(self.hashes@, i);
                        let k = bucket@.lemma_contains_to_index((h, i as usize));
                        assert(bucket@[k].0 == h && key.eq_spec(&self@[bucket@[k].1 as int].0));
                    }
                }
            }
        }
        None
    }

    pub fn get(&self, key: &K) -> (r: Option<&V>)
        ensures key_laws::<K>() ==> match r {
            Some(v) => exists|i: int| 0 <= i < self@.len() && *v == self@[i].1
                && key.eq_spec(&self@[i].0),
            None => forall|i: int| 0 <= i < self@.len() ==> !key.eq_spec(&self@[i].0),
        },
    {
        match self.find(key) {
            Some(i) => Some(&self.entries[i].1),
            None => None,
        }
    }

    pub fn at(&self, i: usize) -> (r: &(K, V))
        requires i < self@.len(),
        ensures *r == self@[i as int],
    {
        &self.entries[i]
    }

    /// Appends an entry. No freshness precondition: holders prove their own no-duplicate facts
    /// from `find`'s `None` case. `Buckets` growth aborts on OOM (hashconsius's failure model);
    /// call `reserve_one` first for the entry storage.
    // `verus!` expands the destructuring pattern to `entries: entries`.
    #[allow(non_shorthand_field_patterns)]
    pub fn insert_fresh(&mut self, key: K, value: V)
        ensures final(self)@ == old(self)@.push((key, value)),
    {
        proof { use_type_invariant(&*self); }
        let h = key.key_hash();
        let mut table = Self { entries: Vec::new(), hashes: Vec::new(), index: None };
        core::mem::swap(self, &mut table);
        let Self { entries, hashes, index } = table;
        let mut entries = entries;
        let mut hashes = hashes;
        let ghost hs = hashes@;
        let mut index = match index {
            Some(index) => index,
            None => {
                proof { assert(hs =~= Seq::<u64>::empty()); }
                Buckets::new(16)
            },
        };
        let uid = entries.len();
        entries.push((key, value));
        hashes.push(h);
        proof { vstd::std_specs::vec::axiom_spec_len(&hashes); }
        index.insert(h, uid, Ghost(hs));
        *self = Self { entries, hashes, index: Some(index) };
    }

    /// Reserves room for one more entry; the test-util checkpoint injects allocation failures.
    #[verifier::external_body]
    pub fn reserve_one(&mut self) -> (result: Result<(), HistoryError>)
        ensures final(self)@ == old(self)@,
            result is Err ==> result == Err(HistoryError::AllocationFailed),
    {
        #[cfg(any(test, feature = "test-util"))]
        junco_core::observation::reservation_checkpoint()
            .map_err(|_| HistoryError::AllocationFailed)?;
        self.entries.try_reserve(1).map_err(|_| HistoryError::AllocationFailed)?;
        self.hashes.try_reserve(1).map_err(|_| HistoryError::AllocationFailed)
    }
}

impl<K: Eq + KeyHash, V: Copy> KeyedMap<K, V> {
    #[allow(clippy::manual_map)]
    pub fn lookup(&self, key: &K) -> (r: Option<V>)
        ensures key_laws::<K>() ==> match r {
            Some(v) => exists|i: int| 0 <= i < self@.len() && self@[i].1 == v
                && key.eq_spec(&self@[i].0),
            None => forall|i: int| 0 <= i < self@.len() ==> !key.eq_spec(&self@[i].0),
        },
    {
        match self.find(key) {
            Some(i) => Some(self.entries[i].1),
            None => None,
        }
    }
}

impl<K: Eq + KeyHash, T> KeyedMap<K, Vec<T>> {
    #[allow(non_shorthand_field_patterns)]
    pub fn push_at(&mut self, i: usize, value: T)
        requires i < old(self)@.len(),
        ensures
            final(self)@.len() == old(self)@.len(),
            final(self)@[i as int].0 == old(self)@[i as int].0,
            final(self)@[i as int].1@ == old(self)@[i as int].1@.push(value),
            forall|j: int| 0 <= j < final(self)@.len() && j != i ==> final(self)@[j] == old(self)@[j],
    {
        proof { use_type_invariant(&*self); }
        let mut table = Self { entries: Vec::new(), hashes: Vec::new(), index: None };
        core::mem::swap(self, &mut table);
        let Self { entries, hashes, index } = table;
        let mut entries = entries;
        entries[i].1.push(value);
        *self = Self { entries, hashes, index };
    }
}

} // verus!
