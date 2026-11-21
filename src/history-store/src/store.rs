// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

//! Process-wide exact-byte identities and synchronized numeric histories.
//! Issuance, bidirectional persistent byte bindings, and lock-local record transactions are checked.
//! Const/static installation, reference identity, and lock/guard mechanics remain
//! narrow native leaves; concurrent observations use retained lifecycle snapshots.

use crate::graph::allocation;
use crate::history::StoredHistory;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::sync::Arc;
use alloc::vec::Vec;
use history_syntax::{Component, MAX_ARITY};
use junco_core::errors::HistoryError;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_assumptions::{arc_identity, reference_identity};
#[cfg(feature = "std")]
use parking_lot::{Mutex, RwLock, RwLockReadGuard};
#[cfg(not(feature = "std"))]
use spin::{Mutex, RwLock, RwLockReadGuard};
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::option::OptionAdditionalFns;

// Per-arity byte domains share one process-wide numeric issuance authority.
static STORES: spin::Mutex<Option<StoreRegistry>> = spin::Mutex::new(None);

struct StoreRegistry {
    authorities: Arc<NumericAuthorities>,
    stores: [Option<Arc<HistoryStore>>; MAX_ARITY],
}

#[cfg(verus_keep_ghost)]
verus! {

impl View for Domain {
    type V = DomainView;
    closed spec fn view(&self) -> DomainView {
        DomainView { paths: path_map(self.paths), ids: self.ids@ }
    }
}

}

/// An inline numeric event; identity and hashing use only its active coordinates.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Copy, Debug)]
pub struct Event {
    pub(crate) arity: u8,
    pub(crate) slots: [u64; MAX_ARITY],
}

#[cfg(verus_keep_ghost)]
verus! {
impl Event {
    #[verifier::type_invariant]
    closed spec fn inv(&self) -> bool { self.arity <= MAX_ARITY }
}
}

#[verus_verify]
impl Event {
    #[verus_spec(result => requires values@.len() <= MAX_ARITY,
        ensures result@ == values@.map(|i: int, value: u64| value as nat))]
    pub(crate) fn from_encoded(values: &[u64]) -> Self {
        assert!(values.len() <= MAX_ARITY);
        let mut slots = [0; MAX_ARITY];
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= values@.len() <= MAX_ARITY,
                forall|i: int| 0 <= i < MAX_ARITY ==> slots@[i] ==
                    if i < index { values@[i] } else { 0 },
            decreases values@.len() - index,
        ))]
        while index < values.len() {
            slots[index] = values[index];
            index += 1;
        }
        Self {
            arity: values.len() as u8,
            slots,
        }
    }

    /// Return a coordinate, or zero when the index is outside the active tuple.
    #[verus_spec(result => ensures index < self@.len() ==> result as nat == self@[index as int],
        index >= self@.len() ==> result == 0)]
    pub fn component(&self, index: usize) -> u64 {
        proof! { use_type_invariant(self); }
        if index < self.arity as usize {
            self.slots[index]
        } else {
            0
        }
    }

    #[verus_spec(result => ensures result == self@.len(), result <= MAX_ARITY)]
    pub const fn arity(&self) -> usize {
        proof! { use_type_invariant(self); }
        self.arity as usize
    }
}

#[verus_verify]
impl Clone for Event {
    #[verus_spec(result => ensures result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

#[verus_verify]
impl PartialEq for Event {
    #[verus_spec(result => ensures result == (self@ == other@))]
    fn eq(&self, other: &Self) -> bool {
        proof! { use_type_invariant(self); use_type_invariant(other); }
        if self.arity != other.arity {
            return false;
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= self.arity <= MAX_ARITY, self.arity == other.arity,
                forall|i: int| 0 <= i < index ==> self.slots@[i] == other.slots@[i],
            decreases self.arity - index,
        ))]
        while index < self.arity as usize {
            if self.slots[index] != other.slots[index] {
                proof! { assert(self@[index as int] != other@[index as int]); }
                return false;
            }
            index += 1;
        }
        proof! { assert(self@ =~= other@); }
        true
    }
}
impl Eq for Event {}

impl core::hash::Hash for Event {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        core::hash::Hash::hash(&self.slots[..self.arity as usize], state);
    }
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
struct Domain {
    paths: BTreeMap<Vec<u8>, u64>,
    ids: BTreeSet<u64>,
    #[cfg(verus_keep_ghost)]
    issued: Tracked<Option<ComponentReceipts>>,
    #[cfg(verus_keep_ghost)]
    bindings: Tracked<ByteBindings>,
}

#[verus_verify]
impl Default for Domain {
    #[verus_spec(result => ensures domain_wf(result@), domain_unissued(result), domain_bindings_wf(result))]
    fn default() -> Self {
        proof! { reveal(path_map); reveal(<Domain as View>::view); }
        proof_decl! { let tracked bindings = ByteBindings::empty(); }
        let result = Self {
            paths: BTreeMap::new(),
            ids: BTreeSet::new(),
            #[cfg(verus_keep_ghost)]
            issued: verus_exec_expr! { Tracked(None) },
            #[cfg(verus_keep_ghost)]
            bindings: verus_exec_expr! { Tracked(bindings) },
        };
        proof! {
            reveal(domain_bindings_wf);
            assert(path_map(result.paths) =~= Map::<Seq<u8>, nat>::empty());
            assert(result@.paths == Map::<Seq<u8>, nat>::empty());
            assert(result@.ids == Set::<u64>::empty());
            assert(domain_bindings_wf(result));
        }
        result
    }
}

#[verus_verify]
impl Domain {
    // Allocation fails without changing the counter; zero is never issued.
    #[verus_verify]
    #[verus_spec(result => ensures
        match result {
            Ok(id) => id == *old(next) && id > 0 && *final(next) == id + 1,
            Err(error) => *final(next) == *old(next)
                && (*old(next) == 0 || *old(next) == u64::MAX)
                && error == HistoryError::IdExhausted { domain },
        }
    )]
    const fn allocate_id(next: &mut u64, domain: &'static str) -> Result<u64, HistoryError> {
        let id = *next;
        if id == 0 {
            return Err(HistoryError::IdExhausted { domain });
        }
        let following = match id.checked_add(1) {
            Some(following) => following,
            None => return Err(HistoryError::IdExhausted { domain }),
        };
        *next = following;
        Ok(id)
    }

    // Borrowed byte-slice keys and native BTree ordering are outside the pinned vstd model.
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures match result {
        Some(id) => path_map(*paths).contains_key(path@)
            && path_map(*paths)[path@] == id as nat,
        None => !path_map(*paths).contains_key(path@),
    })]
    #[inline]
    fn path_lookup(paths: &BTreeMap<Vec<u8>, u64>, path: &[u8]) -> Option<u64> {
        paths.get(path).copied()
    }

    #[verus_verify(external_body)]
    #[verus_spec(ensures path_map(*final(paths)) == path_map(*old(paths)).insert(
        path@, id as nat))]
    #[inline]
    fn path_insert(paths: &mut BTreeMap<Vec<u8>, u64>, path: Vec<u8>, id: u64) {
        paths.insert(path, id);
    }

    #[verus_verify(external_body)]
    #[verus_spec(ensures path_map(*final(paths)) == path_map(*old(paths)).remove(
        path@))]
    #[inline]
    fn path_remove(paths: &mut BTreeMap<Vec<u8>, u64>, path: &[u8]) {
        paths.remove(path);
    }

    #[verus_spec(result =>
        requires domain_wf(old(self)@), domain_provenance(*old(self), index as int), index < MAX_ARITY,
            domain_bindings_wf(*old(self)),
            numeric_store_wf(*numeric_store),
        ensures domain_wf(final(self)@), domain_provenance(*final(self), index as int),
            domain_bindings_wf(*final(self)),
            domain_forward_authority(*final(self)) == domain_forward_authority(*old(self)),
            domain_reverse_authority(*final(self)) == domain_reverse_authority(*old(self)),
            result is Err ==> final(self)@ == old(self)@,
            result is Err ==> final(self).issued@ == old(self).issued@,
            result is Err ==> final(self).bindings@ == old(self).bindings@,
            result matches Ok((id, receipt)) ==> receipt@.valid()
                && receipt@.path() == path@ && receipt@.id() == id
                && receipt@.coordinate_authority() == coordinate_authority(index as int)
                && receipt@.forward_authority() == domain_forward_authority(*old(self))
                && receipt@.reverse_authority() == domain_reverse_authority(*old(self))
                && 0 < id < u64::MAX
                && final(self)@.paths == old(self)@.paths.insert(path@, id as nat),
            result matches Ok((id, receipt)) ==> final(self)@.ids == old(self)@.ids.insert(id),
            old(self)@.paths.contains_key(path@) ==> result is Ok
                && final(self)@ == old(self)@
                && result->Ok_0.0 as nat == old(self)@.paths[path@],
            forall|old_path: Seq<u8>| old(self)@.paths.contains_key(old_path)
                ==> final(self)@.paths.contains_key(old_path)
                    && final(self)@.paths[old_path] == old(self)@.paths[old_path],
    )]
    fn intern<L: Limits>(
        &mut self,
        path: &[u8],
        index: usize,
        domain: &'static str,
        limits: &mut L,
        numeric_store: &HistoryStore,
    ) -> Result<(u64, Tracked<ByteBindingReceipt>), HistoryError> {
        proof! { reveal(<Domain as View>::view); reveal(domain_wf); }
        proof_decl! { let ghost entry = self@; }
        proof_decl! { let ghost entry_bindings = self.bindings@; }
        if let Some(id) = Self::path_lookup(&self.paths, path) {
            proof_decl! { let tracked binding; }
            proof! {
                reveal(domain_bindings_wf);
                reveal(domain_provenance);
                let key = path@;
                assert(self@.paths.contains_key(key));
                assert(self.bindings@.forward@[key] == id);
                assert(self@.ids.contains(id));
                assert(self.bindings@.reverse@[id] == key);
                let tracked bindings = self.bindings.borrow();
                bindings.paths.agree(&bindings.forward);
                bindings.ids.agree(&bindings.reverse);
                let tracked mut paths = bindings.paths.duplicate();
                let tracked forward = paths.split_points_to(key);
                forward.agree(&bindings.forward);
                assert(forward@ == (key, id));
                let tracked mut ids = bindings.ids.duplicate();
                let tracked reverse = ids.split_points_to(id);
                reverse.agree(&bindings.reverse);
                assert(reverse@ == (id, key));
                assert(self.issued@ is Some);
                let tracked held = self.issued.borrow().tracked_borrow();
                assert(held.id() == coordinate_authority(index as int));
                assert(held@.contains_key(id));
                assert(held@[id] == ComponentIssuer::Byte);
                let tracked mut issued = held.duplicate();
                let tracked issuer = issued.split_points_to(id);
                assert(issuer@ == (id, ComponentIssuer::Byte));
                binding = ByteBindingReceipt { forward, reverse, issuer };
            }
            return Ok((id, verus_exec_expr! { Tracked(binding) }));
        }
        let mut owned = Vec::new();
        allocation(owned.try_reserve(path.len()))?;
        owned.extend_from_slice(path);
        limits.enforce_memory()?;
        proof_decl! { let tracked prior = match self.issued.borrow() { Some(previous) => Some(previous), None => None }; }
        proof_decl! { let ghost prior_view = prior; }
        let (id, _receipt) = numeric_store.allocate_after(
            index,
            domain,
            0,
            verus_exec_expr! { Ghost(ComponentIssuer::Byte) },
            verus_exec_expr! { Tracked(prior) },
        )?;
        proof! {
            assert(owned@ == path@);
            assert(entry.ids == self.ids@);
            assert forall|old_path: Seq<u8>| entry.paths.contains_key(old_path)
                implies 0 < entry.paths[old_path] < id as nat by {
                let old_id = entry.paths[old_path] as u64;
                assert(old_id as nat == entry.paths[old_path]);
                assert(entry.paths.values().contains(old_id as nat));
                assert(entry.ids.contains(old_id) <==> entry.paths.values().contains(old_id as nat));
                assert(self.ids@.contains(old_id));
                match prior_view {
                    Some(previous) => { assert(previous@.contains_key(old_id)); }
                    None => { assert(self.ids@ == Set::<u64>::empty()); }
                }
                assert(old_id < id);
            }
            assert(!entry.ids.contains(id));
            assert(junco_core::verify::history_specs::interner_wf(entry.paths, id as nat));
            junco_core::verify::history_specs::lemma_interner_fresh_nonreuse(entry.paths, id as nat,
                path@, id as nat);
        }
        Self::path_insert(&mut self.paths, owned, id);
        self.ids.insert(id);
        if let Err(error) = limits.enforce_memory() {
            // Roll back the mapping, never the allocator: an issued ID must never be reused.
            Self::path_remove(&mut self.paths, path);
            self.ids.remove(&id);
            proof! {
                assert(self@.paths =~= entry.paths);
                assert(self@.ids =~= entry.ids);
            }
            return Err(error.into());
        }
        proof_decl! { let tracked binding; }
        proof! {
            junco_core::verify::history_specs::lemma_interner_raise_frontier(self@.paths,
                id as nat + 1, u64::MAX as nat);
            assert forall|known_id: u64| self.ids@.contains(known_id)
                <==> self@.paths.values().contains(known_id as nat) by {
                let key = path@;
                let updated = entry.paths.insert(key, id as nat);
                if updated.values().contains(known_id as nat) {
                    let witness = choose|p: Seq<u8>| updated.contains_key(p)
                        && updated[p] == known_id as nat;
                    if witness != key {
                        assert(entry.paths.contains_key(witness));
                        assert(entry.paths[witness] == known_id as nat);
                        assert(entry.paths.values().contains(known_id as nat));
                    }
                }
                if entry.paths.values().contains(known_id as nat) {
                    let witness = choose|p: Seq<u8>| entry.paths.contains_key(p)
                        && entry.paths[p] == known_id as nat;
                    assert(witness != key);
                    assert(updated.contains_key(witness));
                    assert(updated[witness] == known_id as nat);
                    assert(updated.values().contains(known_id as nat));
                }
                if known_id == id {
                    assert(updated.contains_key(key));
                    assert(updated[key] == known_id as nat);
                    assert(updated.values().contains(known_id as nat));
                }
            }
            let key = path@;
            let tracked forward = self.bindings.borrow_mut().forward.insert(key, id).persist();
            let tracked reverse = self.bindings.borrow_mut().reverse.insert(id, key).persist();
            self.bindings.borrow_mut().paths.combine_points_to(forward.duplicate());
            self.bindings.borrow_mut().ids.combine_points_to(reverse.duplicate());
            let tracked receipt = _receipt.get();
            let tracked mut held = None;
            vstd::modes::tracked_swap(self.issued.borrow_mut(), &mut held);
            let tracked updated = match held {
                None => receipt.duplicate().submap(),
                Some(mut previous) => { previous.combine_points_to(receipt.duplicate()); previous },
            };
            *self.issued.borrow_mut() = Some(updated);
            binding = ByteBindingReceipt { forward, reverse, issuer: receipt };
            assert forall|p: Seq<u8>| self@.paths.contains_key(p)
                implies self.bindings@.forward@[p] as nat == self@.paths[p] by {
                if p != key { assert(entry.paths.contains_key(p)); }
            }
            assert forall|known: u64| self@.ids.contains(known)
                implies self@.paths.contains_key(self.bindings@.reverse@[known])
                    && self@.paths[self.bindings@.reverse@[known]] == known as nat by {
                if known != id {
                    assert(entry.ids.contains(known));
                    let p = entry_bindings.reverse@[known];
                    assert(entry.paths.contains_key(p));
                    assert(p != key);
                }
            }
            assert forall|p: Seq<u8>| self@.paths.contains_key(p)
                implies self.bindings@.reverse@.contains_key(self.bindings@.forward@[p])
                    && self.bindings@.reverse@[self.bindings@.forward@[p]] == p by {
                if p != key {
                    assert(entry.paths.contains_key(p));
                    assert(entry_bindings.forward@[p] != id);
                }
            }
        }
        Ok((id, verus_exec_expr! { Tracked(binding) }))
    }

    #[verus_spec(result => requires domain_wf(self@),
        ensures (result is Ok) == self.ids@.contains(id),
            result is Ok ==> result == Ok(()),
            result is Ok ==> self@.paths.values().contains(id as nat),
            result is Err ==> result == Err(HistoryError::UnknownId { domain, id }))]
    fn validate(&self, id: u64, domain: &'static str) -> Result<(), HistoryError> {
        proof! {
            reveal(<Domain as View>::view);
            reveal(domain_wf);
            assert(self@.ids.contains(id) <==> self@.paths.values().contains(id as nat));
        }
        if self.ids.contains(&id) {
            Ok(())
        } else {
            Err(HistoryError::UnknownId { domain, id })
        }
    }
}

/// Advance the process history-key counter, failing at `usize::MAX` without changing it.
#[verus_verify]
#[verus_spec(result =>
    requires 0 < *old(next),
    ensures match result {
        Ok(id) => id == *old(next) && 0 < id < usize::MAX && *final(next) == id + 1,
        Err(error) => *old(next) == usize::MAX && *final(next) == *old(next)
            && error == HistoryError::IdExhausted { domain: "history" },
    }
)]
fn next_history_id(next: &mut usize) -> Result<usize, HistoryError> {
    let id = *next;
    let following = match id.checked_add(1) {
        Some(following) => following,
        None => return Err(HistoryError::IdExhausted { domain: "history" }),
    };
    *next = following;
    Ok(id)
}

// Process authorities are embedded in the live allocator mutex payloads.
// Erased Ghost/Tracked signatures retain issuer and receipt types, but not their proof-only contents.
pub(crate) type ComponentIdReceipt =
    vstd::resource::map::GhostPersistentPointsTo<u64, ComponentIssuer>;
pub(crate) type ComponentReceipts =
    vstd::resource::map::GhostPersistentSubmap<u64, ComponentIssuer>;
pub(crate) type HistoryKeyReceipt =
    vstd::resource::map::GhostPersistentPointsTo<usize, HistoryIssuer>;

verus! {
pub(crate) enum ComponentIssuer {
    #[cfg(verus_keep_ghost)]
    Byte,
    #[cfg(verus_keep_ghost)]
    Typed(vstd::resource::Loc),
}
pub(crate) enum HistoryIssuer {
    #[cfg(verus_keep_ghost)]
    Byte,
    #[cfg(verus_keep_ghost)]
    Typed { store: vstd::resource::Loc, lifecycle: vstd::resource::Loc },
}

#[cfg(verus_keep_ghost)]
tracked struct ByteBindings {
    forward: vstd::resource::map::GhostMapAuth<Seq<u8>, u64>,
    reverse: vstd::resource::map::GhostMapAuth<u64, Seq<u8>>,
    paths: vstd::resource::map::GhostPersistentSubmap<Seq<u8>, u64>,
    ids: vstd::resource::map::GhostPersistentSubmap<u64, Seq<u8>>,
}
#[cfg(verus_keep_ghost)]
impl ByteBindings {
    proof fn empty() -> (tracked result: Self)
        ensures result.forward@ == Map::empty(), result.reverse@ == Map::empty(),
            result.paths@ == Map::empty(), result.ids@ == Map::empty(),
            result.paths.id() == result.forward.id(), result.ids.id() == result.reverse.id(),
    {
        let tracked (forward, paths) = vstd::resource::map::GhostMapAuth::new(Map::empty());
        let tracked (reverse, ids) = vstd::resource::map::GhostMapAuth::new(Map::empty());
        Self { forward, reverse, paths: paths.persist(), ids: ids.persist() }
    }
}

/// Persistent evidence of one byte-path binding; no native map or allocation is added.
pub tracked struct ByteBindingReceipt {
    #[cfg(verus_keep_ghost)]
    forward: vstd::resource::map::GhostPersistentPointsTo<Seq<u8>, u64>,
    #[cfg(verus_keep_ghost)]
    reverse: vstd::resource::map::GhostPersistentPointsTo<u64, Seq<u8>>,
    #[cfg(verus_keep_ghost)]
    issuer: ComponentIdReceipt,
}

impl ByteBindingReceipt {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.forward.key() == self.reverse.value() && self.forward.value() == self.reverse.key()
            && self.issuer.key() == self.forward.value() && self.issuer.value() == ComponentIssuer::Byte
    }
    pub closed spec fn valid(self) -> bool { self.inv() }
    pub closed spec fn path(self) -> Seq<u8> { self.forward.key() }
    pub closed spec fn id(self) -> u64 { self.forward.value() }
    pub closed spec fn coordinate_authority(self) -> vstd::resource::Loc { self.issuer.id() }
    pub closed spec fn forward_authority(self) -> vstd::resource::Loc { self.forward.id() }
    pub closed spec fn reverse_authority(self) -> vstd::resource::Loc { self.reverse.id() }

    pub(crate) proof fn issuer_receipt(tracked &self) -> (tracked result: ComponentIdReceipt)
        ensures result.id() == self.coordinate_authority(), result@ == (self.id(), ComponentIssuer::Byte),
            result.key() == self.id(), result.value() == ComponentIssuer::Byte,
    {
        use_type_invariant(self);
        self.issuer.duplicate()
    }
}

pub proof fn lemma_byte_binding_reuse(tracked left: &ByteBindingReceipt, tracked right: &ByteBindingReceipt)
    requires left.forward_authority() == right.forward_authority(),
        left.reverse_authority() == right.reverse_authority(), left.path() == right.path(),
    ensures left.id() == right.id(),
{
    let tracked mut forward = left.forward.duplicate();
    forward.intersection_agrees(&right.forward);
}

pub proof fn lemma_byte_binding_separation(tracked left: &ByteBindingReceipt, tracked right: &ByteBindingReceipt)
    requires left.forward_authority() == right.forward_authority(),
        left.reverse_authority() == right.reverse_authority(), left.path() != right.path(),
    ensures left.id() != right.id(),
{
    use_type_invariant(left); use_type_invariant(right);
    let tracked mut reverse = left.reverse.duplicate();
    reverse.intersection_agrees(&right.reverse);
}

#[cfg(verus_keep_ghost)]
pub(crate) tracked struct CoordinateAuthorities {
    pub(crate) entries: Seq<vstd::resource::map::GhostMapAuth<u64, ComponentIssuer>>,
}
#[verifier::external_derive]
#[derive(Debug)]
pub(crate) struct CoordinateState {
    pub(crate) next: [u64; MAX_ARITY],
    #[cfg(verus_keep_ghost)]
    pub(crate) authorities: Tracked<CoordinateAuthorities>,
}
#[verifier::external_derive]
#[derive(Debug)]
pub(crate) struct HistoryKeyState {
    pub(crate) next: usize,
    #[cfg(verus_keep_ghost)]
    pub(crate) issued: Tracked<vstd::resource::map::GhostMapAuth<usize, HistoryIssuer>>,
}
#[cfg(any(test, verus_keep_ghost))]
impl CoordinateState {
    pub(crate) fn new() -> (result: Self)
        ensures coordinate_wf(result), result.next@ == Seq::new(MAX_ARITY as nat, |i: int| 1u64),
    {
        let tracked authorities = empty_coordinate_authorities(MAX_ARITY as nat);
        Self { next: [1; MAX_ARITY], #[cfg(verus_keep_ghost)] authorities: Tracked(authorities) }
    }
}
#[cfg(any(test, verus_keep_ghost))]
impl HistoryKeyState {
    pub(crate) fn new() -> (result: Self)
        ensures history_key_wf(result), result.next == 1,
    {
        let tracked issued = empty_history_authority();
        Self { next: 1, #[cfg(verus_keep_ghost)] issued: Tracked(issued) }
    }
}

pub(crate) fn allocate_coordinate_state(state: &mut CoordinateState, index: usize,
    domain: &'static str, last: u64, Ghost(issuer): Ghost<ComponentIssuer>,
    Tracked(prior): Tracked<Option<&ComponentReceipts>>)
    -> (result: Result<(u64, Tracked<ComponentIdReceipt>), HistoryError>)
    requires coordinate_wf(*old(state)), coordinate_prior(*old(state), index, prior),
    ensures coordinate_result(*old(state), *final(state), index, domain, last, issuer, prior, result),
        result != Err(HistoryError::WrongHistoryOwner),
{
    if index >= MAX_ARITY { return Err(HistoryError::invariant("invalid identity domain")); }
    let ghost entry = *state;
    let ghost before = coordinate_map(*state, index as int);
    proof {
        if let Some(previous) = prior {
            previous.agree(state.authorities.borrow().entries.tracked_borrow(index as int));
            if previous@.contains_key(last) {
                assert(before.contains_key(last));
                assert(last < entry.next@[index as int]);
            }
        }
    }
    let mut next = state.next[index];
    let allocated = Domain::allocate_id(&mut next, domain);
    state.next[index] = next;
    proof {
        if allocated is Err {
            assert(state.next@ =~= entry.next@);
            assert(state.next == entry.next);
        }
    }
    let id = allocated?;
    let tracked receipt;
    proof {
        assert(!before.contains_key(id));
        receipt = state.authorities.borrow_mut().entries.tracked_borrow_mut(index as int)
            .insert(id, issuer).persist();
        assert forall|d: int, key: u64| 0 <= d < MAX_ARITY implies
            (coordinate_map(*state, d).contains_key(key) <==> 0 < key < state.next@[d]) by {
            if d == index { assert(coordinate_map(*state, d) == before.insert(id, issuer)); }
            else {
                assert(coordinate_map(*state, d) == coordinate_map(entry, d));
                assert(state.next@[d] == entry.next@[d]);
                assert(coordinate_map(entry, d).contains_key(key) <==> 0 < key < entry.next@[d]);
            }
        }
        if let Some(previous) = prior {
            assert forall|key: u64| previous@.contains_key(key) implies key < id by {
                assert(before.contains_key(key));
            }
        }
    }
    proof {
        if last == 0 || (match prior { Some(previous) => previous@.contains_key(last), None => false }) {
            assert(last < id);
        }
    }
    if id <= last { return Err(HistoryError::invariant("identity allocator moved backwards")); }
    Ok((id, Tracked(receipt)))
}

pub(crate) fn allocate_history_state(state: &mut HistoryKeyState, last: usize,
    Ghost(issuer): Ghost<HistoryIssuer>)
    -> (result: Result<(usize, Tracked<HistoryKeyReceipt>), HistoryError>)
    requires history_key_wf(*old(state)),
    ensures history_key_result(*old(state), *final(state), last, issuer, result),
        last < old(state).next ==> (result matches Err(error) ==>
            error == HistoryError::IdExhausted { domain: "history" }),
{
    if last == usize::MAX { return Err(HistoryError::IdExhausted { domain: "history" }); }
    let ghost before = (state.issued@)@;
    let id = next_history_id(&mut state.next)?;
    let tracked receipt;
    proof {
        assert(!before.contains_key(id));
        receipt = state.issued.borrow_mut().insert(id, issuer).persist();
        assert forall|key: usize| (state.issued@)@.contains_key(key)
            <==> 0 < key < state.next by {
            if key != id { assert((state.issued@)@.contains_key(key) == before.contains_key(key)); }
        }
    }
    if id <= last { return Err(HistoryError::invariant("history identity allocator moved backwards")); }
    Ok((id, Tracked(receipt)))
}
#[verifier::external_body]
#[verifier::external_derive]
#[repr(transparent)]
#[derive(Debug)]
pub(crate) struct NativeCoordinates { pub(crate) inner: spin::Mutex<CoordinateState> }
impl NativeCoordinates {
    #[verifier::external_body]
    pub(crate) const fn new() -> (result: Self)
        ensures coordinates_mutex_valid(result),
    {
        let tracked authorities = empty_coordinate_authorities(MAX_ARITY as nat);
        let state = CoordinateState { next: [1; MAX_ARITY], #[cfg(verus_keep_ghost)] authorities: Tracked(authorities) };
        Self { inner: spin::Mutex::new(state) }
    }
    // Only installation and mutex/callback fidelity are native leaves.
    #[verifier::external_body]
    pub(crate) fn with_state<R, Context, F: FnOnce(&mut CoordinateState, Context) -> R>(
        &self, context: Context, operation: F) -> (result: R)
        requires coordinates_mutex_valid(*self),
            forall|borrow: &mut CoordinateState| coordinates_acquired(mut_ref_current(borrow), *self)
                ==> call_requires(operation, (borrow, context)),
            forall|borrow: &mut CoordinateState, output: R|
                coordinates_acquired(mut_ref_current(borrow), *self) && call_ensures(operation, (borrow, context), output)
                    ==> coordinate_frame(mut_ref_current(borrow), mut_ref_future(borrow)),
        ensures exists|borrow: &mut CoordinateState|
            coordinates_acquired(mut_ref_current(borrow), *self)
                && coordinate_frame(mut_ref_current(borrow), mut_ref_future(borrow))
                && call_ensures(operation, (borrow, context), result),
    {
        let mut state = self.inner.lock();
        operation(&mut state, context)
    }
}
#[verifier::external_body]
#[verifier::external_derive]
#[repr(transparent)]
#[derive(Debug)]
pub(crate) struct NativeHistoryKeys { pub(crate) inner: spin::Mutex<HistoryKeyState> }
impl NativeHistoryKeys {
    #[verifier::external_body]
    pub(crate) const fn new() -> (result: Self)
        ensures history_keys_mutex_valid(result),
    {
        let tracked issued = empty_history_authority();
        let state = HistoryKeyState { next: 1, #[cfg(verus_keep_ghost)] issued: Tracked(issued) };
        Self { inner: spin::Mutex::new(state) }
    }
    // Only installation and mutex/callback fidelity are native leaves.
    #[verifier::external_body]
    pub(crate) fn with_state<R, Context, F: FnOnce(&mut HistoryKeyState, Context) -> R>(
        &self, context: Context, operation: F) -> (result: R)
        requires history_keys_mutex_valid(*self),
            forall|borrow: &mut HistoryKeyState| history_keys_acquired(mut_ref_current(borrow), *self)
                ==> call_requires(operation, (borrow, context)),
            forall|borrow: &mut HistoryKeyState, output: R|
                history_keys_acquired(mut_ref_current(borrow), *self) && call_ensures(operation, (borrow, context), output)
                    ==> history_key_frame(mut_ref_current(borrow), mut_ref_future(borrow)),
        ensures exists|borrow: &mut HistoryKeyState|
            history_keys_acquired(mut_ref_current(borrow), *self)
                && history_key_frame(mut_ref_current(borrow), mut_ref_future(borrow))
                && call_ensures(operation, (borrow, context), result),
    {
        let mut state = self.inner.lock();
        operation(&mut state, context)
    }
}
}

#[verus_verify]
#[verus_verify(external_body)]
#[verus_verify(external_derive)]
#[cfg_attr(not(verus_keep_ghost), repr(transparent))]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub(crate) struct NativeDomain {
    inner: Mutex<Domain>,
    #[cfg(verus_keep_ghost)]
    index: Ghost<usize>,
}
#[verus_verify]
impl NativeDomain {
    #[verus_spec(result => requires index@ < MAX_ARITY,
        ensures native_domain_valid(result), native_domain_index(result) == index@ as int)]
    fn new(index: Ghost<usize>) -> Self {
        let domain = Domain::default();
        Self::place(domain, index)
    }
    // Only placement of the checked payload in the native mutex is trusted.
    #[verus_verify(external_body)]
    #[verus_spec(result => requires _index@ < MAX_ARITY, domain_wf(domain@), domain_unissued(domain),
        domain_bindings_wf(domain),
        ensures native_domain_valid(result), native_domain_index(result) == _index@ as int,
            native_domain_forward_authority(result) == domain_forward_authority(domain),
            native_domain_reverse_authority(result) == domain_reverse_authority(domain))]
    fn place(domain: Domain, _index: Ghost<usize>) -> Self {
        Self {
            inner: Mutex::new(domain),
            #[cfg(verus_keep_ghost)]
            index: _index,
        }
    }
    #[verus_verify(external_body)]
    #[verus_spec(result => requires native_domain_valid(*self),
        forall|borrow: &mut Domain| domain_acquired(mut_ref_current(borrow), *self)
            ==> call_requires(operation, (borrow, context)),
        forall|borrow: &mut Domain, output: R| domain_acquired(mut_ref_current(borrow), *self)
            && call_ensures(operation, (borrow, context), output)
            ==> domain_acquired(mut_ref_future(borrow), *self),
        ensures exists|borrow: &mut Domain| domain_acquired(mut_ref_current(borrow), *self)
            && domain_acquired(mut_ref_future(borrow), *self)
            && call_ensures(operation, (borrow, context), result))]
    fn with_domain<R, Context, F: FnOnce(&mut Domain, Context) -> R>(
        &self,
        context: Context,
        operation: F,
    ) -> R {
        let mut domain = self.inner.lock();
        operation(&mut domain, context)
    }
}

#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub(crate) struct RecordCell {
    pub(crate) stored: StoredHistory,
    #[cfg(verus_keep_ghost)]
    pub(crate) lifecycle: Tracked<crate::history::verify::Lifecycle>,
}

#[verus_verify]
impl RecordCell {
    #[verus_spec(result => requires old(self).lifecycle@.wf(),
        old(self).lifecycle@.state() == old(self).stored@, events@.len() > 0,
        ensures crate::history::verify::stored_append_result(old(self).stored, final(self).stored, events@, result),
            result != Err(HistoryError::WrongHistoryOwner),
            result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
            final(self).lifecycle@.wf(), final(self).lifecycle@.state() == final(self).stored@,
            final(self).lifecycle@.id() == old(self).lifecycle@.id(),
            result is Err ==> final(self).lifecycle@ == old(self).lifecycle@)]
    fn append_events<L: Limits>(
        &mut self,
        events: &[Event],
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<(), HistoryError> {
        proof_decl! { let ghost before = self.stored; }
        let result = self.stored.append_events(events, limits, world);
        proof! {
            crate::history::lemma_stored_history_view(before);
            crate::history::lemma_stored_history_view(self.stored);
            if let Ok(()) = result {
                self.lifecycle.borrow_mut().advance(self.stored@);
            } else {
                assert(self.stored@ == before@);
            }
        }
        result
    }

    #[verus_spec(result => requires old(self).lifecycle@.wf(),
        old(self).lifecycle@.state() == old(self).stored@,
        ensures crate::history::verify::stored_truncate_result(old(self).stored, final(self).stored, len, result),
            final(self).lifecycle@.wf(), final(self).lifecycle@.state() == final(self).stored@,
            final(self).lifecycle@.id() == old(self).lifecycle@.id(),
            (result is Err || len >= old(self).stored@.events.len())
                ==> final(self).lifecycle@ == old(self).lifecycle@)]
    fn truncate_events(&mut self, len: usize) -> Result<(), HistoryError> {
        proof_decl! { let ghost before = self.stored; }
        proof_decl! { let ghost previous = self.stored@.events.len(); }
        let result = self.stored.truncate_events(len);
        proof! {
            crate::history::lemma_stored_history_view(before);
            crate::history::lemma_stored_history_view(self.stored);
            if let Ok(()) = result {
                if len < previous { self.lifecycle.borrow_mut().advance(self.stored@); }
            }
        }
        result
    }
}

#[verus_verify(external_body)]
#[verus_verify(external_derive)]
#[repr(transparent)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub(crate) struct NativeRecord {
    pub(crate) inner: Arc<RwLock<RecordCell>>,
}
#[verus_verify]
impl NativeRecord {
    #[cfg(verus_keep_ghost)]
    verus! {
        pub(crate) uninterp spec fn record_id(self) -> usize;
        pub(crate) uninterp spec fn lifecycle_id(self) -> vstd::resource::Loc;
    }

    #[verus_spec(result => ensures record_valid(result),
        result.record_id() == stored.spec_id(), record_installed(result, stored))]
    fn new(stored: StoredHistory) -> Self {
        proof! { crate::history::lemma_stored_history_view(stored); }
        proof_decl! { let tracked lifecycle = crate::history::verify::Lifecycle::new(stored@); }
        Self::place_cell(RecordCell {
            stored,
            #[cfg(verus_keep_ghost)]
            lifecycle: verus_exec_expr! { Tracked(lifecycle) },
        })
    }

    // Native placement publishes only the supplied checked cell and its lock invariant.
    #[verus_verify(external_body)]
    #[verus_spec(result => requires cell.lifecycle@.wf(), cell.lifecycle@.state() == cell.stored@,
        ensures record_valid(result), result.record_id() == cell.stored.spec_id(),
            result.lifecycle_id() == cell.lifecycle@.id(), record_installed(result, cell.stored))]
    fn place_cell(cell: RecordCell) -> Self {
        Self {
            inner: Arc::new(RwLock::new(cell)),
        }
    }

    // Acquisition/release and faithful execution of a checked callback are native.
    #[verus_verify(external_body)]
    #[verus_spec(result => requires record_valid(*self),
        forall|borrow: &mut RecordCell| record_acquired(mut_ref_current(borrow), *self)
            ==> call_requires(operation, (borrow, context)),
        forall|borrow: &mut RecordCell, output: R| record_acquired(mut_ref_current(borrow), *self)
            && call_ensures(operation, (borrow, context), output)
            ==> record_acquired(mut_ref_future(borrow), *self),
        ensures exists|borrow: &mut RecordCell| record_acquired(mut_ref_current(borrow), *self)
            && record_acquired(mut_ref_future(borrow), *self)
            && call_ensures(operation, (borrow, context), result))]
    fn with_record<R, Context, F: FnOnce(&mut RecordCell, Context) -> R>(
        &self,
        context: Context,
        operation: F,
    ) -> R {
        let mut cell = self.inner.write();
        operation(&mut cell, context)
    }
}
#[verus_verify]
impl Clone for NativeRecord {
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures result == *self)]
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}
#[cfg(verus_keep_ghost)]
verus! {
pub mod verify {
    use super::*;
    use vstd::std_specs::option::OptionAdditionalFns;
    pub(crate) uninterp spec fn native_domain_valid(wrapper: NativeDomain) -> bool;
    pub(crate) uninterp spec fn native_domain_index(wrapper: NativeDomain) -> int;
    pub(crate) uninterp spec fn native_domain_forward_authority(wrapper: NativeDomain) -> vstd::resource::Loc;
    pub(crate) uninterp spec fn native_domain_reverse_authority(wrapper: NativeDomain) -> vstd::resource::Loc;
    pub(super) open spec fn domain_acquired(domain: Domain, wrapper: NativeDomain) -> bool {
        domain_wf(domain@) && domain_provenance(domain, native_domain_index(wrapper))
            && domain_bindings_wf(domain)
            && domain_forward_authority(domain) == native_domain_forward_authority(wrapper)
            && domain_reverse_authority(domain) == native_domain_reverse_authority(wrapper)
    }
    pub(crate) uninterp spec fn record_valid(record: NativeRecord) -> bool;
    pub open(crate) spec fn record_acquired(cell: RecordCell, record: NativeRecord) -> bool {
        cell.lifecycle@.wf() && cell.lifecycle@.state() == cell.stored@
            && cell.stored.spec_id() == record.record_id()
            && cell.lifecycle@.id() == record.lifecycle_id()
    }
    pub(crate) closed spec fn record_installed(record: NativeRecord, stored: StoredHistory) -> bool {
        exists|borrow: &mut RecordCell| record_acquired(mut_ref_current(borrow), record)
            && mut_ref_current(borrow).stored == stored
    }
    pub open(crate) spec fn handle_index(handle: HistoryHandle) -> usize { handle.index }
    /// Fixed lifecycle resource identity, never a mutable observation of shared contents.
    pub open(crate) spec fn handle_lifecycle_id(handle: HistoryHandle) -> vstd::resource::Loc {
        handle.record.lifecycle_id()
    }
    /// The native referent owned by the handle, independent of its numeric key.
    pub open(crate) spec fn handle_owner_identity(handle: HistoryHandle) -> vstd::resource::Loc {
        arc_identity(handle.owner)
    }
    pub open(crate) spec fn handle_owner(handle: HistoryHandle) -> Arc<HistoryStore> { handle.owner }
    pub open(crate) spec fn handle_wf(handle: HistoryHandle) -> bool {
        numeric_store_wf(*handle.owner) && record_valid(handle.record)
            && handle.record.record_id() == handle.index
            && handle.global_registration@.id() == history_authority()
            && handle.global_registration@@ == (handle.index, HistoryIssuer::Byte)
    }

    /// Initial placement observation, not an assertion about a later unlocked record.
    pub open(crate) spec fn history_created(history: HistoryHandle) -> bool {
        exists|stored: StoredHistory| record_installed(history.record, stored)
            && stored.spec_id() == handle_index(history)
            && crate::history::verify::stored_events(&stored) == Seq::<Event>::empty()
            && stored.spec_revision() == 0
    }
    pub open(crate) spec fn record_matches_handle(record: HistoryRecord, history: HistoryHandle) -> bool {
        record_view(record) == history.record
    }


    /// The actual current/future borrow of one lock acquisition. Other writers may
    /// intervene before or after this transaction, never between these witnesses.
    #[verifier::prophetic]
    pub open(crate) spec fn record_transaction(history: HistoryHandle,
        before: StoredHistory, after: StoredHistory) -> bool {
        exists|borrow: &mut RecordCell| record_acquired(mut_ref_current(borrow), history.record)
            && record_acquired(mut_ref_future(borrow), history.record)
            && mut_ref_current(borrow).stored == before && mut_ref_future(borrow).stored == after
    }

    #[verifier::prophetic]
    pub open(crate) spec fn record_append_observed(history: HistoryHandle, events: Seq<Event>,
        result: Result<(), HistoryError>) -> bool {
        exists|before: StoredHistory, after: StoredHistory| record_transaction(history, before, after)
            && crate::history::verify::stored_append_result(before, after, events, result)
    }

    #[verifier::prophetic]
    pub open(crate) spec fn record_truncate_observed(history: HistoryHandle, len: usize,
        result: Result<(), HistoryError>) -> bool {
        exists|before: StoredHistory, after: StoredHistory| record_transaction(history, before, after)
            && crate::history::verify::stored_truncate_result(before, after, len, result)
    }

    pub(super) open spec fn byte_domain(store: &HistoryStore, index: int) -> NativeDomain {
        store.domains@[index]
    }

    /// Fixed identities, transparent to the owning facade but closed to its callers.
    pub open(super) spec fn byte_coordinate_authority(store: &HistoryStore, index: int) -> vstd::resource::Loc {
        coordinate_ids(store.authorities.coordinates)[index]
    }
    pub open(super) spec fn byte_forward_authority(store: &HistoryStore, index: int) -> vstd::resource::Loc {
        native_domain_forward_authority(byte_domain(store, index))
    }
    pub open(super) spec fn byte_reverse_authority(store: &HistoryStore, index: int) -> vstd::resource::Loc {
        native_domain_reverse_authority(byte_domain(store, index))
    }

    /// The actual current/future borrow from one acquisition of one coordinate lock.
    #[verifier::prophetic]
    pub open(super) spec fn byte_domain_transaction(store: &HistoryStore, index: int,
        before: DomainView, after: DomainView) -> bool {
        0 <= index < store.arity_spec() && exists|borrow: &mut Domain|
            domain_acquired(mut_ref_current(borrow), byte_domain(store, index))
                && domain_acquired(mut_ref_future(borrow), byte_domain(store, index))
                && mut_ref_current(borrow)@ == before && mut_ref_future(borrow)@ == after
    }

    pub open spec fn byte_intern_maps(before: DomainView, after: DomainView,
        path: Seq<u8>, result: Result<u64, HistoryError>) -> bool {
        domain_wf(before) && domain_wf(after) && before.paths.submap_of(after.paths)
            && match result {
                Ok(id) => 0 < id < u64::MAX
                    && after.paths == before.paths.insert(path, id as nat)
                    && after.ids == before.ids.insert(id),
                Err(_) => after == before,
            }
            && (before.paths.contains_key(path)
                ==> result == Ok(before.paths[path] as u64) && after == before)
    }

    #[verifier::prophetic]
    pub open spec fn byte_intern_result(store: &HistoryStore, index: int,
        path: Seq<u8>, result: Result<u64, HistoryError>) -> bool {
        if 0 <= index < store.arity_spec() {
            exists|before: DomainView, after: DomainView| byte_domain_transaction(store, index, before, after)
                && byte_intern_maps(before, after, path, result)
        } else {
            match result { Err(error) => component_index_error(error), Ok(_) => false }
        }
    }

    pub open spec fn byte_binding_result(store: &HistoryStore, index: int,
        path: Seq<u8>, id: u64, receipt: ByteBindingReceipt) -> bool {
        receipt.valid() && receipt.path() == path && receipt.id() == id
            && receipt.coordinate_authority() == byte_coordinate_authority(store, index)
            && receipt.forward_authority() == byte_forward_authority(store, index)
            && receipt.reverse_authority() == byte_reverse_authority(store, index)
    }

    pub proof fn lemma_byte_binding_pair_facts(store: &HistoryStore, index: int,
        left_path: Seq<u8>, left_id: u64, left: ByteBindingReceipt,
        right_path: Seq<u8>, right_id: u64, right: ByteBindingReceipt)
        requires byte_binding_result(store, index, left_path, left_id, left),
            byte_binding_result(store, index, right_path, right_id, right),
        ensures left.path() == left_path, left.id() == left_id,
            right.path() == right_path, right.id() == right_id,
            left.forward_authority() == right.forward_authority(),
            left.reverse_authority() == right.reverse_authority(),
            left.coordinate_authority() == right.coordinate_authority(),
    {}

    /// A read observation of one domain. Coordinates are read independently, never as one snapshot.
    #[verifier::prophetic]
    pub open(super) spec fn byte_validation_observed(store: &HistoryStore, index: int,
        id: u64, known: bool) -> bool {
        exists|view: DomainView| byte_domain_transaction(store, index, view, view)
            && domain_wf(view) && known == view.ids.contains(id)
    }

    pub open spec fn event_arity_error(error: HistoryError) -> bool {
        match error {
            HistoryError::InvalidPolicy { path, message } => path@ == "event"@
                && message == "event arity does not match store",
            _ => false,
        }
    }

    pub open spec fn component_index_error(error: HistoryError) -> bool {
        match error {
            HistoryError::InvalidPolicy { path, message } => path@ == "component"@
                && message == "component index is outside event arity",
            _ => false,
        }
    }

    /// Validation reads coordinates in increasing index order, stopping at the first absent ID.
    #[verifier::prophetic]
    pub open spec fn event_validation_result(store: &HistoryStore, event: Event,
        result: Result<(), HistoryError>) -> bool {
        if event@.len() != store.arity_spec() {
            match result { Err(error) => event_arity_error(error), Ok(_) => false }
        } else {
            (result == Ok(()) && forall|i: int| 0 <= i < event@.len()
                ==> byte_validation_observed(store, i, event@[i] as u64, true))
            || (exists|i: int| 0 <= i < event@.len()
                && (forall|j: int| 0 <= j < i ==> byte_validation_observed(store, j, event@[j] as u64, true))
                && byte_validation_observed(store, i, event@[i] as u64, false)
                && result == Err(HistoryError::UnknownId { domain: "component", id: event@[i] as u64 }))
        }
    }

    pub proof fn lemma_byte_validation_observed(store: &HistoryStore, index: int, id: u64, known: bool)
        requires byte_validation_observed(store, index, id, known),
        ensures exists|view: DomainView| byte_domain_transaction(store, index, view, view)
            && domain_wf(view) && known == view.ids.contains(id),
    { reveal(byte_validation_observed); }

    pub proof fn lemma_event_validation_result_facts(store: &HistoryStore, event: Event,
        result: Result<(), HistoryError>)
        requires event_validation_result(store, event, result),
        ensures result matches Err(error) ==> event_validation_error(event, error),
            result is Ok ==> event@.len() == store.arity_spec()
                && (forall|i: int| 0 <= i < event@.len()
                    ==> byte_validation_observed(store, i, event@[i] as u64, true)),
            result matches Err(HistoryError::UnknownId { domain, id }) ==>
                domain == "component" && event@.len() == store.arity_spec()
                && (exists|i: int| 0 <= i < event@.len() && id == event@[i]
                    && byte_validation_observed(store, i, id, false)
                    && (forall|j: int| 0 <= j < i
                        ==> byte_validation_observed(store, j, event@[j] as u64, true))),
            result matches Err(HistoryError::InvalidPolicy { .. }) ==> event@.len() != store.arity_spec(),
    {
        if let Err(HistoryError::UnknownId { domain, id }) = result {
            let i = choose|i: int| 0 <= i < event@.len()
                && (forall|j: int| 0 <= j < i ==> byte_validation_observed(store, j, event@[j] as u64, true))
                && byte_validation_observed(store, i, event@[i] as u64, false)
                && result == Err(HistoryError::UnknownId { domain: "component", id: event@[i] as u64 });
            assert(event@[i] <= u64::MAX);
            assert(id == event@[i]);
        }
    }

    /// Errors retain the absent numeric coordinate or report an event/store arity mismatch.
    pub open spec fn event_validation_error(event: Event, error: HistoryError) -> bool {
        event_arity_error(error) || exists|i: int| 0 <= i < event@.len()
            && error == (HistoryError::UnknownId { domain: "component", id: event@[i] as u64 })
    }

    #[verifier::prophetic]
    pub open(crate) spec fn append_result(store: &HistoryStore, history: HistoryHandle,
        events: Seq<Event>, result: Result<(), HistoryError>) -> bool {
        if reference_identity(store) != handle_owner_identity(history) {
            result == Err(HistoryError::WrongHistoryOwner)
        } else if events.len() == 0 {
            result == Ok(())
        } else {
            result != Err(HistoryError::WrongHistoryOwner)
                && ((exists|i: int, error: HistoryError| 0 <= i < events.len()
                    && result == Err(error) && event_validation_error(events[i], error))
                    || record_append_observed(history, events, result))
        }
    }

    #[verifier::prophetic]
    pub open(crate) spec fn truncate_result(store: &HistoryStore, history: HistoryHandle,
        len: usize, result: Result<(), HistoryError>) -> bool {
        if reference_identity(store) != handle_owner_identity(history) {
            result == Err(HistoryError::WrongHistoryOwner)
        } else { record_truncate_observed(history, len, result) }
    }

    pub open(crate) spec fn len_result(store: &HistoryStore, history: HistoryHandle,
        result: Result<usize, HistoryError>) -> bool {
        if reference_identity(store) != handle_owner_identity(history) {
            result == Err(HistoryError::WrongHistoryOwner)
        } else {
            exists|record: HistoryRecord, guard: HistoryRecordReadGuard|
                record_view(record) == history.record && record_read_observed(record, guard)
                    && result == Ok(guard.stored_view()@.events.len() as usize)
        }
    }

    pub proof fn lemma_history_created(history: HistoryHandle)
        requires handle_wf(history), history_created(history),
        ensures exists|stored: StoredHistory| stored.spec_id() == handle_index(history)
            && stored@.events == Seq::<language::EventView>::empty() && stored@.revision == 0,
    {
        reveal(history_created);
        let stored = choose|stored: StoredHistory| record_installed(history.record, stored)
            && stored.spec_id() == handle_index(history)
            && crate::history::verify::stored_events(&stored) == Seq::<Event>::empty()
            && stored.spec_revision() == 0;
        crate::history::lemma_stored_history_view(stored);
    }

    pub proof fn lemma_record_transaction_ids(history: HistoryHandle,
        before: StoredHistory, after: StoredHistory)
        requires handle_wf(history), record_transaction(history, before, after),
        ensures before.spec_id() == handle_index(history), after.spec_id() == handle_index(history),
    {}

    pub proof fn lemma_record_append_observed(history: HistoryHandle, events: Seq<Event>,
        result: Result<(), HistoryError>)
        requires handle_wf(history), record_append_observed(history, events, result),
        ensures exists|before: StoredHistory, after: StoredHistory|
            record_transaction(history, before, after)
                && before.spec_id() == handle_index(history) && after.spec_id() == handle_index(history)
                && crate::history::verify::stored_append_result(before, after, events, result),
    {}

    pub proof fn lemma_record_truncate_observed(history: HistoryHandle, len: usize,
        result: Result<(), HistoryError>)
        requires handle_wf(history), record_truncate_observed(history, len, result),
        ensures exists|before: StoredHistory, after: StoredHistory|
            record_transaction(history, before, after)
                && before.spec_id() == handle_index(history) && after.spec_id() == handle_index(history)
                && crate::history::verify::stored_truncate_result(before, after, len, result),
    {}

    pub proof fn lemma_append_result_facts(store: &HistoryStore, history: HistoryHandle,
        events: Seq<Event>, result: Result<(), HistoryError>)
        requires append_result(store, history, events, result),
        ensures (result == Err(HistoryError::WrongHistoryOwner))
            == (reference_identity(store) != handle_owner_identity(history)),
            reference_identity(store) == handle_owner_identity(history) && events.len() == 0
                ==> result == Ok(()),
            events.len() > 0 && result is Ok ==> record_append_observed(history, events, result),
            reference_identity(store) == handle_owner_identity(history) && events.len() > 0
                ==> (exists|i: int, error: HistoryError| 0 <= i < events.len()
                    && result == Err(error) && event_validation_error(events[i], error))
                    || record_append_observed(history, events, result),
    {}

    pub proof fn lemma_truncate_result_facts(store: &HistoryStore, history: HistoryHandle,
        len: usize, result: Result<(), HistoryError>)
        requires truncate_result(store, history, len, result),
        ensures (result == Err(HistoryError::WrongHistoryOwner))
            == (reference_identity(store) != handle_owner_identity(history)),
            reference_identity(store) == handle_owner_identity(history)
                ==> record_truncate_observed(history, len, result),
    {}

    pub proof fn lemma_len_result_facts(store: &HistoryStore, history: HistoryHandle,
        result: Result<usize, HistoryError>)
        requires handle_wf(history), len_result(store, history, result),
        ensures (result is Ok) == (reference_identity(store) == handle_owner_identity(history)),
            result is Err ==> result == Err(HistoryError::WrongHistoryOwner),
            result is Ok ==> exists|guard: HistoryRecordReadGuard| guard.valid()
                && guard.record_id() == handle_index(history)
                && guard.lifecycle_id() == handle_lifecycle_id(history)
                && guard.snapshot_view().id() == handle_lifecycle_id(history)
                && guard.snapshot_view().value() == guard.stored_view()@
                && result == Ok(guard.stored_view()@.events.len() as usize),
    {
        reveal(handle_lifecycle_id);
        reveal(HistoryRecord::record_id);
        reveal(HistoryRecord::lifecycle_id);
        if result is Ok {
            let (record, guard) = choose|record: HistoryRecord, guard: HistoryRecordReadGuard|
                record_view(record) == history.record && record_read_observed(record, guard)
                    && result == Ok(guard.stored_view()@.events.len() as usize);
            guard.lemma_observation();
        }
    }
    pub open(super) spec fn handle_clone_frame(before: HistoryHandle, after: HistoryHandle) -> bool {
        before.owner == after.owner && handle_owner_identity(before) == handle_owner_identity(after)
            && before.index == after.index && before.record == after.record
            && before.global_registration@.id() == after.global_registration@.id()
            && before.global_registration@@ == after.global_registration@@
    }
    pub open(crate) spec fn singleton_valid(arity: nat) -> bool {
        let store = singleton_store(arity);
        1 <= arity <= MAX_ARITY && store.arity_spec() == arity
            && store.domains@.len() == arity
            && store.authorities == numeric_authorities()
            && coordinates_mutex_valid(store.authorities.coordinates)
            && history_keys_mutex_valid(store.authorities.history_keys)
            && (forall|i: int| 0 <= i < arity ==> native_domain_valid(store.domains@[i])
                && native_domain_index(store.domains@[i]) == i)
    }
    /// The store is the process-wide singleton of its arity, with its static authorities installed.
    pub open(crate) spec fn numeric_store_wf(store: HistoryStore) -> bool {
        1 <= store.arity_spec() <= MAX_ARITY && store == *singleton_store(store.arity_spec())
            && singleton_valid(store.arity_spec())
    }

    pub uninterp spec fn coordinate_ids(wrapper: NativeCoordinates) -> Seq<vstd::resource::Loc>;
    pub uninterp spec fn coordinates_mutex_valid(wrapper: NativeCoordinates) -> bool;
    pub open(crate) spec fn coordinates_acquired(state: CoordinateState, wrapper: NativeCoordinates) -> bool {
        coordinate_wf(state) && forall|d: int| 0 <= d < MAX_ARITY ==> coordinate_id(state,d) == coordinate_ids(wrapper)[d]
    }
    pub uninterp spec fn history_keys_id(wrapper: NativeHistoryKeys) -> vstd::resource::Loc;
    pub uninterp spec fn history_keys_mutex_valid(wrapper: NativeHistoryKeys) -> bool;
    pub open(crate) spec fn history_keys_acquired(state: HistoryKeyState, wrapper: NativeHistoryKeys) -> bool {
        history_key_wf(state) && state.issued@.id() == history_keys_id(wrapper)
    }

    pub(crate) fn allocator_stale_and_drop_client() {
        let mut coordinates = CoordinateState::new();
        let ghost original = coordinates;
        let stale = allocate_coordinate_state(&mut coordinates, 0, "component", 1,
            Ghost(ComponentIssuer::Byte), Tracked(None));
        assert(stale is Err);
        assert(coordinates.next@[0] == 2);
        assert(coordinate_map(coordinates,0).contains_key(1));
        let second = allocate_coordinate_state(&mut coordinates, 0, "component", 0,
            Ghost(ComponentIssuer::Byte), Tracked(None));
        assert(second is Ok);
        assert(second.unwrap().0 == 2);
        assert(coordinate_map(coordinates,0).contains_key(1));
        assert(coordinate_map(coordinates,0).contains_key(2));
        // A consumer may fail after issuance and discard its persistent receipt.
        let third = allocate_coordinate_state(&mut coordinates, 0, "component", 0,
            Ghost(ComponentIssuer::Byte), Tracked(None));
        assert(third is Ok);
        assert(third.unwrap().0 == 3);
        assert(coordinate_frame(original,coordinates));
        let ghost before_invalid = coordinates;
        let invalid = allocate_coordinate_state(&mut coordinates, MAX_ARITY, "component", 0,
            Ghost(ComponentIssuer::Byte), Tracked(None));
        assert(invalid is Err);
        assert(coordinates.next == before_invalid.next);
        assert forall|d: int| 0 <= d < MAX_ARITY implies coordinate_map(coordinates,d) == coordinate_map(before_invalid,d) by {}
        let mut histories = HistoryKeyState::new();
        let stale = allocate_history_state(&mut histories, 1, Ghost(HistoryIssuer::Byte));
        assert(stale is Err);
        assert(histories.next == 2);
        assert((histories.issued@)@.contains_key(1));
        let second = allocate_history_state(&mut histories, 0, Ghost(HistoryIssuer::Byte));
        assert(second is Ok);
        assert(second.unwrap().0 == 2);
        assert((histories.issued@)@.contains_key(1));
        assert((histories.issued@)@.contains_key(2));
        let ghost before_max = histories;
        let exhausted = allocate_history_state(&mut histories, usize::MAX, Ghost(HistoryIssuer::Byte));
        assert(exhausted == Err(HistoryError::IdExhausted { domain: "history" }));
        assert(histories.next == before_max.next);
        assert((histories.issued@)@ == (before_max.issued@)@);
    }
    pub(crate) fn allocator_arithmetic_exhaustion_client(coordinates: &mut CoordinateState,
        histories: &mut HistoryKeyState)
        requires coordinate_wf(*old(coordinates)), old(coordinates).next@[0] == u64::MAX,
            history_key_wf(*old(histories)), old(histories).next == usize::MAX,
        ensures final(coordinates).next == old(coordinates).next,
            coordinate_map(*final(coordinates),0) == coordinate_map(*old(coordinates),0),
            final(histories).next == old(histories).next,
            (final(histories).issued@)@ == (old(histories).issued@)@,
    {
        let component = allocate_coordinate_state(coordinates,0,"component",0,
            Ghost(ComponentIssuer::Byte),Tracked(None));
        assert(component is Err);
        let history = allocate_history_state(histories,0,Ghost(HistoryIssuer::Byte));
        assert(history is Err);
    }

    pub(crate) fn allocator_later_failure_client() {
        let mut coordinates = CoordinateState::new();
        let failure: Result<(), HistoryError> = match allocate_coordinate_state(&mut coordinates,
            0, "component", 0, Ghost(ComponentIssuer::Byte), Tracked(None)) {
            Ok((_id, _receipt)) => Err(HistoryError::AllocationFailed),
            Err(error) => Err(error),
        };
        assert(failure == Err(HistoryError::AllocationFailed));
        let second = allocate_coordinate_state(&mut coordinates, 0, "component", 0,
            Ghost(ComponentIssuer::Byte), Tracked(None));
        assert(second matches Ok((id, _)) && id == 2);
        assert(coordinate_map(coordinates, 0).contains_key(1));
        assert(coordinate_map(coordinates, 0).contains_key(2));

        let mut histories = HistoryKeyState::new();
        let failure: Result<(), HistoryError> = match allocate_history_state(&mut histories,
            0, Ghost(HistoryIssuer::Byte)) {
            Ok((_id, _receipt)) => Err(HistoryError::AllocationFailed),
            Err(error) => Err(error),
        };
        assert(failure == Err(HistoryError::AllocationFailed));
        let second = allocate_history_state(&mut histories, 0, Ghost(HistoryIssuer::Byte));
        assert(second matches Ok((id, _)) && id == 2);
        assert((histories.issued@)@.contains_key(1));
        assert((histories.issued@)@.contains_key(2));
    }

    pub(crate) fn allocator_last_legal_key_client(coordinates: &mut CoordinateState,
        histories: &mut HistoryKeyState)
        requires coordinate_wf(*old(coordinates)), old(coordinates).next@[0] == u64::MAX - 1,
            history_key_wf(*old(histories)), old(histories).next == usize::MAX - 1,
        ensures coordinate_frame(*old(coordinates), *final(coordinates)),
            final(coordinates).next@[0] == u64::MAX,
            coordinate_map(*final(coordinates), 0) == coordinate_map(*old(coordinates), 0).insert((u64::MAX - 1) as u64, ComponentIssuer::Byte),
            history_key_frame(*old(histories), *final(histories)), final(histories).next == usize::MAX,
            (final(histories).issued@)@ == (old(histories).issued@)@.insert((usize::MAX - 1) as usize, HistoryIssuer::Byte),
    {
        let component = allocate_coordinate_state(coordinates, 0, "component", 0,
            Ghost(ComponentIssuer::Byte), Tracked(None));
        assert(component matches Ok((id, _)) && id == u64::MAX - 1);
        let exhausted = allocate_coordinate_state(coordinates, 0, "component", 0,
            Ghost(ComponentIssuer::Byte), Tracked(None));
        assert(exhausted == Err(HistoryError::IdExhausted { domain: "component" }));
        let history = allocate_history_state(histories, 0, Ghost(HistoryIssuer::Byte));
        assert(history matches Ok((id, _)) && id == usize::MAX - 1);
        let exhausted = allocate_history_state(histories, 0, Ghost(HistoryIssuer::Byte));
        assert(exhausted == Err(HistoryError::IdExhausted { domain: "history" }));
    }

    pub open(crate) spec fn coordinate_map(state: CoordinateState, index: int) -> Map<u64, ComponentIssuer> {
        state.authorities@.entries[index]@
    }
    pub open(crate) spec fn coordinate_id(state: CoordinateState, index: int) -> vstd::resource::Loc {
        state.authorities@.entries[index].id()
    }
    pub open(crate) spec fn coordinate_wf(state: CoordinateState) -> bool {
        state.authorities@.entries.len() == MAX_ARITY
            && forall|d: int| 0 <= d < MAX_ARITY ==> state.next@[d] > 0
                && (forall|id: u64| coordinate_map(state, d).contains_key(id) <==> 0 < id < state.next@[d])
    }
    pub open(crate) spec fn coordinate_frame(before: CoordinateState, after: CoordinateState) -> bool {
        coordinate_wf(after) && forall|d: int| 0 <= d < MAX_ARITY ==>
            coordinate_id(before, d) == coordinate_id(after, d)
                && coordinate_map(before, d).submap_of(coordinate_map(after, d))
    }
    pub open(crate) spec fn coordinate_prior(state: CoordinateState, index: usize,
        prior: Option<&ComponentReceipts>) -> bool {
        match prior { None => true, Some(previous) => index < MAX_ARITY && previous.id() == coordinate_id(state, index as int) }
    }
    pub open(crate) spec fn coordinate_result(before: CoordinateState, after: CoordinateState,
        index: usize, domain: &'static str, last: u64, issuer: ComponentIssuer, prior: Option<&ComponentReceipts>,
        result: Result<(u64, Tracked<ComponentIdReceipt>), HistoryError>) -> bool {
        coordinate_frame(before, after)
        && (index < MAX_ARITY && (last == 0 || match prior {
            Some(previous) => previous@.contains_key(last), None => false,
        }) ==> (result matches Err(error) ==> error == HistoryError::IdExhausted { domain }))
        && if index >= MAX_ARITY {
            after.next == before.next && (forall|d: int| 0 <= d < MAX_ARITY ==> coordinate_map(after,d) == coordinate_map(before,d))
                && result == Err(HistoryError::Invariant { message: "invalid identity domain" })
        } else if before.next@[index as int] == u64::MAX {
            after.next == before.next && (forall|d: int| 0 <= d < MAX_ARITY ==> coordinate_map(after,d) == coordinate_map(before,d))
                && result == Err(HistoryError::IdExhausted { domain })
        } else {
            let id = before.next@[index as int];
            after.next@ == before.next@.update(index as int, (id + 1) as u64)
            && (forall|d: int| 0 <= d < MAX_ARITY ==> coordinate_map(after,d) ==
                if d == index { coordinate_map(before,d).insert(id,issuer) } else { coordinate_map(before,d) })
            && if id <= last { result == Err(HistoryError::Invariant { message: "identity allocator moved backwards" }) }
            else { match result { Ok((key, receipt)) => key == id && 0 < key < u64::MAX
                && receipt@.id() == coordinate_id(after,index as int) && receipt@@ == (key,issuer)
                && (match prior { None => true, Some(previous) => forall|k: u64| previous@.contains_key(k) ==> k < key }),
                Err(_) => false } }
        }
    }
    pub open(crate) spec fn history_key_wf(state: HistoryKeyState) -> bool {
        state.next > 0 && forall|id: usize| (state.issued@)@.contains_key(id) <==> 0 < id < state.next
    }
    pub open(crate) spec fn history_key_frame(before: HistoryKeyState, after: HistoryKeyState) -> bool {
        history_key_wf(after) && before.issued@.id() == after.issued@.id()
            && (before.issued@)@.submap_of((after.issued@)@)
    }
    pub open(crate) spec fn history_key_result(before: HistoryKeyState, after: HistoryKeyState,
        last: usize, issuer: HistoryIssuer, result: Result<(usize, Tracked<HistoryKeyReceipt>), HistoryError>) -> bool {
        history_key_frame(before,after) && if last == usize::MAX || before.next == usize::MAX {
            after.next == before.next && (after.issued@)@ == (before.issued@)@
                && result == Err(HistoryError::IdExhausted { domain: "history" })
        } else {
            after.next == before.next + 1 && (after.issued@)@ == (before.issued@)@.insert(before.next,issuer)
                && if before.next <= last { result == Err(HistoryError::Invariant { message: "history identity allocator moved backwards" }) }
                else { match result { Ok((key,receipt)) => key == before.next && 0 < key < usize::MAX
                    && receipt@.id() == after.issued@.id() && receipt@@ == (key,issuer), Err(_) => false } }
        }
    }
    pub(crate) proof fn empty_coordinate_authorities(count: nat) -> (tracked result: CoordinateAuthorities)
        ensures result.entries.len() == count,
            forall|i: int| 0 <= i < count ==> result.entries[i]@ == Map::empty(),
        decreases count,
    {
        if count == 0 {
            CoordinateAuthorities { entries: Seq::tracked_empty() }
        } else {
            let tracked mut result = empty_coordinate_authorities((count - 1) as nat);
            let tracked (authority, _) = vstd::resource::map::GhostMapAuth::new(Map::empty());
            result.entries.tracked_push(authority);
            assert forall|i: int| 0 <= i < count implies result.entries[i]@ == Map::empty() by {
                if i < count - 1 { assert(result.entries[i]@ == Map::empty()); }
            }
            result
        }
    }
    pub(crate) proof fn empty_history_authority() -> (tracked result: vstd::resource::map::GhostMapAuth<usize, HistoryIssuer>)
        ensures result@ == Map::empty(),
    {
        let tracked (authority, _) = vstd::resource::map::GhostMapAuth::new(Map::empty());
        authority
    }

    /// One process-wide store per arity, installed by `HistoryStore::new`.
    pub uninterp spec fn singleton_store(arity: nat) -> Arc<HistoryStore>;
    pub(crate) uninterp spec fn numeric_authorities() -> Arc<NumericAuthorities>;
    pub open(crate) spec fn coordinate_authority(index: int) -> vstd::resource::Loc {
        coordinate_ids(numeric_authorities().coordinates)[index]
    }
    pub open(crate) spec fn history_authority() -> vstd::resource::Loc {
        history_keys_id(numeric_authorities().history_keys)
    }

    use junco_core::verify::history_specs as language;
    impl View for Event {
        type V = language::EventView;
        open(crate) spec fn view(&self) -> language::EventView {
            Seq::new(self.arity as nat, |i: int| self.slots@[i] as nat)
        }
    }
    impl vstd::std_specs::cmp::PartialEqSpecImpl for Event {
        open spec fn obeys_eq_spec() -> bool { true }
        open spec fn eq_spec(&self, other: &Self) -> bool { self@ == other@ }
    }
    pub open spec fn events_view(events: Seq<Event>) -> Seq<language::EventView> {
        Seq::new(events.len(), |i: int| events[i]@)
    }

    // Default's trait contract is public; its model is visible but predicate bodies stay local.
    pub struct DomainView {
        pub paths: Map<Seq<u8>, nat>,
        pub ids: Set<u64>,
    }

    #[verifier::opaque]
    pub(super) open spec fn path_map(paths: BTreeMap<Vec<u8>, u64>) -> Map<Seq<u8>, nat> {
        Map::new(
            paths@.dom().map(|path: Vec<u8>| path@),
            |bytes: Seq<u8>| {
                let path = choose|path: Vec<u8>| paths@.contains_key(path)
                    && path@ == bytes;
                paths@[path] as nat
            },
        )
    }


    pub open spec fn domain_wf(domain: DomainView) -> bool {
        language::interner_wf(domain.paths, u64::MAX as nat)
            && (forall|id: u64| domain.ids.contains(id)
                <==> domain.paths.values().contains(id as nat))
    }
    pub open(super) spec fn domain_unissued(domain: Domain) -> bool { domain.issued@ is None }

    pub open(super) spec fn domain_provenance(domain: Domain, index: int) -> bool {
        match domain.issued@ {
            None => domain.ids@ == Set::empty(),
            Some(receipts) => receipts.id() == coordinate_authority(index)
                && receipts@.dom() == domain.ids@
                && forall|id: u64| receipts@.contains_key(id) ==> receipts@[id] == ComponentIssuer::Byte,
        }
    }

    pub(super) open spec fn domain_forward_authority(domain: Domain) -> vstd::resource::Loc {
        domain.bindings@.forward.id()
    }
    pub(super) open spec fn domain_reverse_authority(domain: Domain) -> vstd::resource::Loc {
        domain.bindings@.reverse.id()
    }
    pub open(super) spec fn domain_bindings_wf(domain: Domain) -> bool {
        let bindings = domain.bindings@;
        bindings.paths.id() == bindings.forward.id() && bindings.ids.id() == bindings.reverse.id()
            && bindings.paths@ == bindings.forward@ && bindings.ids@ == bindings.reverse@
            && bindings.forward@.dom() == domain@.paths.dom()
            && (forall|path: Seq<u8>| domain@.paths.contains_key(path)
                ==> bindings.forward@[path] as nat == domain@.paths[path])
            && bindings.reverse@.dom() == domain@.ids
            && (forall|id: u64| domain@.ids.contains(id)
                ==> domain@.paths.contains_key(bindings.reverse@[id])
                    && domain@.paths[bindings.reverse@[id]] == id as nat)
            && (forall|path: Seq<u8>| domain@.paths.contains_key(path)
                ==> bindings.reverse@.contains_key(bindings.forward@[path])
                    && bindings.reverse@[bindings.forward@[path]] == path)
    }

    pub open(crate) spec fn record_view(record: HistoryRecord) -> NativeRecord { record.native }

    /// A lock-local read observation, not a mutable state attached to a shared record.
    pub open(crate) spec fn record_read_observed(record: HistoryRecord, guard: HistoryRecordReadGuard) -> bool {
        guard.valid() && guard.native_record() == record.native
            && guard.record_id() == record.record_id()
            && guard.lifecycle_id() == record.lifecycle_id()
            && guard.stored_view().spec_id() == record.record_id()
            && guard.snapshot_view().id() == record.lifecycle_id()
            && guard.snapshot_view().value() == guard.stored_view()@
    }
}
}

/// The process-wide synchronized byte identities and numeric ID allocators.
///
/// Every handle owns its record; this owner never retains histories, runtimes or caches.
#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct HistoryStore {
    pub(crate) domains: Vec<NativeDomain>,
    pub(crate) authorities: Arc<NumericAuthorities>,
}

#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub(crate) struct NumericAuthorities {
    pub(crate) coordinates: NativeCoordinates,
    pub(crate) history_keys: NativeHistoryKeys,
}

/// A shared history reference. Cloning it never copies events.
#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct HistoryHandle {
    pub(crate) owner: Arc<HistoryStore>,
    pub(crate) index: usize,
    pub(crate) record: NativeRecord,
    #[cfg(verus_keep_ghost)]
    pub(crate) global_registration: Tracked<HistoryKeyReceipt>,
}

impl HistoryHandle {
    #[verus_verify]
    /// Return the opaque, never-reused process-wide history ID.
    #[verus_spec(result => requires handle_wf(*self), ensures result == handle_index(*self))]
    pub const fn index(&self) -> usize {
        self.index
    }

    /// Check exact native owner identity without exposing the store or a mutable record.
    #[verus_verify]
    #[verus_spec(result => ensures
        result == (reference_identity(store) == handle_owner_identity(*self)),
        result ==> *store == *handle_owner(*self))]
    pub fn belongs_to(&self, store: &HistoryStore) -> bool {
        let owner = borrow_numeric_owner(&self.owner);
        same_numeric_reference(store, owner)
    }
}

// Native Arc dereference and reference pointer comparison are the only owner leaves.
#[doc(hidden)]
#[verus_verify(external_body)]
#[verus_spec(result => ensures *result == **owner,
    reference_identity(result) == arc_identity(*owner))]
pub fn borrow_numeric_owner(owner: &Arc<HistoryStore>) -> &HistoryStore {
    owner.as_ref()
}

#[verus_verify(external_body)]
#[verus_spec(result => ensures
    result == (reference_identity(left) == reference_identity(right)),
    result ==> *left == *right)]
fn same_numeric_reference(left: &HistoryStore, right: &HistoryStore) -> bool {
    core::ptr::eq(left, right)
}

#[verus_verify(external_body)]
#[verus_spec(result => ensures result == *owner, *result == **owner,
    arc_identity(result) == arc_identity(*owner))]
fn share_numeric_owner(owner: &Arc<HistoryStore>) -> Arc<HistoryStore> {
    Arc::clone(owner)
}

#[verus_verify]
impl Clone for HistoryHandle {
    #[verus_spec(result => ensures handle_wf(*self) ==> handle_wf(result), handle_clone_frame(*self, result))]
    fn clone(&self) -> Self {
        proof_decl! { let tracked receipt = self.global_registration.borrow().duplicate(); }
        Self {
            owner: share_numeric_owner(&self.owner),
            index: self.index,
            record: self.record.clone(),
            #[cfg(verus_keep_ghost)]
            global_registration: verus_exec_expr! { Tracked(receipt) },
        }
    }
}
#[cfg(verus_keep_ghost)]
verus! {
impl HistoryHandle {
    pub(crate) proof fn history_key_receipt_ref(tracked &self) -> (tracked result: &HistoryKeyReceipt)
        requires handle_wf(*self),
        ensures result.id() == history_authority(), result@ == (handle_index(*self), HistoryIssuer::Byte),
    { self.global_registration.borrow() }
}
}

/// A shared read-only history record. Mutations remain transactions on `HistoryStore`.
///
/// A record never grants the write capability needed to replace another history's word:
///
/// ```compile_fail
/// use history_store::store::HistoryRecord;
/// fn swap_histories(left: &HistoryRecord, right: &HistoryRecord) {
///     let mut left = left.read();
///     let mut right = right.read();
///     core::mem::swap(&mut *left, &mut *right);
/// }
/// ```
///
/// ```compile_fail
/// use history_store::store::HistoryRecord;
/// fn write_history(record: &HistoryRecord) {
///     let _guard = record.write();
/// }
/// ```
#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct HistoryRecord {
    pub(crate) native: NativeRecord,
}

#[verus_verify]
impl HistoryRecord {
    #[verus_spec(result => requires record_valid(native),
        ensures record_view(result) == native, result.valid(),
            result.record_id() == native.record_id(), result.lifecycle_id() == native.lifecycle_id())]
    pub(crate) fn from_native(native: NativeRecord) -> Self {
        Self { native }
    }

    /// Hold a read lock without exposing the underlying lock or its write capability.
    /// The retained snapshot describes this acquisition, not an unlocked future state.
    #[verus_spec(result => requires self.valid(),
        ensures record_read_observed(*self, result), result.valid(),
            result.record_id() == self.record_id(), result.lifecycle_id() == self.lifecycle_id(),
            result.stored_view().spec_id() == self.record_id(),
            result.snapshot_view().id() == self.lifecycle_id(),
            result.snapshot_view().value() == result.stored_view()@,
            result.snapshot_view().value().events == events_view(crate::history::verify::stored_events(&result.stored_view())),
            result.snapshot_view().value().revision == result.stored_view().spec_revision(),
            result.snapshot_view().value().events.len() == crate::history::verify::stored_events(&result.stored_view()).len())]
    pub fn read(&self) -> HistoryRecordReadGuard<'_> {
        let guard = NativeRecordReadGuard::acquire(&self.native);
        #[cfg(verus_keep_ghost)]
        let cell = guard.cell();
        proof_decl! { let tracked snapshot = cell.lifecycle.borrow().observe(); }
        proof! { crate::history::lemma_stored_history_view(cell.stored); }
        HistoryRecordReadGuard {
            guard,
            #[cfg(verus_keep_ghost)]
            snapshot: verus_exec_expr! { Tracked(snapshot) },
        }
    }
}

#[verus_verify]
impl Clone for HistoryRecord {
    #[verus_spec(result => ensures result == *self, self.valid() ==> result.valid())]
    fn clone(&self) -> Self {
        Self {
            native: self.native.clone(),
        }
    }
}

/// A borrowed record view. The native guard stays private because it can reveal its lock.
///
/// ```compile_fail
/// use history_store::store::HistoryRecord;
/// fn recover_native_guard(record: &HistoryRecord) {
///     let _native_guard = record.read().guard;
/// }
/// ```
#[verus_verify]
pub struct HistoryRecordReadGuard<'a> {
    guard: NativeRecordReadGuard<'a>,
    #[cfg(verus_keep_ghost)]
    snapshot: Tracked<crate::history::verify::Snapshot>,
}

#[verus_verify]
impl core::ops::Deref for HistoryRecordReadGuard<'_> {
    type Target = StoredHistory;

    #[verus_spec(result => ensures *result == self.stored_view())]
    fn deref(&self) -> &Self::Target {
        let cell = self.guard.cell();
        &cell.stored
    }
}

#[verus_verify]
impl HistoryRecordReadGuard<'_> {
    /// Validate an actual retained snapshot against the lifecycle held by this read lock.
    #[doc(hidden)]
    #[cfg(verus_keep_ghost)]
    #[verus_spec(requires self.valid(), previous@.id() == self.lifecycle_id(),
        ensures previous@.value().revision <= self.snapshot_view().value().revision,
            previous@.value().revision == self.snapshot_view().value().revision
                ==> previous@.value().events.is_prefix_of(self.snapshot_view().value().events))]
    pub fn validate_snapshot(&self, previous: Tracked<&crate::history::verify::Snapshot>) {
        let cell = self.guard.cell();
        proof! {
            let tracked snapshot = previous.get();
            cell.lifecycle.borrow().validate(snapshot);
        }
    }
}

// Only native read-lock acquisition and fidelity of a borrow under that guard are trusted.
#[verus_verify]
#[verus_verify(external_body)]
struct NativeRecordReadGuard<'a> {
    guard: RwLockReadGuard<'a, RecordCell>,
}

#[verus_verify]
impl<'a> NativeRecordReadGuard<'a> {
    #[verus_verify(external_body)]
    #[verus_spec(result => requires record_valid(*record),
        ensures result.record_view() == *record, record_acquired(result.cell_view(), *record))]
    fn acquire(record: &'a NativeRecord) -> Self {
        Self {
            guard: record.inner.read(),
        }
    }

    #[verus_verify(external_body)]
    #[verus_spec(result => ensures *result == self.cell_view())]
    fn cell(&self) -> &RecordCell {
        &self.guard
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl NativeRecordReadGuard<'_> {
    uninterp spec fn cell_view(self) -> RecordCell;
    uninterp spec fn record_view(self) -> NativeRecord;
}

impl HistoryRecord {
    pub open(crate) spec fn valid(&self) -> bool { record_valid(self.native) }
    pub open(crate) spec fn record_id(&self) -> usize { self.native.record_id() }
    pub open(crate) spec fn lifecycle_id(&self) -> vstd::resource::Loc { self.native.lifecycle_id() }
}

impl HistoryRecordReadGuard<'_> {
    /// The exact stored payload borrowed while this read lock is held.
    pub closed spec fn stored_view(&self) -> StoredHistory { self.guard.cell_view().stored }
    /// The persistent observation retained from this read acquisition.
    pub closed spec fn snapshot_view(&self) -> crate::history::verify::Snapshot { self.snapshot@ }
    pub closed spec fn record_id(&self) -> usize { self.guard.record_view().record_id() }
    pub closed spec fn lifecycle_id(&self) -> vstd::resource::Loc { self.guard.record_view().lifecycle_id() }
    pub(crate) closed spec fn native_record(&self) -> NativeRecord { self.guard.record_view() }
    pub closed spec fn valid(&self) -> bool {
        record_acquired(self.guard.cell_view(), self.guard.record_view())
            && self.snapshot@.id() == self.lifecycle_id()
            && self.snapshot@.value() == self.stored_view()@
    }

    pub proof fn snapshot_ref(tracked &self) -> (tracked result: &crate::history::verify::Snapshot)
        requires self.valid(),
        ensures *result == self.snapshot_view(), result.id() == self.lifecycle_id(),
            result.value() == self.stored_view()@,
    { self.snapshot.borrow() }

    /// Retain evidence after releasing the guard, without copying any native events.
    pub proof fn snapshot(tracked &self) -> (tracked result: crate::history::verify::Snapshot)
        requires self.valid(),
        ensures result.id() == self.lifecycle_id(), result.value() == self.stored_view()@,
            result@ == self.snapshot_view()@,
    { self.snapshot.borrow().duplicate() }

    pub proof fn lemma_observation(&self)
        requires self.valid(),
        ensures self.stored_view().spec_id() == self.record_id(),
            self.snapshot_view().id() == self.lifecycle_id(),
            self.snapshot_view().value() == self.stored_view()@,
            self.snapshot_view().value().events == events_view(crate::history::verify::stored_events(&self.stored_view())),
            self.snapshot_view().value().revision == self.stored_view().spec_revision(),
            self.snapshot_view().value().events.len() == crate::history::verify::stored_events(&self.stored_view()).len(),
    { crate::history::lemma_stored_history_view(self.stored_view()); }
}
}

#[verus_verify]
impl HistoryStore {
    /// Return the process-wide store for `arity`, sharing numeric issuance across all arities.
    /// Panics unless `1 <= arity <= MAX_ARITY`.
    // Native static initialization and Arc allocation; no user code runs under this lock.
    #[verus_verify(external_body)]
    #[verus_spec(result => requires 1 <= arity <= MAX_ARITY,
        ensures result == singleton_store(arity as nat), singleton_valid(arity as nat),
            numeric_store_wf(*result), result.arity_spec() == arity,
            arc_identity(result) == arc_identity(singleton_store(arity as nat)))]
    pub fn new(arity: usize) -> Arc<Self> {
        assert!(
            (1..=MAX_ARITY).contains(&arity),
            "event arity must be between 1 and MAX_ARITY"
        );
        let mut registry = STORES.lock();
        let registry = registry.get_or_insert_with(|| StoreRegistry {
            authorities: Arc::new(NumericAuthorities {
                coordinates: NativeCoordinates::new(),
                history_keys: NativeHistoryKeys::new(),
            }),
            stores: core::array::from_fn(|_| None),
        });
        if let Some(store) = &registry.stores[arity - 1] {
            return Arc::clone(store);
        }
        let mut domains = Vec::with_capacity(arity);
        for _index in 0..arity {
            domains.push(NativeDomain::new(verus_exec_expr! { Ghost(_index) }));
        }
        let store = Arc::new(Self {
            domains,
            authorities: Arc::clone(&registry.authorities),
        });
        registry.stores[arity - 1] = Some(Arc::clone(&store));
        store
    }

    #[cfg(verus_keep_ghost)]
    verus! {
        pub closed spec fn arity_spec(&self) -> nat { self.domains@.len() }
    }

    #[verus_spec(result => ensures result == self.arity_spec())]
    pub fn arity(&self) -> usize {
        self.domains.len()
    }

    /// Issue a component ID above `last` from the counters shared by byte and typed views,
    /// so a numeric event from one view can never name another view's identity.
    #[verus_spec(result =>
        requires numeric_store_wf(*self),
            match prior@ { None => true, Some(previous) => index < MAX_ARITY && previous.id() == coordinate_authority(index as int) },
        ensures result matches Ok((id, receipt)) ==> last < id < u64::MAX
            && receipt@.id() == coordinate_authority(index as int) && receipt@@ == (id, issuer@)
            && (match prior@ { None => true, Some(previous) => forall|key: u64| previous@.contains_key(key) ==> key < id }),
        result != Err(HistoryError::WrongHistoryOwner),
        index < MAX_ARITY && (last == 0 || match prior@ {
            Some(previous) => previous@.contains_key(last), None => false,
        }) ==> (result matches Err(error) ==> error == HistoryError::IdExhausted { domain }),
    )]
    pub(crate) fn allocate_after(
        &self,
        index: usize,
        domain: &'static str,
        last: u64,
        issuer: Ghost<ComponentIssuer>,
        prior: Tracked<Option<&ComponentReceipts>>,
    ) -> Result<(u64, Tracked<ComponentIdReceipt>), HistoryError> {
        proof! { reveal(coordinate_authority); }
        self.authorities.coordinates.with_state((index, domain, last, issuer, prior),
            verus_exec_expr! {
            |state: &mut CoordinateState, context: (usize, &'static str, u64, Ghost<ComponentIssuer>, Tracked<Option<&ComponentReceipts>>)|
                -> (result: Result<(u64, Tracked<ComponentIdReceipt>), HistoryError>)
                requires coordinates_acquired(*old(state), self.authorities.coordinates),
                    coordinate_prior(*old(state), context.0, context.4@),
                ensures coordinate_result(*old(state), *final(state), context.0, context.1, context.2, context.3@, context.4@, result),
                    result != Err(HistoryError::WrongHistoryOwner),
                    context.0 < MAX_ARITY && (context.2 == 0 || match context.4@ {
                        Some(previous) => previous@.contains_key(context.2), None => false,
                    }) ==> (result matches Err(error) ==> error == HistoryError::IdExhausted { domain: context.1 }),
            { allocate_coordinate_state(state, context.0, context.1, context.2, context.3, context.4) } })
    }

    /// Issue a never-recycled history ID above `last`; retained receipts certify a live frontier.
    #[verus_spec(result => requires numeric_store_wf(*self),
        match prior@ { Some(previous) => previous.id() == history_authority(), None => true },
        ensures result matches Ok((id, receipt)) ==> last < id < usize::MAX
            && receipt@.id() == history_authority() && receipt@@ == (id, issuer@),
        last == 0 || (match prior@ { Some(previous) => previous.key() == last, None => false }) ==>
            (result matches Err(error) ==> error == HistoryError::IdExhausted { domain: "history" }))]
    pub(crate) fn allocate_history_after(
        &self,
        last: usize,
        issuer: Ghost<HistoryIssuer>,
        prior: Tracked<Option<&HistoryKeyReceipt>>,
    ) -> Result<(usize, Tracked<HistoryKeyReceipt>), HistoryError> {
        proof! { reveal(history_authority); }
        if last == usize::MAX {
            return Err(HistoryError::IdExhausted { domain: "history" });
        }
        self.authorities.history_keys.with_state((last, issuer, prior),
            verus_exec_expr! {
            |state: &mut HistoryKeyState, context: (usize, Ghost<HistoryIssuer>, Tracked<Option<&HistoryKeyReceipt>>)|
                -> (result: Result<(usize, Tracked<HistoryKeyReceipt>), HistoryError>)
                requires history_keys_acquired(*old(state), self.authorities.history_keys),
                    match context.2@ { Some(previous) => previous.id() == old(state).issued@.id(), None => true },
                ensures history_key_result(*old(state), *final(state), context.0, context.1@, result),
                    context.0 == 0 || (match context.2@ { Some(previous) => previous.key() == context.0, None => false }) ==>
                        (result matches Err(error) ==> error == HistoryError::IdExhausted { domain: "history" }),
            {
                let (last, issuer, Tracked(prior)) = context;
                proof {
                    if let Some(previous) = prior {
                        previous.agree(state.issued.borrow());
                        assert((state.issued@)@.contains_key(previous.key()));
                        assert(previous.key() < state.next);
                    }
                }
                allocate_history_state(state, last, issuer)
            } })
    }
}

#[verus_verify]
impl HistoryStore {
    /// Intern arbitrary exact bytes in one coordinate; prior bindings survive every outcome.
    /// A coordinate outside this store's arity returns `InvalidPolicy` without touching a domain.
    #[verus_verify]
    #[verus_spec(result => requires numeric_store_wf(*self),
        ensures result matches Ok(id) ==> 0 < id < u64::MAX,
            byte_intern_result(self, component.0 as int, bytes@, result))]
    pub fn intern<L: Limits>(
        &self,
        component: Component,
        bytes: &[u8],
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<u64, HistoryError> {
        match self.intern_observed(component, bytes, limits, world) {
            Ok((id, _receipt)) => Ok(id),
            Err(error) => Err(error),
        }
    }

    /// Retain persistent byte identity evidence without another native lookup or allocation.
    #[doc(hidden)]
    #[verus_verify]
    #[verus_spec(result => requires numeric_store_wf(*self),
        ensures byte_intern_result(self, component.0 as int, bytes@,
            match result { Ok((id, _)) => Ok(id), Err(error) => Err(error) }),
            result matches Ok((id, receipt)) ==> 0 < id < u64::MAX
                && component.0 < self.arity_spec()
                && byte_binding_result(self, component.0 as int, bytes@, id, receipt@)
                && receipt@.coordinate_authority() == coordinate_authority(component.0 as int))]
    pub fn intern_observed<L: Limits>(
        &self,
        component: Component,
        bytes: &[u8],
        limits: &mut L,
        _world: &mut ObservationWorld,
    ) -> Result<(u64, Tracked<ByteBindingReceipt>), HistoryError> {
        let index = component.index();
        if index >= self.arity() {
            return Err(HistoryError::invalid_policy(
                "component",
                "component index is outside event arity",
            ));
        }
        let native = &self.domains[index];
        let context = (bytes, limits);
        proof_decl! { let ghost input = context; }
        let operation = verus_exec_expr! {
            |domain: &mut Domain, context: (&[u8], &mut L)|
                -> (result: Result<(u64, Tracked<ByteBindingReceipt>), HistoryError>)
                requires domain_acquired(*old(domain), *native),
                    native_domain_index(*native) == index, numeric_store_wf(*self),
                    index < self.arity_spec() <= MAX_ARITY,
                    *native == byte_domain(self, index as int),
                ensures domain_acquired(*final(domain), *native),
                    byte_intern_maps(old(domain)@, final(domain)@, context.0@,
                        match result { Ok((id, _)) => Ok(id), Err(error) => Err(error) }),
                    result matches Ok((id, receipt)) ==> byte_binding_result(self, index as int, context.0@, id, receipt@)
                        && 0 < id < u64::MAX
                        && receipt@.coordinate_authority() == coordinate_authority(index as int),
            { domain.intern(context.0, index, "component", context.1, self) }
        };
        let result = native.with_domain(context, operation);
        proof! {
            let borrow = choose|borrow: &mut Domain| domain_acquired(mut_ref_current(borrow), *native)
                && domain_acquired(mut_ref_future(borrow), *native)
                && call_ensures(operation, (borrow, input), result);
            let before = mut_ref_current(borrow)@;
            let after = mut_ref_future(borrow)@;
            assert(byte_domain_transaction(self, index as int, before, after));
            assert(byte_intern_maps(before, after, bytes@,
                match result { Ok((id, _)) => Ok(id), Err(error) => Err(error) }));
            assert(byte_intern_result(self, index as int, bytes@,
                match result { Ok((id, _)) => Ok(id), Err(error) => Err(error) }));
        }
        result
    }

    /// Create an empty history owned by its handles and read-only records.
    #[verus_verify]
    #[verus_spec(result => requires numeric_store_wf(**self),
        ensures result matches Ok(handle) ==> handle_wf(handle)
            && handle_owner_identity(handle) == arc_identity(*self) && history_created(handle))]
    pub fn new_history<L: Limits>(
        self: &Arc<Self>,
        limits: &mut L,
        _world: &mut ObservationWorld,
    ) -> Result<HistoryHandle, HistoryError> {
        let (index, _global_registration) = self.allocate_history_after(
            0,
            verus_exec_expr! { Ghost(HistoryIssuer::Byte) },
            verus_exec_expr! { Tracked(None) },
        )?;
        limits.enforce_memory()?;
        let stored = StoredHistory::new(index);
        proof! { crate::history::lemma_stored_history_view(stored); }
        let record = NativeRecord::new(stored);
        limits.enforce_memory()?;
        let handle = HistoryHandle {
            owner: share_numeric_owner(self),
            index,
            record,
            #[cfg(verus_keep_ghost)]
            global_registration: _global_registration,
        };
        proof! {
            assert(handle_wf(handle));
            assert(handle_owner_identity(handle) == arc_identity(*self));
            assert(crate::history::verify::stored_events(&stored).len() == 0);
            assert(crate::history::verify::stored_events(&stored) =~= Seq::<Event>::empty());
            assert(stored.spec_revision() == 0);
            assert(record_installed(record, stored));
            assert(history_created(handle));
        }
        Ok(handle)
    }

    /// Build an inline event from IDs belonging to this store's byte domains.
    /// Wrong arity and unknown IDs are rejected before the event is returned.
    #[verus_verify]
    #[verus_spec(result => requires numeric_store_wf(*self),
        ensures result matches Ok(event) ==> event@ == slots@.map(|i: int, id: u64| id as nat)
            && event@.len() == self.arity_spec() && event_validation_result(self, event, Ok(())),
            slots@.len() != self.arity_spec() ==> match result {
                Err(error) => event_arity_error(error), Ok(_) => false,
            },
            slots@.len() == self.arity_spec() ==> exists|event: Event|
                event@ == slots@.map(|i: int, id: u64| id as nat)
                && event_validation_result(self, event,
                    match result { Ok(_) => Ok(()), Err(error) => Err(error) }))]
    pub fn event(&self, slots: &[u64]) -> Result<Event, HistoryError> {
        if slots.len() != self.arity() {
            return Err(HistoryError::invalid_policy(
                "event",
                "event arity does not match store",
            ));
        }
        let event = Event::from_encoded(slots);
        let validation = self.validate_event(&event);
        proof! {
            assert(exists|candidate: Event| candidate@ == slots@.map(|i: int, id: u64| id as nat)
                && event_validation_result(self, candidate, validation));
        }
        validation?;
        Ok(event)
    }

    /// Validate arity, then coordinates in index order at separate read linearizations.
    #[verus_verify]
    #[verus_spec(result => requires numeric_store_wf(*self),
        ensures event_validation_result(self, *event, result),
            result matches Err(error) ==> event_validation_error(*event, error))]
    pub fn validate_event(&self, event: &Event) -> Result<(), HistoryError> {
        let arity = self.arity();
        if event.arity() != arity {
            return Err(HistoryError::invalid_policy(
                "event",
                "event arity does not match store",
            ));
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant numeric_store_wf(*self),
                index <= arity == self.arity_spec(), event@.len() == arity,
                forall|i: int| 0 <= i < index ==> byte_validation_observed(self, i, event@[i] as u64, true),
            decreases arity - index,
        ))]
        while index < arity {
            let native = &self.domains[index];
            let id = event.component(index);
            let operation = verus_exec_expr! {
                |domain: &mut Domain, id: u64| -> (result: Result<(), HistoryError>)
                    requires domain_acquired(*old(domain), *native),
                    ensures domain_acquired(*final(domain), *native), final(domain)@ == old(domain)@,
                        (result is Ok) == old(domain)@.ids.contains(id),
                        result is Ok ==> result == Ok(()),
                        result is Err ==> result == Err(HistoryError::UnknownId { domain: "component", id }),
                {
                    proof { reveal(<Domain as View>::view); }
                    domain.validate(id, "component")
                }
            };
            let result = native.with_domain(id, operation);
            proof! {
                let borrow = choose|borrow: &mut Domain| domain_acquired(mut_ref_current(borrow), *native)
                    && domain_acquired(mut_ref_future(borrow), *native)
                    && call_ensures(operation, (borrow, id), result);
                let view = mut_ref_current(borrow)@;
                assert(mut_ref_future(borrow)@ == view);
                assert(byte_domain_transaction(self, index as int, view, view));
                assert((result is Ok) == view.ids.contains(id));
                assert(byte_validation_observed(self, index as int, id, result is Ok));
                if result is Err {
                    assert(event_validation_result(self, *event, result));
                    lemma_event_validation_result_facts(self, *event, result);
                }
            }
            result?;
            index += 1;
        }
        proof! { assert(event_validation_result(self, *event, Ok(()))); }
        Ok(())
    }
}

impl HistoryStore {
    /// Borrow a read-only record after checking that the history belongs to this store.
    #[verus_verify]
    #[verus_spec(result => requires handle_wf(*history),
        ensures result is Ok <==> reference_identity(self) == handle_owner_identity(*history),
            result is Err ==> result == Err(HistoryError::WrongHistoryOwner),
            result matches Ok(record) ==> record_matches_handle(record, *history) && record.valid()
                && record.record_id() == handle_index(*history)
                && record.lifecycle_id() == handle_lifecycle_id(*history))]
    pub fn history_record(&self, history: &HistoryHandle) -> Result<HistoryRecord, HistoryError> {
        let record = self.history_record_inner(history)?;
        Ok(HistoryRecord::from_native(record))
    }

    #[verus_verify]
    #[verus_spec(result => requires handle_wf(*history),
        ensures result is Ok <==> reference_identity(self) == handle_owner_identity(*history),
            result is Err ==> result == Err(HistoryError::WrongHistoryOwner),
            result matches Ok(record) ==> record == history.record && record_valid(record)
                && numeric_store_wf(*self))]
    fn history_record_inner(&self, history: &HistoryHandle) -> Result<NativeRecord, HistoryError> {
        if !history.belongs_to(self) {
            return Err(HistoryError::WrongHistoryOwner);
        }
        Ok(history.record.clone())
    }

    /// Atomically append validated events, preserving the history revision.
    /// The postcondition describes only this operation's lock-local transaction;
    /// ownership and validation errors, and empty input, need no record lock.
    #[verus_verify]
    #[verus_spec(result => requires handle_wf(*history),
        ensures append_result(self, *history, events@, result))]
    pub fn append<L: Limits>(
        &self,
        history: &HistoryHandle,
        events: &[Event],
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<(), HistoryError> {
        let record = self.history_record_inner(history)?;
        if events.is_empty() {
            return Ok(());
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= events@.len(), events@.len() > 0, handle_wf(*history),
                record == history.record, record_valid(record), numeric_store_wf(*self),
                reference_identity(self) == handle_owner_identity(*history),
            decreases events@.len() - index))]
        while index < events.len() {
            let validation = self.validate_event(&events[index]);
            proof! {
                if let Err(error) = &validation {
                    assert(event_validation_error(events@[index as int], *error));
                    assert(exists|i: int, failed: HistoryError| 0 <= i < events@.len()
                        && Err::<(), HistoryError>(*error) == Err(failed)
                        && event_validation_error(events@[i], failed));
                }
            }
            validation?;
            index += 1;
        }
        let context = (events, limits, world);
        proof_decl! { let ghost input = context; }
        let operation = verus_exec_expr! {
            |cell: &mut RecordCell, context: (&[Event], &mut L, &mut ObservationWorld)|
                -> (result: Result<(), HistoryError>)
                requires record_acquired(*old(cell), record), context.0@.len() > 0,
                ensures record_acquired(*final(cell), record),
                    crate::history::verify::stored_append_result(old(cell).stored, final(cell).stored,
                        context.0@, result), result != Err(HistoryError::WrongHistoryOwner),
                    result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
            { cell.append_events(context.0, context.1, context.2) }
        };
        let result = record.with_record(context, operation);
        proof! {
            let borrow = choose|borrow: &mut RecordCell| record_acquired(mut_ref_current(borrow), record)
                && record_acquired(mut_ref_future(borrow), record)
                && call_ensures(operation, (borrow, input), result);
            let before = mut_ref_current(borrow).stored;
            let after = mut_ref_future(borrow).stored;
            assert(crate::history::verify::stored_append_result(before, after, events@, result));
            assert(record_transaction(*history, before, after));
            assert(record_append_observed(*history, events@, result));
        }
        result
    }

    /// Remove a suffix, invalidating prior snapshots only when events are removed.
    /// No-op, proper shrink, and revision exhaustion use the exact lock-local table.
    #[verus_verify]
    #[verus_spec(result => requires handle_wf(*history),
        ensures truncate_result(self, *history, len, result))]
    pub fn truncate(&self, history: &HistoryHandle, len: usize) -> Result<(), HistoryError> {
        let record = self.history_record_inner(history)?;
        let operation = verus_exec_expr! {
            |cell: &mut RecordCell, len: usize| -> (result: Result<(), HistoryError>)
                requires record_acquired(*old(cell), record),
                ensures record_acquired(*final(cell), record),
                    crate::history::verify::stored_truncate_result(old(cell).stored, final(cell).stored, len, result),
            { cell.truncate_events(len) }
        };
        let result = record.with_record(len, operation);
        proof! {
            let borrow = choose|borrow: &mut RecordCell| record_acquired(mut_ref_current(borrow), record)
                && record_acquired(mut_ref_future(borrow), record)
                && call_ensures(operation, (borrow, len), result);
            let before = mut_ref_current(borrow).stored;
            let after = mut_ref_future(borrow).stored;
            assert(crate::history::verify::stored_truncate_result(before, after, len, result));
            assert(record_transaction(*history, before, after));
            assert(record_truncate_observed(*history, len, result));
        }
        result
    }

    /// Return the event count observed by a read guard after verifying ownership.
    /// Concurrent callers may change the record after this observation is released.
    #[verus_verify]
    #[verus_spec(result => requires handle_wf(*history),
        ensures len_result(self, *history, result))]
    pub fn len(&self, history: &HistoryHandle) -> Result<usize, HistoryError> {
        let record = self.history_record(history)?;
        let guard = record.read();
        let len = guard.len();
        proof! {
            assert(exists|observed: HistoryRecord, held: HistoryRecordReadGuard|
                record_view(observed) == history.record && record_read_observed(observed, held)
                    && Ok::<usize, HistoryError>(len) == Ok(held.stored_view()@.events.len() as usize));
        }
        Ok(len)
    }
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::unwrap_used,
        clippy::indexing_slicing,
        clippy::arithmetic_side_effects
    )]

    use super::*;
    use junco_core::limits::Unmetered;

    fn event(store: &HistoryStore) -> Event {
        Event::from_encoded(&[
            store
                .intern(
                    Component(0),
                    b"alice",
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap(),
            store
                .intern(Component(1), b"edit", &mut Unmetered, &mut ObservationWorld)
                .unwrap(),
            store
                .intern(Component(2), b"doc", &mut Unmetered, &mut ObservationWorld)
                .unwrap(),
        ])
    }

    fn typed_event() -> Event {
        // A fresh typed view issues IDs that are never members of a byte domain.
        crate::typed::Store::<((), (), ())>::new()
            .unwrap()
            .encode_event(&((), (), ()))
            .unwrap()
    }

    #[test]
    fn global_owners_share_identities_and_handles() {
        let first = HistoryStore::new(3);
        let second = HistoryStore::new(3);
        assert!(Arc::ptr_eq(&first, &second));
        let principal = first
            .intern(
                Component(0),
                b"global-test/alice",
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        assert_eq!(
            principal,
            second
                .intern(
                    Component(0),
                    b"global-test/alice",
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap()
        );
        let history = first
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert!(history.belongs_to(&second));
        second
            .append(
                &history,
                &[event(&first)],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        assert_eq!(first.len(&history).unwrap(), 1);
        assert!(matches!(
            first.allocate_history_after(usize::MAX, Ghost::assume_new(), Tracked::assume_new()),
            Err(HistoryError::IdExhausted { domain: "history" })
        ));
    }

    #[test]
    fn all_arities_share_numeric_authorities_not_byte_domains() {
        let first = HistoryStore::new(1);
        let mut history_ids = BTreeSet::new();
        let mut coordinate_ids: Vec<BTreeSet<u64>> =
            (0..MAX_ARITY).map(|_| BTreeSet::new()).collect();
        for arity in 1..=MAX_ARITY {
            let store = HistoryStore::new(arity);
            assert_eq!(store.arity(), arity);
            assert_eq!(store.domains.len(), arity);
            assert!(Arc::ptr_eq(&store, &HistoryStore::new(arity)));
            assert!(Arc::ptr_eq(&first.authorities, &store.authorities));
            let mut slots = [0; MAX_ARITY];
            for index in 0..arity {
                let bytes = b"all-arities/\xff\x80\0";
                let component = Component(index as u8);
                let id = store
                    .intern(component, bytes, &mut Unmetered, &mut ObservationWorld)
                    .unwrap();
                assert_eq!(
                    id,
                    store
                        .intern(component, bytes, &mut Unmetered, &mut ObservationWorld)
                        .unwrap()
                );
                assert!(coordinate_ids[index].insert(id));
                slots[index] = id;
            }
            let event = store.event(&slots[..arity]).unwrap();
            assert_eq!(event.arity(), arity);
            store.validate_event(&event).unwrap();
            let history = store
                .new_history(&mut Unmetered, &mut ObservationWorld)
                .unwrap();
            assert!(history_ids.insert(history.index()));
            store
                .append(&history, &[event], &mut Unmetered, &mut ObservationWorld)
                .unwrap();
            if arity != 1 {
                assert!(!history.belongs_to(&first));
                assert!(matches!(
                    first.len(&history),
                    Err(HistoryError::WrongHistoryOwner)
                ));
                assert!(matches!(
                    first.validate_event(&event),
                    Err(HistoryError::InvalidPolicy { .. })
                ));
            }
            for index in [arity as u8, u8::MAX] {
                assert!(matches!(
                    store.intern(
                        Component(index),
                        b"invalid",
                        &mut Unmetered,
                        &mut ObservationWorld
                    ),
                    Err(HistoryError::InvalidPolicy { .. })
                ));
            }
            let malformed = Event::from_encoded(&slots[..arity - 1]);
            assert!(matches!(
                store.event(&slots[..arity - 1]),
                Err(HistoryError::InvalidPolicy { .. })
            ));
            assert!(matches!(
                store.event(&[1; MAX_ARITY + 1]),
                Err(HistoryError::InvalidPolicy { .. })
            ));
            assert!(matches!(
                store.event(&[0; MAX_ARITY][..arity]),
                Err(HistoryError::UnknownId {
                    domain: "component",
                    id: 0
                })
            ));
            assert!(matches!(
                store.validate_event(&malformed),
                Err(HistoryError::InvalidPolicy { .. })
            ));
            assert!(matches!(
                store.append(
                    &history,
                    &[event, malformed],
                    &mut Unmetered,
                    &mut ObservationWorld
                ),
                Err(HistoryError::InvalidPolicy { .. })
            ));
            assert_eq!(store.len(&history).unwrap(), 1);
            assert_eq!(event.component(arity), 0);
            assert_eq!(event.component(usize::MAX), 0);
        }
    }

    #[test]
    fn numeric_event_equality_and_hash_ignore_inactive_slots() {
        use core::hash::{Hash, Hasher};
        #[derive(Default)]
        struct TestHasher(u64);
        impl Hasher for TestHasher {
            fn finish(&self) -> u64 {
                self.0
            }
            fn write(&mut self, bytes: &[u8]) {
                for byte in bytes {
                    self.0 = self.0.wrapping_mul(31).wrapping_add(u64::from(*byte));
                }
            }
        }
        for arity in 1..=MAX_ARITY {
            let left = Event::from_encoded(&[17; MAX_ARITY][..arity]);
            let mut right = left;
            right.slots[arity..].fill(u64::MAX);
            assert_eq!(left, right);
            let mut left_hash = TestHasher::default();
            let mut right_hash = TestHasher::default();
            left.hash(&mut left_hash);
            right.hash(&mut right_hash);
            assert_eq!(left_hash.finish(), right_hash.finish());
            if arity < MAX_ARITY {
                assert_ne!(left, Event::from_encoded(&[17; MAX_ARITY][..arity + 1]));
            }
        }
    }

    #[test]
    #[should_panic(expected = "event arity must be between 1 and MAX_ARITY")]
    fn zero_store_arity_is_rejected() {
        HistoryStore::new(0);
    }

    #[test]
    #[should_panic(expected = "event arity must be between 1 and MAX_ARITY")]
    fn oversized_store_arity_is_rejected() {
        HistoryStore::new(MAX_ARITY + 1);
    }

    #[test]
    fn read_only_record_clones_observe_store_transactions() {
        let store = HistoryStore::new(3);
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let record = store.history_record(&history).unwrap();
        let retained = record.clone();
        {
            let first = record.read();
            let second = retained.read();
            assert!(core::ptr::eq(&*first, &*second));
            assert_eq!(first.len(), 0);
            assert_eq!(second.revision(), 0);
            assert_eq!(first.id(), history.index());
        }
        let event = event(&store);
        store
            .append(&history, &[event], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert_eq!(retained.read().len(), 1);
        assert_eq!(record.read().revision(), 0);
        store.truncate(&history, 0).unwrap();
        assert_eq!(retained.read().len(), 0);
        assert_eq!(record.read().revision(), 1);
        store
            .append(
                &history,
                &[event, event],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        // Records keep the buffer alive after the handle; the singleton never retains it.
        let weak = Arc::downgrade(&history.record.inner);
        drop(history);
        assert_eq!(retained.read().as_slice(), [event, event]);
        assert_eq!(retained.read().revision(), 1);
        drop(record);
        drop(retained);
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn exact_identities_and_large_domain() {
        let store = HistoryStore::new(3);
        let paths = ["a", "A", "/a", "a/", "a\0", "é", "e\u{301}"];
        let mut ids = BTreeSet::new();
        for path in paths {
            let id = store
                .intern(
                    Component(0),
                    path.as_bytes(),
                    &mut Unmetered,
                    &mut ObservationWorld,
                )
                .unwrap();
            assert_eq!(
                id,
                store
                    .intern(
                        Component(0),
                        path.as_bytes(),
                        &mut Unmetered,
                        &mut ObservationWorld
                    )
                    .unwrap()
            );
            assert!(ids.insert(id));
        }
        let first = store
            .intern(
                Component(2),
                b"common/prefix/0",
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let mut resources = BTreeSet::from([first]);
        for index in 1..5000 {
            assert!(
                resources.insert(
                    store
                        .intern(
                            Component(2),
                            alloc::format!("common/prefix/{index}").as_bytes(),
                            &mut Unmetered,
                            &mut ObservationWorld,
                        )
                        .unwrap()
                )
            );
        }
        assert_eq!(
            first,
            store
                .intern(
                    Component(2),
                    b"common/prefix/0",
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap()
        );
        assert_eq!(resources.len(), 5000);
        let action = store
            .intern(Component(1), b"a", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        store
            .intern(Component(0), b"new", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert_eq!(
            action,
            store
                .intern(Component(1), b"a", &mut Unmetered, &mut ObservationWorld)
                .unwrap()
        );
        let long = "x".repeat(4096);
        assert_ne!(
            store
                .intern(
                    Component(2),
                    long.as_bytes(),
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap(),
            store
                .intern(
                    Component(2),
                    (long + "/").as_bytes(),
                    &mut Unmetered,
                    &mut ObservationWorld
                )
                .unwrap()
        );
    }

    #[test]
    fn checked_full_width_allocator() {
        let mut next = u64::from(u32::MAX) + 1;
        assert_eq!(
            Domain::allocate_id(&mut next, "component").unwrap(),
            u64::from(u32::MAX) + 1
        );
        next = u64::MAX - 1;
        assert_eq!(
            Domain::allocate_id(&mut next, "component").unwrap(),
            u64::MAX - 1
        );
        assert!(matches!(
            Domain::allocate_id(&mut next, "component"),
            Err(HistoryError::IdExhausted {
                domain: "component"
            })
        ));
        assert_eq!(next, u64::MAX);
    }

    #[test]
    fn checked_history_key_counter() {
        let mut next = 1;
        assert_eq!(next_history_id(&mut next).unwrap(), 1);
        assert_eq!(next, 2);
        next = usize::MAX - 1;
        assert_eq!(next_history_id(&mut next).unwrap(), usize::MAX - 1);
        assert_eq!(next, usize::MAX);
        assert!(matches!(
            next_history_id(&mut next),
            Err(HistoryError::IdExhausted { domain: "history" })
        ));
        assert_eq!(next, usize::MAX);
    }

    #[test]
    fn allocator_failures_preserve_consumed_ids() {
        let mut coordinates = CoordinateState::new();
        assert!(matches!(
            allocate_coordinate_state(
                &mut coordinates,
                0,
                "component",
                1,
                Ghost::assume_new(),
                Tracked::assume_new()
            ),
            Err(HistoryError::Invariant { .. })
        ));
        assert_eq!(coordinates.next[0], 2);
        assert_eq!(&coordinates.next[1..], &[1; MAX_ARITY - 1]);
        let (second, _) = allocate_coordinate_state(
            &mut coordinates,
            0,
            "component",
            0,
            Ghost::assume_new(),
            Tracked::assume_new(),
        )
        .unwrap();
        assert_eq!(second, 2);
        assert_eq!(coordinates.next[0], 3);
        assert_eq!(&coordinates.next[1..], &[1; MAX_ARITY - 1]);
        assert!(matches!(
            allocate_coordinate_state(
                &mut coordinates,
                MAX_ARITY,
                "invalid",
                0,
                Ghost::assume_new(),
                Tracked::assume_new()
            ),
            Err(HistoryError::Invariant { .. })
        ));
        assert_eq!(coordinates.next[0], 3);
        assert_eq!(&coordinates.next[1..], &[1; MAX_ARITY - 1]);

        let mut histories = HistoryKeyState::new();
        assert!(matches!(
            allocate_history_state(&mut histories, 1, Ghost::assume_new()),
            Err(HistoryError::Invariant { .. })
        ));
        assert_eq!(histories.next, 2);
        let (second, _) = allocate_history_state(&mut histories, 0, Ghost::assume_new()).unwrap();
        assert_eq!(second, 2);
        assert_eq!(histories.next, 3);
        assert!(matches!(
            allocate_history_state(&mut histories, usize::MAX, Ghost::assume_new()),
            Err(HistoryError::IdExhausted { domain: "history" })
        ));
        assert_eq!(histories.next, 3);
    }

    #[test]
    fn atomic_append_and_revisions() {
        let store = HistoryStore::new(3);
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let valid = event(&store);
        let typed = typed_event();
        store
            .append(&history, &[valid], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert!(matches!(
            store.append(
                &history,
                &[valid, typed],
                &mut Unmetered,
                &mut ObservationWorld
            ),
            Err(HistoryError::UnknownId {
                domain: "component",
                ..
            })
        ));
        let record = store.history_record(&history).unwrap();
        assert_eq!(record.read().as_slice(), [valid]);
        assert_eq!(record.read().revision, 0);
        assert!(matches!(
            store.validate_event(&Event::from_encoded(&[
                valid.component(0),
                typed.component(1),
                valid.component(2),
            ])),
            Err(HistoryError::UnknownId {
                domain: "component",
                ..
            })
        ));
        assert!(matches!(
            store.validate_event(&Event::from_encoded(&[
                valid.component(0),
                valid.component(1),
                typed.component(2),
            ])),
            Err(HistoryError::UnknownId {
                domain: "component",
                ..
            })
        ));
        store
            .append(
                &history,
                &[valid, valid],
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        assert_eq!(store.len(&history.clone()).unwrap(), 3);
        assert_eq!(record.read().revision, 0);
        store.truncate(&history, 4).unwrap();
        store.truncate(&history, 3).unwrap();
        assert_eq!(record.read().revision, 0);
        store.truncate(&history, 2).unwrap();
        assert_eq!(record.read().revision, 1);
        store
            .history_record_inner(&history)
            .unwrap()
            .inner
            .write()
            .stored
            .revision = u64::MAX;
        assert!(matches!(
            store.truncate(&history, 0),
            Err(HistoryError::RevisionExhausted)
        ));
        assert_eq!(store.len(&history).unwrap(), 2);
    }

    #[cfg(feature = "std")]
    #[test]
    fn synchronized_interning_shares_one_identity() {
        fn assert_send_sync<T: Send + Sync>() {}
        use alloc::vec::Vec;
        assert_send_sync::<HistoryStore>();
        let barrier = Arc::new(std::sync::Barrier::new(8));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let barrier = Arc::clone(&barrier);
                std::thread::spawn(move || {
                    barrier.wait();
                    let store = HistoryStore::new(3);
                    let history = store
                        .new_history(&mut Unmetered, &mut ObservationWorld)
                        .unwrap();
                    (event(&store), history)
                })
            })
            .collect();
        let results: Vec<_> = threads
            .into_iter()
            .map(|thread| thread.join().unwrap())
            .collect();
        let store = HistoryStore::new(3);
        let mut keys = BTreeSet::new();
        for (event, history) in &results {
            assert_eq!(*event, results[0].0);
            assert!(Arc::ptr_eq(&history.owner, &store));
            assert!(history.index() > 0);
            assert!(keys.insert(history.index()));
        }
    }

    #[test]
    fn interning_and_history_creation_roll_back_memory_failures() {
        struct FailMemory {
            calls: usize,
            fail_at: usize,
        }
        impl Limits for FailMemory {
            fn checkpoint(&mut self) -> Result<(), junco_core::limits::LimitError> {
                Ok(())
            }
            fn publication_checkpoint(&mut self) -> Result<(), junco_core::limits::LimitError> {
                Ok(())
            }
            fn enforce_memory(&mut self) -> Result<(), junco_core::limits::LimitError> {
                self.calls = self.calls.saturating_add(1);
                if self.calls == self.fail_at {
                    Err(junco_core::limits::LimitError::MemoryLimitExceeded { usage: 1, limit: 0 })
                } else {
                    Ok(())
                }
            }
        }
        let store = HistoryStore::new(3);
        let known = store
            .intern(
                Component(0),
                b"rollback-test/known",
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        for fail_at in [1, 2] {
            let mut limits = FailMemory { calls: 0, fail_at };
            assert!(matches!(
                store.intern(
                    Component(0),
                    b"rollback-test/new",
                    &mut limits,
                    &mut ObservationWorld
                ),
                Err(HistoryError::Limit(_))
            ));
            let domain = store.domains[0].inner.lock();
            assert_eq!(
                domain.paths.get(b"rollback-test/known".as_slice()),
                Some(&known)
            );
            assert!(!domain.paths.contains_key(b"rollback-test/new".as_slice()));
            drop(domain);

            let mut limits = FailMemory { calls: 0, fail_at };
            assert!(matches!(
                store.new_history(&mut limits, &mut ObservationWorld),
                Err(HistoryError::Limit(_))
            ));
        }
        let history = store
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert!(history.index() > 0);
        assert!(history.belongs_to(&store));
        assert_eq!(store.len(&history).unwrap(), 0);
    }
}
