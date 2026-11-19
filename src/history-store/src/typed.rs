//! Scoped typed views retain persistent receipts from process-wide identity authorities.
//! Receipts certify each committed frontier, including after a later allocation fails.
//! Exclusive registry births distinguish owners; native key laws govern Eq classes.

use crate::store::Event as NumericEvent;
use crate::store::HistoryStore;
use alloc::sync::Arc;
use alloc::vec::Vec;
use history_syntax::KeyHash;
#[cfg(verus_keep_ghost)]
use history_syntax::event::specs::{AritySpec, EventSpec};
#[cfg(verus_keep_ghost)]
use history_syntax::spec::events::{arity, event_view, projection_laws};
use history_syntax::syntax::Component;
use history_syntax::{Arity, Event, MAX_ARITY};
use junco_core::compile::{FlatEncoder, lower_flat, validate_component};
use junco_core::errors::HistoryError;
use junco_core::flat::FlatPair;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_assumptions::{arc_identity, reference_identity};
#[cfg(feature = "std")]
use parking_lot::Mutex;
#[cfg(not(feature = "std"))]
use spin::Mutex;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

use crate::keyed::KeyedMap;

// Ghost<T> signatures still name T after native erasure; this is the exact finite model.
pub type ComponentMaps<E> = vstd::seq::Seq<vstd::seq::Seq<(<E as Event>::Component, u64)>>;
pub type HistoryRegistration =
    vstd::resource::map::GhostPersistentPointsTo<usize, vstd::resource::Loc>;
pub(crate) type RegistryBirth = vstd::resource::map::GhostPointsTo<usize, vstd::resource::Loc>;
pub(crate) type StoreIdReceipt =
    vstd::resource::map::GhostPersistentPointsTo<u64, vstd::resource::Loc>;
#[cfg(verus_keep_ghost)]
pub(crate) type StoreIdAuth = vstd::resource::map::GhostMapAuth<u64, vstd::resource::Loc>;

// One process allocator across every E, including on targets without AtomicU64.
#[verus_verify]
static STORE_IDS: NativeStoreIds = NativeStoreIds::new();

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::std_specs::vec::group_vec_axioms};

pub(crate) struct Codebook<K: Copy + Eq + KeyHash> {
    pub(crate) values: KeyedMap<K, u64>,
    pub(crate) last: u64,
    #[cfg(verus_keep_ghost)]
    pub(crate) issued: Tracked<Option<crate::store::ComponentReceipts>>,
}

/// Checked arithmetic for the process store-ID allocator.
fn checked_successor(last: u64, domain: &'static str) -> (result: Result<u64, HistoryError>)
    ensures match result {
        Ok(id) => last < u64::MAX && id == last + 1 && id > 0,
        Err(error) => last == u64::MAX && error == HistoryError::IdExhausted { domain },
    },
{
    match last.checked_add(1) {
        Some(id) => Ok(id),
        None => Err(HistoryError::IdExhausted { domain }),
    }
}

// Checked payload of the live process store-ID authority.
pub(crate) struct StoreIdState {
    pub(crate) last: u64,
    #[cfg(verus_keep_ghost)]
    pub(crate) issued: Tracked<StoreIdAuth>,
}

impl StoreIdState {
    pub(crate) const fn new() -> (result: Self)
        ensures store_id_state_wf(result), result.last == 0,
            (result.issued@)@ == Map::<u64, vstd::resource::Loc>::empty(),
    {
        let tracked issued = empty_store_id_authority();
        Self { last: 0, #[cfg(verus_keep_ghost)] issued: Tracked(issued) }
    }
}

pub(crate) fn issue_store_id(state: &mut StoreIdState,
    Ghost(registry): Ghost<vstd::resource::Loc>)
    -> (result: Result<(u64, Tracked<StoreIdReceipt>), HistoryError>)
    requires store_id_state_wf(*old(state)),
    ensures store_id_issue_result(*old(state), *final(state), registry, result),
{
    let ghost before = (state.issued@)@;
    let id = match checked_successor(state.last, "store") {
        Ok(id) => id,
        Err(_) => return Err(HistoryError::IdExhausted { domain: "store" }),
    };
    proof { assert(!before.contains_key(id)); }
    let tracked receipt = state.issued.borrow_mut().insert(id, registry).persist();
    state.last = id;
    proof {
        assert forall|key: u64| #[trigger] (state.issued@)@.contains_key(key)
            <==> 0 < key <= state.last by {
            if key != id { assert((state.issued@)@.contains_key(key) == before.contains_key(key)); }
        }
        assert(before <= (state.issued@)@);
    }
    Ok((id, Tracked(receipt)))
}

// Only const mutex installation and lock/callback fidelity remain native leaves.
#[verifier::external_body]
pub(crate) struct NativeStoreIds {
    pub(crate) inner: spin::Mutex<StoreIdState>,
}

impl NativeStoreIds {
    #[verifier::external_body]
    pub(crate) const fn new() -> (result: Self)
        ensures store_ids_mutex_valid(result),
    {
        Self { inner: spin::Mutex::new(StoreIdState::new()) }
    }

    #[verifier::external_body]
    pub(crate) fn with_state<R, Context, F: FnOnce(&mut StoreIdState, Context) -> R>(
        &self, context: Context, operation: F) -> (result: R)
        requires store_ids_mutex_valid(*self),
            forall|borrow: &mut StoreIdState|
                store_id_state_acquired(mut_ref_current(borrow), *self)
                ==> call_requires(operation, (borrow, context)),
            forall|borrow: &mut StoreIdState, output: R|
                store_id_state_acquired(mut_ref_current(borrow), *self)
                    && call_ensures(operation, (borrow, context), output)
                ==> store_id_state_frame(mut_ref_current(borrow), mut_ref_future(borrow)),
        ensures exists|borrow: &mut StoreIdState|
            store_id_state_acquired(mut_ref_current(borrow), *self)
                && store_id_state_frame(mut_ref_current(borrow), mut_ref_future(borrow))
                && call_ensures(operation, (borrow, context), result),
    {
        let mut state = self.inner.lock();
        operation(&mut state, context)
    }
}

impl<K: Copy + Eq + KeyHash> Codebook<K> {
    fn new() -> (result: Self)
        ensures book_wf(result), book_entries(result) == Seq::<(K, u64)>::empty(),
            result.issued@ is None, result.last == 0,
            forall|index: int, issuer: crate::store::ComponentIssuer|
                book_receipts_wf(result, index, issuer),
    {
        Self { values: KeyedMap::new(), last: 0,
            #[cfg(verus_keep_ghost)] issued: Tracked(None) }
    }

    fn intern(&mut self, value: &K, index: usize, domain: &'static str,
        numeric_store: &HistoryStore, Ghost(issuer): Ghost<crate::store::ComponentIssuer>)
        -> (result: Result<u64, HistoryError>)
        requires crate::store::verify::numeric_store_wf(*numeric_store),
            index < numeric_store.arity_spec(),
            book_receipts_wf(*old(self), index as int, issuer),
        ensures book_receipts_wf(*final(self), index as int, issuer),
            result != Err(HistoryError::WrongHistoryOwner),
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> error == HistoryError::AllocationFailed
                || error == (HistoryError::IdExhausted { domain }),
            result matches Err(_) ==> final(self).issued@ == old(self).issued@,
            junco_core::spec::hypotheses::key_laws::<K>() && book_wf(*old(self)) ==> {
            &&& book_wf(*final(self))
            &&& book_entries(*old(self)).is_prefix_of(book_entries(*final(self)))
            &&& match result {
                Ok(id) => book_encoded(*final(self), *value, id)
                    && (book_entries(*final(self)) == book_entries(*old(self))
                        || book_entries(*final(self)) == book_entries(*old(self)).push((*value, id))),
                Err(_) => book_entries(*final(self)) == book_entries(*old(self))
                    && final(self).last == old(self).last,
            }
        },
    {
        let ghost before = book_entries(*self);
        let ghost initial_wf = book_wf(*self);
        let ghost prior_entries = match self.issued@ {
            Some(receipts) => receipts@, None => Map::<u64, crate::store::ComponentIssuer>::empty(),
        };
        if let Some(id) = self.values.lookup(value) {
            return Ok(id);
        }
        // Reuse is checked first, so an exhausted domain still accepts established keys.
        let tracked prior = match self.issued.borrow() {
            Some(receipts) => Some(receipts), None => None,
        };
        let (id, Tracked(receipt)) = numeric_store.allocate_after(index, domain, self.last,
            Ghost(issuer), Tracked(prior))?;
        self.values.reserve_one()?;
        self.values.insert_fresh(*value, id);
        self.last = id;
        proof {
            let tracked mut previous = None;
            vstd::modes::tracked_swap(self.issued.borrow_mut(), &mut previous);
            let tracked aggregate = match previous {
                Some(mut aggregate) => { aggregate.combine_points_to(receipt); aggregate },
                None => receipt.submap(),
            };
            *self.issued.borrow_mut() = Some(aggregate);
            assert(self.issued@ is Some);
            assert((self.issued@->0)@ == prior_entries.insert(id, issuer));
            assert((self.issued@->0)@.contains_key(self.last));
        }
        proof {
            if junco_core::spec::hypotheses::key_laws::<K>() {
                assert(book_entries(*self) == before.push((*value, id)));
                let ghost old_ids = before.map(|i: int, pair: (K,u64)| pair.1);
                let ghost new_ids = book_entries(*self).map(|i: int, pair: (K,u64)| pair.1);
                assert(prior_entries.dom() == old_ids.to_set());
                assert(new_ids =~= old_ids.push(id));
                old_ids.lemma_push_to_set_commute(id);
                assert((self.issued@->0)@.dom() =~= prior_entries.dom().insert(id));
                assert((self.issued@->0)@.dom() == new_ids.to_set());
            }
            assert forall|key: u64| (self.issued@->0)@.contains_key(key) implies
                0 < key <= self.last && (self.issued@->0)@[key] == issuer by {
                if key != id { assert(prior_entries.contains_key(key)); }
            }
            if junco_core::spec::hypotheses::key_laws::<K>() && initial_wf {
                assert forall|i: int| #![trigger book_entries(*self)[i]]
                    0 <= i < book_entries(*self).len() implies
                    0 < book_entries(*self)[i].1 <= self.last by {
                    if i < before.len() { assert(before[i].1 < id); }
                }
                assert forall|i: int, j: int|
                    0 <= i < book_entries(*self).len() && 0 <= j < book_entries(*self).len()
                    implies (book_entries(*self)[i].0.eq_spec(&book_entries(*self)[j].0)
                        == (book_entries(*self)[i].1 == book_entries(*self)[j].1)) by {
                    if i == before.len() && j < before.len() {
                        assert(!value.eq_spec(&before[j].0));
                        assert(!before[j].0.eq_spec(value));
                    } else if j == before.len() && i < before.len() {
                        assert(!value.eq_spec(&before[i].0));
                        assert(!before[i].0.eq_spec(value));
                    }
                }
                assert(book_encoded(*self, *value, id)) by {
                    assert(book_entries(*self)[before.len() as int] == (*value, id));
                }
            }
        }
        Ok(id)
    }
}

pub(crate) struct ComponentBooks<E: Event> {
    pub(crate) books: Vec<Codebook<E::Component>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) registry: Ghost<vstd::resource::Loc>,
}

pub(crate) struct Codebooks<E: Event> {
    pub(crate) components: ComponentBooks<E>,
    pub(crate) next_history: usize,
    #[cfg(verus_keep_ghost)]
    pub(crate) owner: Ghost<u64>,
    #[cfg(verus_keep_ghost)]
    pub(crate) history_resources: Tracked<vstd::resource::map::GhostMapAuth<usize, vstd::resource::Loc>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) latest_history: Tracked<Option<crate::store::HistoryKeyReceipt>>,
}

impl<E: Event> Codebooks<E> {
    fn new(Ghost(owner): Ghost<u64>,
        Tracked(authority): Tracked<vstd::resource::map::GhostMapAuth<usize, vstd::resource::Loc>>)
        -> (result: Self)
        requires authority@ == map![0usize => authority.id()],
        ensures books_wf(result), result.owner@ == owner, result.next_history == 1,
            books_maps(result) == empty_maps::<E>(), registry_wf(result),
            result.history_resources@ == authority,
    {
        let width = E::Arity::value();
        let mut components = Vec::with_capacity(width);
        let mut index = 0;
        while index < width
            invariant index == components@.len(), index <= width,
                width == arity::<E>(), 1 <= width <= MAX_ARITY,
                forall|i: int| 0 <= i < index ==> book_wf(components@[i])
                    && book_entries(components@[i]) == Seq::<(E::Component, u64)>::empty()
                    && book_receipts_wf(components@[i], i,
                        crate::store::ComponentIssuer::Typed(authority.id())),
            decreases width - index,
        {
            components.push(Codebook::new());
            index += 1;
        }
        let result = Self {
            components: ComponentBooks {
                books: components,
                #[cfg(verus_keep_ghost)]
                registry: Ghost(authority.id()),
            },
            next_history: 1,
            #[cfg(verus_keep_ghost)]
            owner: Ghost(owner),
            #[cfg(verus_keep_ghost)]
            history_resources: Tracked(authority),
            #[cfg(verus_keep_ghost)]
            latest_history: Tracked(None),
        };
        proof {
            lemma_component_maps_wf(result.components);
            assert forall|field: int| 0 <= field < arity::<E>() implies
                books_maps(result)[field] =~= empty_maps::<E>()[field] by {}
            assert(books_maps(result) =~= empty_maps::<E>());
        }
        result
    }

    // The local frontier is registration bookkeeping; the process store is the allocation authority.
    fn allocate_history_id(&mut self, numeric_store: &HistoryStore,
        Ghost(location): Ghost<vstd::resource::Loc>)
        -> (result: Result<(usize, Tracked<crate::store::HistoryKeyReceipt>), HistoryError>)
        requires registry_wf(*old(self)), crate::store::verify::numeric_store_wf(*numeric_store),
        ensures self_same_books(*old(self), *final(self)), registry_wf(*final(self)),
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> error == (HistoryError::IdExhausted { domain: "history" }),
            final(self).history_resources@ == old(self).history_resources@,
            match result {
                Ok((id, receipt)) => old(self).next_history <= id && 0 < id < usize::MAX
                    && final(self).next_history == id + 1
                    && receipt@.id() == crate::store::verify::history_authority()
                    && receipt@.key() == id
                    && receipt@.value() == (crate::store::HistoryIssuer::Typed {
                        store: old(self).history_resources@.id(), lifecycle: location }),
                Err(_) => final(self).next_history == old(self).next_history,
            },
    {
        let frontier = self.next_history;
        if frontier == usize::MAX {
            return Err(HistoryError::IdExhausted { domain: "history" });
        }
        let last = match frontier.checked_sub(1) {
            Some(last) => last,
            None => return Err(HistoryError::invariant("history frontier is zero")),
        };
        let tracked prior = match self.latest_history.borrow() {
            Some(receipt) => Some(receipt), None => None,
        };
        let (id, receipt) = numeric_store.allocate_history_after(last,
            Ghost(crate::store::HistoryIssuer::Typed {
                store: self.history_resources@.id(), lifecycle: location }), Tracked(prior))?;
        let next = match id.checked_add(1) {
            Some(next) => next,
            None => return Err(HistoryError::IdExhausted { domain: "history" }),
        };
        self.next_history = next;
        proof {
            *self.latest_history.borrow_mut() = Some(receipt.borrow().duplicate());
            assert forall|key: usize| (self.history_resources@)@.contains_key(key)
                implies key < self.next_history by {
                assert(key < frontier);
            }
        }
        Ok((id, receipt))
    }

    fn allocate_history_id_for_resource(&mut self, numeric_store: &HistoryStore,
        Ghost(location): Ghost<vstd::resource::Loc>,
        Tracked(prior): Tracked<Option<&HistoryRegistration>>)
        -> (result: Result<(usize, Tracked<HistoryRegistration>, Tracked<crate::store::HistoryKeyReceipt>), HistoryError>)
        requires registry_wf(*old(self)), crate::store::verify::numeric_store_wf(*numeric_store),
            match prior { Some(registration) => registration.id() == old(self).history_resources@.id(), None => true },
        ensures registry_wf(*final(self)), self_same_books(*old(self), *final(self)),
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> error == (HistoryError::IdExhausted { domain: "history" }),
            final(self).history_resources@.id() == old(self).history_resources@.id(),
            (old(self).history_resources@)@.submap_of((final(self).history_resources@)@),
            match result {
                Ok((id, registration, receipt)) => 0 < id < usize::MAX && old(self).next_history <= id
                    && final(self).next_history == id + 1
                    && (final(self).history_resources@)@ == (old(self).history_resources@)@.insert(id, location)
                    && registration@.id() == old(self).history_resources@.id()
                    && registration@.key() == id && registration@.value() == location
                    && receipt@.id() == crate::store::verify::history_authority()
                    && receipt@.key() == id
                    && receipt@.value() == (crate::store::HistoryIssuer::Typed {
                        store: old(self).history_resources@.id(), lifecycle: location })
                    && match prior { Some(previous) => previous.key() < id, None => true },
                Err(_) => final(self).next_history == old(self).next_history
                    && final(self).history_resources@ == old(self).history_resources@,
            },
    {
        let ghost resources = (self.history_resources@)@;
        let ghost frontier = self.next_history;
        proof {
            if let Some(previous) = prior {
                previous.agree(self.history_resources.borrow());
            }
        }
        let (id, receipt) = self.allocate_history_id(numeric_store, Ghost(location))?;
        proof { assert(!resources.contains_key(id)); }
        let tracked registration = self.history_resources.borrow_mut().insert(id, location).persist();
        proof {
            assert forall|previous: usize| (self.history_resources@)@.contains_key(previous)
                implies previous < self.next_history by {
                if previous != id { assert(resources.contains_key(previous)); }
            }
        }
        Ok((id, Tracked(registration), receipt))
    }
}

// Native locks carry only the Codebooks invariant and finite snapshot provenance.
// They do not supply equality preservation or ID injection: intern proves those.
#[verifier::external_body]
#[verifier::accept_recursive_types(E)]
pub(crate) struct NativeBooks<E: Event> {
    inner: Mutex<Codebooks<E>>,
}

impl<E: Event> NativeBooks<E> {
    #[verifier::external_body]
    fn new(books: Codebooks<E>, Tracked(birth): Tracked<&RegistryBirth>) -> (result: Self)
        requires books_wf(books), registry_wf(books),
            birth.id() == books.history_resources@.id() && birth.key() == 0
                && birth.value() == books.history_resources@.id(),
        ensures mutex_valid(result, books.owner@, books.history_resources@.id()),
            snapshot_published::<E>(books.history_resources@.id(), books_maps(books)),
    {
        Self { inner: Mutex::new(books) }
    }

    // Locking invokes only a callback whose checked contract restores the actual entry frame.
    #[verifier::external_body]
    fn with_books<R, Context, F: FnOnce(&mut Codebooks<E>, Context) -> R>(&self,
        Ghost(owner): Ghost<u64>, Ghost(first): Ghost<ComponentMaps<E>>,
        Ghost(second): Ghost<ComponentMaps<E>>, Ghost(registry): Ghost<vstd::resource::Loc>,
        context: Context, operation: F) -> (result: R)
        requires mutex_valid(*self, owner, registry),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> snapshot_published::<E>(registry, first)
                && maps_wf::<E>(first) && snapshot_published::<E>(registry, second) && maps_wf::<E>(second),
            forall|borrow: &mut Codebooks<E>| books_acquired(mut_ref_current(borrow), owner, registry, first, second)
                ==> call_requires(operation, (borrow, context)),
            forall|borrow: &mut Codebooks<E>, output: R|
                books_acquired(mut_ref_current(borrow), owner, registry, first, second)
                    && call_ensures(operation, (borrow, context), output)
                ==> publication_frame(mut_ref_current(borrow), mut_ref_future(borrow)),
        ensures exists|borrow: &mut Codebooks<E>|
            books_acquired(mut_ref_current(borrow), owner, registry, first, second)
                && publication_frame(mut_ref_current(borrow), mut_ref_future(borrow))
                && call_ensures(operation, (borrow, context), result)
                && snapshot_published::<E>(registry, books_maps(mut_ref_future(borrow))),
    {
        let mut books = self.inner.lock();
        operation(&mut books, context)
    }
}

/// Policy-arity typed coordinate codebooks scoped to this view. Component and history IDs
/// come from shared process-wide authorities, so views never issue colliding identities.
/// Share a store with `Arc`; components and events retain their original Rust values.
pub struct Store<E: Event> {
    pub(crate) id: u64,
    pub(crate) books: NativeBooks<E>,
    pub(crate) numeric_store: Arc<HistoryStore>,
    #[cfg(verus_keep_ghost)]
    pub(crate) history_registry: Ghost<vstd::resource::Loc>,
    #[cfg(verus_keep_ghost)]
    pub(crate) store_id_receipt: Tracked<StoreIdReceipt>,
    #[cfg(verus_keep_ghost)]
    pub(crate) registry_birth: Tracked<RegistryBirth>,
}

/// Share the native store allocation without changing its logical contents.
#[doc(hidden)]
#[verifier::external_body]
pub fn share_store<E: Event>(store: &Arc<Store<E>>) -> (result: Arc<Store<E>>)
    ensures result == *store, *result == **store,
        arc_identity(result) == arc_identity(*store), same_store_owner(result, *store),
{
    Arc::clone(store)
}

/// Borrow the referent whose native identity is retained by the Arc.
#[doc(hidden)]
#[verifier::external_body]
pub fn borrow_store<E: Event>(store: &Arc<Store<E>>) -> (result: &Store<E>)
    ensures *result == **store, reference_identity(result) == arc_identity(*store),
{
    store.as_ref()
}

// Verus statics are exec-only; this leaf exposes the one installed mutex reference.
#[verifier::external_body]
fn process_store_ids_ref() -> (result: &'static NativeStoreIds)
    ensures *result == process_store_ids(), store_ids_mutex_valid(*result),
{ &STORE_IDS }

fn allocate_store_id(Ghost(registry): Ghost<vstd::resource::Loc>)
    -> (result: Result<(u64, Tracked<StoreIdReceipt>), HistoryError>)
    ensures result matches Ok((id, receipt)) ==> id > 0
        && receipt@.id() == store_id_authority() && receipt@.key() == id
        && receipt@.value() == registry,
        junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Err(error) ==> error == (HistoryError::IdExhausted { domain: "store" }),
{
    proof { reveal(store_id_authority); }
    let ids = process_store_ids_ref();
    ids.with_state(Ghost(registry),
        |state: &mut StoreIdState, registry: Ghost<vstd::resource::Loc>|
            -> (result: Result<(u64, Tracked<StoreIdReceipt>), HistoryError>)
            requires store_id_state_acquired(*old(state), *ids),
            ensures store_id_issue_result(*old(state), *final(state), registry@, result),
        { issue_store_id(state, registry) })
}

/// A fresh process-wide owner id from the store-id allocator, for clients that tag handles with
/// their issuer (the analyzer's `RuleId`). Ids are issued in increasing order, so no two calls in
/// one process return the same id; the allocator's ghost receipt is not needed by these clients.
pub fn issue_owner_id() -> (result: Result<u64, HistoryError>)
    ensures result matches Ok(id) ==> id > 0,
        junco_core::verify::history_specs::no_invariant_failure(result),
        result matches Err(error) ==> error == (HistoryError::IdExhausted { domain: "store" }),
{
    let (id, _receipt) = allocate_store_id(Ghost(arbitrary()))?;
    Ok(id)
}

impl<E: Event> Store<E> {
    /// Create an empty typed view. Store-ID exhaustion is reported before wrapping.
    pub fn new() -> (result: Result<Self, HistoryError>)
        ensures result matches Ok(store) ==> store_wf(store),
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> error == (HistoryError::IdExhausted { domain: "store" }),
    {
        let tracked (mut authority, empty) = vstd::resource::map::GhostMapAuth::new(
            Map::<usize, vstd::resource::Loc>::empty());
        let ghost registry = authority.id();
        let tracked birth = authority.insert(0, registry);
        let (id, _receipt) = allocate_store_id(Ghost(registry))?;
        let state = Codebooks::new(Ghost(id), Tracked(authority));
        let books = NativeBooks::new(state, Tracked(&birth));
        Ok(Self { id, books, numeric_store: HistoryStore::new(E::Arity::value()),
            #[cfg(verus_keep_ghost)]
            history_registry: Ghost(registry),
            #[cfg(verus_keep_ghost)]
            store_id_receipt: _receipt,
            #[cfg(verus_keep_ghost)]
            registry_birth: Tracked(birth),
        })
    }

    /// Return the numeric store shared by every typed view and byte history of this arity.
    pub fn numeric_store(&self) -> (result: &Arc<HistoryStore>)
        ensures *result == numeric_owner(*self),
            store_wf(*self) ==> *result == crate::store::verify::singleton_store(arity::<E>())
                && crate::store::verify::numeric_store_wf(**result)
                && result.arity_spec() == arity::<E>(),
    {
        &self.numeric_store
    }

    pub(crate) fn id(&self) -> (result: u64)
        ensures result == store_id(*self),
    {
        self.id
    }
    pub(crate) proof fn store_id_receipt_ref(tracked &self) -> (tracked result: &StoreIdReceipt)
        requires store_wf(*self),
        ensures result.id() == store_id_authority(), result.key() == self.id,
            result.value() == self.history_registry@,
    { self.store_id_receipt.borrow() }

    #[cfg(verus_keep_ghost)]
    pub(crate) fn allocate_history_id(&self) -> (result: Result<usize, HistoryError>)
        requires store_wf(*self),
        ensures result matches Ok(id) ==> 0 < id < usize::MAX,
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> error == (HistoryError::IdExhausted { domain: "history" }),
    {
        let (id, _registration, _receipt) = self.allocate_history_id_for_resource(Ghost(arbitrary()), Tracked(None))?;
        Ok(id)
    }

    /// The checked allocation body publishes an immutable resource-backed receipt.
    pub(crate) fn allocate_history_id_for_resource(&self,
        Ghost(location): Ghost<vstd::resource::Loc>, Tracked(prior): Tracked<Option<&HistoryRegistration>>)
        -> (result: Result<(usize, Tracked<HistoryRegistration>, Tracked<crate::store::HistoryKeyReceipt>), HistoryError>)
        requires store_wf(*self),
            match prior { Some(registration) => registration.id() == registry_id(self), None => true },
        ensures result matches Ok((id, registration, receipt)) ==> 0 < id < usize::MAX
            && registration@.id() == registry_id(self) && registration@.key() == id
            && registration@.value() == location
            && receipt@.id() == crate::store::verify::history_authority() && receipt@.key() == id
            && receipt@.value() == (crate::store::HistoryIssuer::Typed {
                store: registry_id(self), lifecycle: location })
            && match prior { Some(previous) => previous.key() < id, None => true },
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> error == (HistoryError::IdExhausted { domain: "history" }),
    {
        proof { if junco_core::spec::hypotheses::event_obligations::<E>() { lemma_empty_maps_wf::<E>(); } }
        let ghost owner = self.id;
        let ghost registry = self.history_registry@;
        self.books.with_books(Ghost(owner), Ghost(empty_maps::<E>()), Ghost(empty_maps::<E>()), Ghost(registry),
            &*self.numeric_store,
            |books: &mut Codebooks<E>, numeric_store: &HistoryStore| -> (result: Result<(usize, Tracked<HistoryRegistration>, Tracked<crate::store::HistoryKeyReceipt>), HistoryError>)
                requires books_acquired(*old(books), owner, registry, empty_maps::<E>(), empty_maps::<E>()),
                    crate::store::verify::numeric_store_wf(*numeric_store),
                    match prior { Some(previous) => previous.id() == registry, None => true },
                ensures publication_frame(*old(books), *final(books)),
                    junco_core::verify::history_specs::no_invariant_failure(result),
                    result matches Err(error) ==> error == (HistoryError::IdExhausted { domain: "history" }),
                    result matches Ok((id, registration, receipt)) ==> 0 < id < usize::MAX
                        && registration@.id() == registry && registration@.key() == id
                        && registration@.value() == location
                        && receipt@.id() == crate::store::verify::history_authority() && receipt@.key() == id
                        && receipt@.value() == (crate::store::HistoryIssuer::Typed {
                            store: registry, lifecycle: location })
                        && match prior { Some(previous) => previous.key() < id, None => true },
            {
                books.allocate_history_id_for_resource(numeric_store, Ghost(location), Tracked(prior))
            })
    }

    pub(crate) fn encode_event(&self, event: &E) -> (result: Result<NumericEvent, HistoryError>)
        requires store_wf(*self),
        ensures result matches Ok(numeric) ==> numeric@.len() == arity::<E>(),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> (result matches Ok(numeric) ==>
            exists|maps: ComponentMaps<E>| snapshot_published::<E>(registry_id(self), maps)
                && maps_wf::<E>(maps) && event_encoded::<E>(maps, *event, numeric)),
            junco_core::verify::history_specs::no_invariant_failure(result),
            !(result matches Err(HistoryError::InvalidPolicy { .. })),
            result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
    {
        proof { if junco_core::spec::hypotheses::event_obligations::<E>() { lemma_empty_maps_wf::<E>(); } }
        let (result, _) = self.encode_event_with_snapshot(event,
            Ghost(empty_maps::<E>()), Ghost(empty_maps::<E>()));
        result
    }

    /// Extend two previously published finite snapshots under one lock acquisition.
    pub fn encode_event_with_snapshot(&self, event: &E,
        Ghost(first): Ghost<ComponentMaps<E>>, Ghost(second): Ghost<ComponentMaps<E>>)
        -> (result: (Result<NumericEvent, HistoryError>, Ghost<ComponentMaps<E>>))
        requires store_wf(*self),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> maps_wf::<E>(first)
                && snapshot_published::<E>(registry_id(self), first) && maps_wf::<E>(second)
                && snapshot_published::<E>(registry_id(self), second),
        ensures snapshot_published::<E>(registry_id(self), result.1@),
            result.0 != Err(HistoryError::WrongHistoryOwner),
            result.0 matches Ok(numeric) ==> numeric@.len() == arity::<E>(),
            junco_core::verify::history_specs::no_invariant_failure(result.0),
            !(result.0 matches Err(HistoryError::InvalidPolicy { .. })),
            result.0 matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> maps_wf::<E>(result.1@)
                && maps_extend::<E>(first, result.1@) && maps_extend::<E>(second, result.1@)
                && (result.0 matches Ok(numeric) ==> event_encoded::<E>(result.1@, *event, numeric)),
    {
        let ghost owner = self.id;
        let ghost registry = self.history_registry@;
        self.books.with_books(Ghost(owner), Ghost(first), Ghost(second), Ghost(registry), &*self.numeric_store,
            |books: &mut Codebooks<E>, numeric_store: &HistoryStore| -> (output: (Result<NumericEvent, HistoryError>, Ghost<ComponentMaps<E>>))
                requires books_acquired(*old(books), owner, registry, first, second),
                    crate::store::verify::numeric_store_wf(*numeric_store),
                    numeric_store.arity_spec() == arity::<E>(),
                ensures publication_frame(*old(books), *final(books)),
                    output.0 != Err(HistoryError::WrongHistoryOwner),
                    output.0 matches Ok(numeric) ==> numeric@.len() == arity::<E>(),
                    junco_core::verify::history_specs::no_invariant_failure(output.0),
                    !(output.0 matches Err(HistoryError::InvalidPolicy { .. })),
                    output.0 matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
                    output.1@ == books_maps(*final(books)),
                    junco_core::spec::hypotheses::event_obligations::<E>() ==> maps_wf::<E>(output.1@)
                        && maps_extend::<E>(first, output.1@) && maps_extend::<E>(second, output.1@)
                        && (output.0 matches Ok(numeric) ==> event_encoded::<E>(output.1@, *event, numeric)),
            {
                let ghost initial = books_maps(*books);
                let ghost initial_registry = books.components.registry@;
                let result = {
                    let mut encoder = BorrowedEncoder { books: &mut books.components, numeric_store,
                        #[cfg(verus_keep_ghost)] calls: Ghost(0nat) };
                    encoder.encode_event(event)
                };
                let ghost maps = books_maps(*books);
                proof {
                    assert(component_receipts_wf(books.components));
                    assert(books.components.registry@ == initial_registry);
                    assert(components_wf(books.components));
                    if junco_core::spec::hypotheses::event_obligations::<E>() {
                        lemma_component_maps_wf(books.components);
                        junco_core::verify::encoding::lemma_extends_transitive(first, initial, maps,
                            junco_core::verify::flatten::component_equality::<E>());
                        junco_core::verify::encoding::lemma_extends_transitive(second, initial, maps,
                            junco_core::verify::flatten::component_equality::<E>());
                    }
                }
                (result, Ghost(maps))
            })
    }

    /// Validate/encode constants while holding the same single lock used by requests.
    pub fn lower_with_snapshot<L: Limits>(&self, source: &FlatPair<E::Component>,
        limits: &mut L, world: &mut ObservationWorld, Ghost(prior): Ghost<ComponentMaps<E>>)
        -> (result: (Result<FlatPair<u64>, HistoryError>, Ghost<ComponentMaps<E>>))
        requires store_wf(*self),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> maps_wf::<E>(prior)
                && snapshot_published::<E>(registry_id(self), prior),
        ensures result.0 matches Ok(numeric) ==> junco_core::flat::verify::structural_wf(numeric),
            snapshot_published::<E>(registry_id(self), result.1@),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> junco_core::verify::history_specs::no_invariant_failure(result.0),
            junco_core::spec::hypotheses::event_obligations::<E>() && junco_core::flat::verify::structural_wf(*source)
                && junco_core::verify::encoding::constants_in_domain(*source, domain::<E>())
                ==> !(result.0 matches Err(HistoryError::InvalidPolicy { .. })),
            junco_core::spec::hypotheses::event_obligations::<E>() && junco_core::flat::verify::structural_wf(*source)
                && junco_core::verify::encoding::constants_in_domain(*source, domain::<E>())
                ==> (result.0 matches Err(error) ==> junco_core::spec::semantics::resource_error(error)),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> maps_wf::<E>(result.1@)
                && maps_extend::<E>(prior, result.1@)
                && (result.0 matches Ok(numeric) ==>
                    junco_core::verify::encoding::lowering(*source, numeric, result.1@,
                        junco_core::verify::flatten::component_equality::<E>())
                    && junco_core::verify::encoding::constants_in_domain(*source, domain::<E>())),
    {
        let ghost owner = self.id;
        let ghost registry = self.history_registry@;
        self.books.with_books(Ghost(owner), Ghost(prior), Ghost(prior), Ghost(registry),
            (limits, world, &*self.numeric_store),
            |books: &mut Codebooks<E>, context: (&mut L, &mut ObservationWorld, &HistoryStore)|
                -> (output: (Result<FlatPair<u64>, HistoryError>, Ghost<ComponentMaps<E>>))
                requires books_acquired(*old(books), owner, registry, prior, prior),
                    crate::store::verify::numeric_store_wf(*context.2),
                    context.2.arity_spec() == arity::<E>(),
                ensures publication_frame(*old(books), *final(books)),
                    output.1@ == books_maps(*final(books)),
                    output.0 matches Ok(numeric) ==> junco_core::flat::verify::structural_wf(numeric),
                    junco_core::spec::hypotheses::event_obligations::<E>() ==> junco_core::verify::history_specs::no_invariant_failure(output.0),
                    junco_core::spec::hypotheses::event_obligations::<E>() && junco_core::flat::verify::structural_wf(*source)
                        && junco_core::verify::encoding::constants_in_domain(*source, domain::<E>())
                        ==> !(output.0 matches Err(HistoryError::InvalidPolicy { .. })),
                    junco_core::spec::hypotheses::event_obligations::<E>() && junco_core::flat::verify::structural_wf(*source)
                        && junco_core::verify::encoding::constants_in_domain(*source, domain::<E>())
                        ==> (output.0 matches Err(error) ==> junco_core::spec::semantics::resource_error(error)),
                    junco_core::spec::hypotheses::event_obligations::<E>() ==> maps_wf::<E>(output.1@) && maps_extend::<E>(prior, output.1@)
                        && (output.0 matches Ok(numeric) ==>
                            junco_core::verify::encoding::lowering(*source, numeric, output.1@,
                                junco_core::verify::flatten::component_equality::<E>())
                            && junco_core::verify::encoding::constants_in_domain(*source, domain::<E>())),
            {
                let (limits, world, numeric_store) = context;
                let ghost initial = books_maps(*books);
                let ghost initial_registry = books.components.registry@;
                proof { if junco_core::spec::hypotheses::event_obligations::<E>() { lemma_component_maps_wf(books.components); } }
                let result = {
                    let mut encoder = BorrowedEncoder { books: &mut books.components, numeric_store,
                        #[cfg(verus_keep_ghost)] calls: Ghost(0nat) };
                    lower_flat(source, &mut encoder, limits, world)
                };
                let ghost maps = books_maps(*books);
                proof {
                    assert(component_receipts_wf(books.components));
                    assert(books.components.registry@ == initial_registry);
                    assert(components_wf(books.components));
                    if junco_core::spec::hypotheses::event_obligations::<E>() {
                        junco_core::verify::encoding::lemma_extends_transitive(prior, initial, maps,
                            junco_core::verify::flatten::component_equality::<E>());
                    }
                }
                (result, Ghost(maps))
            })
    }
}

/// A scoped encoder borrows codebooks and the process allocator, restoring receipt validity and registry identity.
pub(crate) struct BorrowedEncoder<'a, E: Event> {
    pub(crate) books: &'a mut ComponentBooks<E>,
    pub(crate) numeric_store: &'a HistoryStore,
    #[cfg(verus_keep_ghost)]
    pub(crate) calls: Ghost<nat>,
}

impl<'a, E: Event> FlatEncoder<E::Component> for BorrowedEncoder<'a, E> {
    open spec fn equality() -> junco_core::verify::encoding::Equality<E::Component> {
        junco_core::verify::flatten::component_equality::<E>()
    }
    open spec fn domain() -> junco_core::verify::encoding::Domain<E::Component> { domain::<E>() }
    open(crate) spec fn maps(&self) -> ComponentMaps<E> { component_maps(*self.books) }
    open(crate) spec fn encoding_calls(&self) -> nat { self.calls@ }
    open(crate) spec fn state_wf(&self) -> bool {
        component_receipts_wf(*self.books)
            && crate::store::verify::numeric_store_wf(*self.numeric_store)
            && self.numeric_store.arity_spec() == arity::<E>()
    }
    open(crate) spec fn obeys_encoding_spec(&self) -> bool {
        junco_core::spec::hypotheses::event_obligations::<E>() && components_wf(*self.books)
    }
    open spec fn errors_are_non_invariant(&self) -> bool { true }
    open spec fn errors_are_resource(&self) -> bool { true }

    #[verifier::prophetic]
    open(crate) spec fn restoration(&self) -> (ComponentMaps<E>, bool) {
        let restored = mut_ref_future(self.books);
        (component_maps(restored), components_wf(restored)
            && restored.registry@ == self.books.registry@)
    }

    fn encode(&mut self, field: Component, value: &E::Component)
        -> (result: Result<u64, HistoryError>)
        ensures encoder_frame(*old(self), *final(self)),
            result != Err(HistoryError::WrongHistoryOwner),
            junco_core::verify::history_specs::no_invariant_failure(result),
            junco_core::spec::hypotheses::event_obligations::<E>() && domain::<E>()(field, *value)
                ==> !(result matches Err(HistoryError::InvalidPolicy { .. })),
            junco_core::spec::hypotheses::event_obligations::<E>() && domain::<E>()(field, *value)
                ==> (result matches Err(error) ==> junco_core::spec::semantics::resource_error(error)),
    {
        proof {
            self.calls = Ghost(self.calls@ + 1);
            junco_core::verify::encoding::lemma_grows_by_refl(component_maps(*self.books), junco_core::verify::encoding::only_value(field, *value));
        }
        validate_component::<E>(field, value)?;
        let index = field.index();
        if index >= self.books.books.len() {
            return Err(HistoryError::invalid_policy("$", "constant belongs to another component"));
        }
        self.intern_component(index, value)
    }
}

impl<'a, E: Event> BorrowedEncoder<'a, E> {
    // Requests obtain the coordinate from their position, not from untrusted native key code.
    // Constant encoding checks that position before reaching this common receipt-preserving path.
    fn intern_component(&mut self, index: usize, value: &E::Component)
        -> (result: Result<u64, HistoryError>)
        requires old(self).state_wf(), index < arity::<E>(),
            junco_core::spec::hypotheses::event_obligations::<E>() && components_wf(*old(self).books)
                ==> domain::<E>()(Component(index as u8), *value),
        ensures final(self).state_wf(), encoder_frame(*old(self), *final(self)),
            final(self).restoration() == old(self).restoration(),
            final(self).calls == old(self).calls,
            result != Err(HistoryError::WrongHistoryOwner),
            junco_core::verify::history_specs::no_invariant_failure(result),
            result matches Err(error) ==> error == HistoryError::AllocationFailed
                || error == (HistoryError::IdExhausted { domain: "component" }),
            junco_core::spec::hypotheses::event_obligations::<E>() && components_wf(*old(self).books) ==>
                maps_wf::<E>(component_maps(*final(self).books))
                && maps_extend::<E>(component_maps(*old(self).books), component_maps(*final(self).books))
                && junco_core::verify::encoding::grows_by(component_maps(*old(self).books), component_maps(*final(self).books),
                    junco_core::verify::encoding::only_value(Component(index as u8), *value))
                && (result matches Ok(id) ==> junco_core::verify::encoding::encoded(
                    component_maps(*final(self).books), Self::equality(), Component(index as u8), *value, id)),
    {
        let ghost initial = *self.books;
        let ghost initial_wf = components_wf(initial);
        let result = self.books.books[index].intern(value, index, "component", self.numeric_store,
            Ghost(crate::store::ComponentIssuer::Typed(self.books.registry@)));
        proof {
            assert forall|i: int| 0 <= i < arity::<E>() implies
                book_receipts_wf(self.books.books@[i], i,
                    crate::store::ComponentIssuer::Typed(self.books.registry@)) by {
                if i != index { assert(self.books.books@[i] == initial.books@[i]); }
            }
            assert(component_receipts_wf(*self.books));
            if junco_core::spec::hypotheses::event_obligations::<E>() && initial_wf {
                assert forall|i: int| 0 <= i < arity::<E>() implies
                    book_wf(self.books.books@[i])
                    && (forall|j: int| 0 <= j < book_entries(self.books.books@[i]).len() ==>
                        E::coordinate_spec(book_entries(self.books.books@[i])[j].0) == i) by {
                    if i == index {
                        let before = book_entries(initial.books@[i]);
                        let after = book_entries(self.books.books@[i]);
                        assert forall|j: int| 0 <= j < after.len() implies
                            E::coordinate_spec(after[j].0) == i by {
                            if j < before.len() { assert(after[j] == before[j]); }
                            else { assert(after[j].0 == *value); }
                        }
                    } else { assert(self.books.books@[i] == initial.books@[i]); }
                }
                assert(components_wf(*self.books));
                assert forall|i: int| 0 <= i < arity::<E>() implies
                    book_entries(initial.books@[i]).is_prefix_of(book_entries(self.books.books@[i])) by {
                    if i != index { assert(self.books.books@[i] == initial.books@[i]); }
                }
                lemma_component_maps_wf(*self.books);
                lemma_component_maps_extend(initial, *self.books);
                assert forall|i: int| 0 <= i < arity::<E>() && i != index
                    implies self.books.books@[i] == initial.books@[i] by {}
                if let Ok(id) = result {
                    assert(book_entries(self.books.books@[index as int]) == book_entries(initial.books@[index as int])
                        || book_entries(self.books.books@[index as int]) == book_entries(initial.books@[index as int]).push((*value, id)));
                }
                lemma_component_maps_grow(initial, *self.books, index as int, *value);
                if let Ok(id) = result {
                    lemma_component_book_encoded(*self.books, Component(index as u8), *value, id);
                }
            }
        }
        result
    }

    fn encode_event(&mut self, event: &E) -> (result: Result<NumericEvent, HistoryError>)
        requires old(self).state_wf(), components_wf(*old(self).books),
        ensures final(self).state_wf(), components_wf(*final(self).books),
            result matches Ok(numeric) ==> numeric@.len() == arity::<E>(),
            result != Err(HistoryError::WrongHistoryOwner),
            junco_core::verify::history_specs::no_invariant_failure(result),
            !(result matches Err(HistoryError::InvalidPolicy { .. })),
            result matches Err(error) ==> junco_core::spec::semantics::resource_error(error),
            final(self).books.registry@ == old(self).books.registry@,
            junco_core::spec::hypotheses::event_obligations::<E>() ==>
            maps_extend::<E>(component_maps(*old(self).books), component_maps(*final(self).books))
            && (result matches Ok(numeric) ==> event_encoded::<E>(component_maps(*final(self).books), *event, numeric)),
            final(self).restoration() == old(self).restoration(),
    {
        let width = E::Arity::value();
        let mut slots = [0u64; MAX_ARITY];
        let ghost before = component_maps(*self.books);
        let ghost registry = self.books.registry@;
        let ghost restored = self.restoration();
        let mut index = 0;
        while index < width
            invariant index <= width, width == arity::<E>(), 1 <= width <= MAX_ARITY,
                self.state_wf(), components_wf(*self.books), self.books.registry@ == registry,
                registry == old(self).books.registry@,
                self.restoration() == restored, restored == old(self).restoration(),
                before == component_maps(*old(self).books),
                junco_core::spec::hypotheses::event_obligations::<E>() ==> maps_extend::<E>(before, component_maps(*self.books)),
                junco_core::spec::hypotheses::event_obligations::<E>() ==> forall|i: int| 0 <= i < index ==>
                    junco_core::verify::encoding::encoded(component_maps(*self.books), Self::equality(),
                        Component(i as u8), event_view(*event)[i], slots@[i]),
            decreases width - index,
        {
            let value = event.component(index);
            let ghost previous = component_maps(*self.books);
            let result = self.intern_component(index, &value);
            proof {
                if junco_core::spec::hypotheses::event_obligations::<E>() {
                    junco_core::verify::encoding::lemma_extends_transitive(before, previous,
                        component_maps(*self.books), Self::equality());
                    assert(before.len() == previous.len());
                    assert(previous.len() == component_maps(*self.books).len());
                    assert(maps_extend::<E>(before, component_maps(*self.books)));
                    assert forall|i: int| 0 <= i < index implies
                        junco_core::verify::encoding::encoded(component_maps(*self.books), Self::equality(),
                            Component(i as u8), event_view(*event)[i], slots@[i]) by {
                        assert(junco_core::verify::encoding::encoded(previous, Self::equality(),
                            Component(i as u8), event_view(*event)[i], slots@[i]));
                    }
                }
            }
            slots[index] = result?;
            index += 1;
        }
        let numeric = NumericEvent::from_encoded(&slots[..width]);
        proof {
            assert forall|i: int| 0 <= i < width implies numeric_values(numeric)[i] == slots@[i] by {}
            if junco_core::spec::hypotheses::event_obligations::<E>() {
                assert forall|i: int| 0 <= i < width implies
                    domain::<E>()(Component(i as u8), event_view(*event)[i]) by {}
            }
        }
        Ok(numeric)
    }
}
}

impl<E: Event> core::fmt::Debug for Store<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Store")
            .field("id", &self.id)
            .finish_non_exhaustive()
    }
}

#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    use junco_core::verify::encoding;
    use junco_core::verify::flatten::component_equality;
    use vstd::std_specs::option::OptionAdditionalFns;
    verus! {

    pub type ComponentMaps<E> = super::ComponentMaps<E>;
    pub type HistoryRegistration = super::HistoryRegistration;

    /// Native allocation identity, independent of codebook and registry identities.
    pub closed spec fn same_store_owner<E: Event>(left: Arc<Store<E>>, right: Arc<Store<E>>) -> bool {
        arc_identity(left) == arc_identity(right)
    }

    pub proof fn lemma_same_store_owner_identity<E: Event>(left: Arc<Store<E>>, right: Arc<Store<E>>)
        ensures same_store_owner(left, right) == (arc_identity(left) == arc_identity(right)),
    {}

    pub(crate) proof fn empty_store_id_authority() -> (tracked result: StoreIdAuth)
        ensures result@ == Map::<u64, vstd::resource::Loc>::empty(),
    {
        let tracked (authority, empty) = StoreIdAuth::new(Map::empty());
        authority
    }

    pub open(crate) spec fn store_id_state_wf(state: StoreIdState) -> bool {
        forall|id: u64| #[trigger] (state.issued@)@.contains_key(id)
            <==> 0 < id <= state.last
    }

    pub open(crate) spec fn store_id_state_frame(before: StoreIdState, after: StoreIdState) -> bool {
        store_id_state_wf(after) && before.issued@.id() == after.issued@.id()
            && before.last <= after.last && (before.issued@)@ <= (after.issued@)@
    }

    pub(crate) uninterp spec fn store_ids_authority_id(ids: NativeStoreIds) -> vstd::resource::Loc;
    pub(crate) uninterp spec fn process_store_ids() -> NativeStoreIds;
    pub open(super) spec fn store_id_authority() -> vstd::resource::Loc {
        store_ids_authority_id(process_store_ids())
    }
    pub(crate) uninterp spec fn store_ids_mutex_valid(ids: NativeStoreIds) -> bool;

    pub open(crate) spec fn store_id_state_acquired(state: StoreIdState, ids: NativeStoreIds) -> bool {
        store_id_state_wf(state) && state.issued@.id() == store_ids_authority_id(ids)
    }

    pub open(crate) spec fn store_id_issue_result(before: StoreIdState, after: StoreIdState,
        registry: vstd::resource::Loc,
        result: Result<(u64, Tracked<StoreIdReceipt>), HistoryError>) -> bool {
        &&& store_id_state_frame(before, after)
        &&& match result {
            Ok((id, receipt)) => {
                &&& before.last < u64::MAX
                &&& id == before.last + 1
                &&& after.last == id
                &&& (after.issued@)@ == (before.issued@)@.insert(id, registry)
                &&& receipt@.id() == after.issued@.id()
                &&& receipt@.key() == id
                &&& receipt@.value() == registry
                &&& 0 < id <= after.last
            },
            Err(error) => {
                &&& before.last == u64::MAX
                &&& after.last == before.last
                &&& (after.issued@)@ == (before.issued@)@
                &&& error == HistoryError::IdExhausted { domain: "store" }
            },
        }
    }

    // Dropping the first consumer's receipt cannot recycle its authoritative entry.
    pub(crate) fn store_id_state_nonrecycling_client(Ghost(registry): Ghost<vstd::resource::Loc>)
        -> (result: StoreIdState)
        ensures store_id_state_wf(result), result.last == 2,
            (result.issued@)@ == map![1u64 => registry, 2u64 => registry],
    {
        let mut state = StoreIdState::new();
        {
            let first = issue_store_id(&mut state, Ghost(registry));
            assert(first matches Ok((id, _)) && id == 1);
        }
        let second = issue_store_id(&mut state, Ghost(registry));
        assert(second matches Ok((id, _)) && id == 2);
        state
    }

    pub(crate) fn store_id_state_max_client(state: &mut StoreIdState,
        Ghost(registry): Ghost<vstd::resource::Loc>)
        requires store_id_state_wf(*old(state)), old(state).last == u64::MAX - 1,
        ensures store_id_state_wf(*final(state)), final(state).last == u64::MAX,
            final(state).issued@.id() == old(state).issued@.id(),
            (final(state).issued@)@ == (old(state).issued@)@.insert(u64::MAX, registry),
    {
        let first = issue_store_id(state, Ghost(registry));
        assert(first matches Ok((id, _)) && id == u64::MAX);
        let ghost issued = (state.issued@)@;
        let second = issue_store_id(state, Ghost(registry));
        assert(second == Err(HistoryError::IdExhausted { domain: "store" }));
        assert((state.issued@)@ == issued);
    }

    pub(crate) proof fn lemma_registry_births_distinct(
        tracked left: &mut RegistryBirth, tracked right: &RegistryBirth)
        requires old(left).key() == 0, right.key() == 0,
        ensures final(left).id() == old(left).id(), final(left)@ == old(left)@,
            final(left).id() != right.id(),
    {
        if left.id() == right.id() {
            left.disjoint(right);
            assert(false);
        }
    }

    pub(crate) proof fn lemma_store_receipts_distinct(
        left_registry: vstd::resource::Loc, right_registry: vstd::resource::Loc,
        tracked left: &StoreIdReceipt, tracked right: &StoreIdReceipt)
        requires left.id() == right.id(), left.value() == left_registry,
            right.value() == right_registry, left_registry != right_registry,
        ensures left.key() != right.key(),
    {
        let tracked mut witness = left.duplicate();
        witness.intersection_agrees(right);
    }

    #[doc(hidden)]
    pub fn independently_constructed_stores_client<E: Event, F: Event>()
        -> (result: Result<(Store<E>, Store<F>), HistoryError>)
        ensures result matches Ok((left, right)) ==> store_wf(left) && store_wf(right)
            && registry_id(&left) != registry_id(&right) && store_id(left) != store_id(right),
    {
        let mut left = Store::<E>::new()?;
        let right = Store::<F>::new()?;
        proof {
            lemma_registry_births_distinct(left.registry_birth.borrow_mut(), right.registry_birth.borrow());
            lemma_store_receipts_distinct(left.history_registry@, right.history_registry@,
                left.store_id_receipt.borrow(), right.store_id_receipt.borrow());
        }
        Ok((left, right))
    }

    fn typed_component_receipt_client<E: Event>(store: &Store<E>, value: &E::Component, index: usize)
        -> (result: Result<(u64, Tracked<crate::store::ComponentIdReceipt>), HistoryError>)
        requires store_wf(*store), index < arity::<E>(), junco_core::spec::hypotheses::key_laws::<E::Component>(),
        ensures result matches Ok((id, receipt)) ==> receipt@.key() == id
            && receipt@.id() == crate::store::verify::coordinate_authority(index as int)
            && receipt@.value() == crate::store::ComponentIssuer::Typed(store.history_registry@),
    {
        let mut book = Codebook::<E::Component>::new();
        let id = book.intern(value, index, "component", store.numeric_store(),
            Ghost(crate::store::ComponentIssuer::Typed(store.history_registry@)))?;
        let tracked receipt;
        proof {
            let ghost entries = book_entries(book);
            let ghost i = choose|i: int| 0 <= i < entries.len()
                && entries[i].1 == id && value.eq_spec(&entries[i].0);
            let ghost ids = entries.map(|i: int, pair: (E::Component, u64)| pair.1);
            assert(ids[i] == id);
            assert(ids.to_set().contains(id));
            assert(book.issued@ is Some);
            let tracked held = book.issued.borrow().tracked_borrow();
            let tracked mut aggregate = held.duplicate();
            assert(aggregate@.contains_key(id));
            receipt = aggregate.split_points_to(id);
        }
        Ok((id, Tracked(receipt)))
    }

    pub(crate) fn component_receipts_client<E: Event, F: Event, L: Limits>(
        left: &Store<E>, right: &Store<F>, first: &E::Component, second: &F::Component,
        component: Component, bytes: &[u8], limits: &mut L, world: &mut ObservationWorld)
        -> (result: Result<(u64, u64, u64), HistoryError>)
        requires store_wf(*left), store_wf(*right), component.0 < arity::<E>(),
            component.0 < arity::<F>(), left.history_registry@ != right.history_registry@,
            junco_core::spec::hypotheses::key_laws::<E::Component>(), junco_core::spec::hypotheses::key_laws::<F::Component>(),
        ensures result matches Ok((byte, first, second)) ==>
            byte != first && byte != second && first != second,
    {
        let index = component.index();
        let (byte, Tracked(binding)) = left.numeric_store().intern_observed(component, bytes, limits, world)?;
        let tracked byte_receipt = binding.issuer_receipt();
        let (first, Tracked(first_receipt)) = typed_component_receipt_client(left, first, index)?;
        let (second, Tracked(second_receipt)) = typed_component_receipt_client(right, second, index)?;
        proof {
            let tracked mut byte_witness = byte_receipt.duplicate();
            byte_witness.intersection_agrees(&first_receipt);
            byte_witness.intersection_agrees(&second_receipt);
            let tracked mut typed_witness = first_receipt.duplicate();
            typed_witness.intersection_agrees(&second_receipt);
        }
        Ok((byte, first, second))
    }


    pub open spec fn domain<E: Event>() -> encoding::Domain<E::Component> {
        junco_core::verify::flatten::component_domain::<E>()
    }

    /// The event obligations make component equality an equivalence.
    pub proof fn lemma_native_obligations_eq_equivalence<E: Event>()
        requires junco_core::spec::hypotheses::event_obligations::<E>(),
        ensures junco_core::spec::hypotheses::eq_equivalence::<E::Component>(),
    {
    }

    /// Projection and arity facts available to typed-policy clients outside this crate.
    pub proof fn lemma_native_obligations_projection<E: Event>()
        requires junco_core::spec::hypotheses::event_obligations::<E>(),
        ensures E::obeys_projection_spec(), projection_laws::<E>(),
            1 <= arity::<E>() <= MAX_ARITY,
    {}

    pub open spec fn empty_maps<E: Event>() -> ComponentMaps<E> {
        Seq::new(arity::<E>(), |i: int| Seq::<(E::Component, u64)>::empty())
    }

    pub open spec fn maps_wf<E: Event>(maps: ComponentMaps<E>) -> bool {
        maps.len() == arity::<E>()
            && encoding::maps_wf(maps, component_equality::<E>(), domain::<E>())
    }
    pub open spec fn maps_extend<E: Event>(before: ComponentMaps<E>, after: ComponentMaps<E>) -> bool {
        before.len() == after.len() && encoding::extends(before, after, component_equality::<E>())
    }

    /// Persistent provenance scoped to the unique, linearly owned mutex registry resource.
    pub uninterp spec fn snapshot_published<E: Event>(registry: vstd::resource::Loc, maps: ComponentMaps<E>) -> bool;

    pub open(crate) spec fn store_id<E: Event>(store: Store<E>) -> u64 { store.id }
    pub open(super) spec fn numeric_owner<E: Event>(store: Store<E>) -> Arc<HistoryStore> { store.numeric_store }
    pub open(crate) spec fn store_wf<E: Event>(store: Store<E>) -> bool {
        store.id > 0 && mutex_valid(store.books, store.id, store.history_registry@)
            && snapshot_published::<E>(store.history_registry@, empty_maps::<E>())
            && store.numeric_store == crate::store::verify::singleton_store(arity::<E>())
            && crate::store::verify::numeric_store_wf(*store.numeric_store)
            && store.numeric_store.arity_spec() == arity::<E>()
            && store.store_id_receipt@.id() == store_id_authority()
            && store.store_id_receipt@.key() == store.id
            && store.store_id_receipt@.value() == store.history_registry@
            && store.registry_birth@.id() == store.history_registry@
            && store.registry_birth@.key() == 0
            && store.registry_birth@.value() == store.history_registry@
    }

    pub open(crate) spec fn registry_id<E: Event>(store: &Store<E>) -> vstd::resource::Loc {
        store.history_registry@
    }

    pub proof fn lemma_empty_snapshot<E: Event>(store: &Store<E>)
        requires store_wf(*store),
        ensures snapshot_published::<E>(registry_id(store), empty_maps::<E>()),
    {}


    pub proof fn registrations_agree(tracked left: &HistoryRegistration, tracked right: &HistoryRegistration)
        requires left.id() == right.id(), left.key() == right.key(),
        ensures left.value() == right.value(),
    {
        let tracked mut left_map = left.duplicate().submap();
        left_map.combine_points_to(right.duplicate());
    }


    pub open spec fn numeric_values(numeric: NumericEvent) -> Seq<u64> {
        numeric@.map(|i: int, value: nat| value as u64)
    }

    pub open spec fn event_encoded<E: Event>(maps: ComponentMaps<E>, raw: E, numeric: NumericEvent) -> bool {
        encoding::event_encoded(maps, component_equality::<E>(), domain::<E>(),
            event_view(raw), numeric_values(numeric))
            && junco_core::verify::encoding::event_representation(numeric_values(numeric), numeric@)
    }

    pub(crate) open(crate) spec fn book_entries<K: Copy + Eq + KeyHash>(book: Codebook<K>) -> Seq<(K, u64)> {
        book.values@
    }
    pub(crate) open(crate) spec fn book_wf<K: Copy + Eq + KeyHash>(book: Codebook<K>) -> bool {
        (forall|i: int| #![trigger book_entries(book)[i]]
            0 <= i < book_entries(book).len() ==> 0 < book_entries(book)[i].1 <= book.last)
            && (junco_core::spec::hypotheses::key_laws::<K>() ==> forall|i: int, j: int|
                0 <= i < book_entries(book).len() && 0 <= j < book_entries(book).len()
                ==> (book_entries(book)[i].0.eq_spec(&book_entries(book)[j].0)
                    == (book_entries(book)[i].1 == book_entries(book)[j].1)))
    }
    pub(crate) open(crate) spec fn book_encoded<K: Copy + Eq + KeyHash>(book: Codebook<K>, value: K, id: u64) -> bool {
        id > 0 && exists|i: int| 0 <= i < book_entries(book).len()
            && book_entries(book)[i].1 == id && value.eq_spec(&book_entries(book)[i].0)
    }
    pub(crate) open(crate) spec fn book_receipts_wf<K: Copy + Eq + KeyHash>(book: Codebook<K>,
        index: int, issuer: crate::store::ComponentIssuer) -> bool {
        match book.issued@ {
            None => book.last == 0
                && (junco_core::spec::hypotheses::key_laws::<K>() ==> book_entries(book).len() == 0),
            Some(receipts) => receipts.id() == crate::store::verify::coordinate_authority(index)
                && receipts@.contains_key(book.last)
                && (forall|id: u64| #[trigger] receipts@.contains_key(id) ==>
                    0 < id <= book.last && receipts@[id] == issuer)
                && (junco_core::spec::hypotheses::key_laws::<K>() ==> receipts@.dom() ==
                    book_entries(book).map(|i: int, pair: (K,u64)| pair.1).to_set()),
        }
    }
    pub(crate) open(crate) spec fn component_receipts_wf<E: Event>(books: ComponentBooks<E>) -> bool {
        books.books@.len() == arity::<E>() && 1 <= arity::<E>() <= MAX_ARITY
            && forall|index: int| 0 <= index < arity::<E>() ==>
                book_receipts_wf(books.books@[index], index,
                    crate::store::ComponentIssuer::Typed(books.registry@))
    }
    pub(crate) open(crate) spec fn components_wf<E: Event>(books: ComponentBooks<E>) -> bool {
        component_receipts_wf(books)
            && (junco_core::spec::hypotheses::event_obligations::<E>() ==> forall|index: int| 0 <= index < arity::<E>() ==>
                book_wf(books.books@[index])
                && forall|i: int| 0 <= i < book_entries(books.books@[index]).len() ==>
                    E::coordinate_spec(book_entries(books.books@[index])[i].0) == index)
    }
    pub open(crate) spec fn encoder_frame<'a, E: Event>(before: BorrowedEncoder<'a, E>, after: BorrowedEncoder<'a, E>) -> bool {
        before.books.registry@ == after.books.registry@
            && (components_wf(*before.books) ==> components_wf(*after.books))
    }
    pub(crate) open(crate) spec fn component_maps<E: Event>(books: ComponentBooks<E>) -> ComponentMaps<E> {
        books.books@.map(|i: int, book: Codebook<E::Component>| book_entries(book))
    }

    pub(crate) proof fn lemma_component_book_encoded<E: Event>(
        books: ComponentBooks<E>, field: Component, value: E::Component, id: u64)
        requires junco_core::spec::hypotheses::event_obligations::<E>(), components_wf(books),
            field.0 < arity::<E>(), domain::<E>()(field, value),
            book_encoded(books.books@[field.0 as int], value, id),
        ensures encoding::encoded(component_maps(books), component_equality::<E>(), field, value, id),
            domain::<E>()(field, value),
    {
        let f = field.0 as int;
        let entries = book_entries(books.books@[f]);
        let i = choose|i: int| 0 <= i < entries.len() && entries[i].1 == id
            && value.eq_spec(&entries[i].0);
        assert(component_maps(books)[f][i] == entries[i]);
    }
    pub(crate) open(crate) spec fn books_wf<E: Event>(books: Codebooks<E>) -> bool {
        components_wf(books.components) && books.components.registry@ == books.history_resources@.id()
    }
    pub(crate) open(crate) spec fn books_maps<E: Event>(books: Codebooks<E>) -> ComponentMaps<E> {
        component_maps(books.components)
    }
    pub(crate) open(crate) spec fn self_same_books<E: Event>(before: Codebooks<E>, after: Codebooks<E>) -> bool {
        before.components == after.components && before.owner@ == after.owner@
    }
    // Keys may be sparse: other views and byte records share the process allocator.
    pub(crate) open(crate) spec fn registry_wf<E: Event>(books: Codebooks<E>) -> bool {
        books.next_history > 0 && (books.history_resources@)@.contains_key(0)
            && (books.history_resources@)@[0] == books.history_resources@.id()
            && (forall|id: usize| (books.history_resources@)@.contains_key(id) ==> id < books.next_history)
            && match books.latest_history@ {
                None => books.next_history == 1,
                Some(receipt) => receipt.id() == crate::store::verify::history_authority()
                    && receipt.key() + 1 == books.next_history,
            }
    }
    pub(crate) uninterp spec fn mutex_valid<E: Event>(mutex: NativeBooks<E>, owner: u64, registry: vstd::resource::Loc) -> bool;

    pub(crate) open(crate) spec fn books_acquired<E: Event>(books: Codebooks<E>, owner: u64,
        registry: vstd::resource::Loc, first: ComponentMaps<E>, second: ComponentMaps<E>) -> bool {
        books.owner@ == owner && registry_wf(books) && books.history_resources@.id() == registry
            && books_wf(books)
            && (junco_core::spec::hypotheses::event_obligations::<E>() ==>
                maps_extend::<E>(first, books_maps(books)) && maps_extend::<E>(second, books_maps(books)))
    }

    pub(crate) open(crate) spec fn publication_frame<E: Event>(before: Codebooks<E>, after: Codebooks<E>) -> bool {
        before.owner@ == after.owner@ && registry_wf(after)
            && before.components.registry@ == after.components.registry@ && books_wf(after)
            && before.history_resources@.id() == after.history_resources@.id()
            && (before.history_resources@)@.submap_of((after.history_resources@)@)
            && (junco_core::spec::hypotheses::event_obligations::<E>() ==> books_wf(after) && maps_extend::<E>(books_maps(before), books_maps(after)))
    }

    pub proof fn lemma_empty_maps_wf<E: Event>()
        requires junco_core::spec::hypotheses::event_obligations::<E>(),
        ensures maps_wf::<E>(empty_maps::<E>()),
    {}

    pub(super) proof fn lemma_component_maps_wf<E: Event>(books: ComponentBooks<E>)
        requires components_wf(books),
        ensures junco_core::spec::hypotheses::event_obligations::<E>() ==> maps_wf::<E>(component_maps(books)),
    {
        if junco_core::spec::hypotheses::event_obligations::<E>() {
            assert(encoding::equality_laws(component_equality::<E>(), domain::<E>()));
            assert forall|f: int, i: int| 0 <= f < arity::<E>() && 0 <= i < component_maps(books)[f].len()
                implies domain::<E>()(encoding::field_at(f), component_maps(books)[f][i].0)
                    && component_maps(books)[f][i].1 > 0 by {
                assert(component_maps(books)[f] == book_entries(books.books@[f]));
            }
            assert forall|f: int, i: int, j: int| 0 <= f < arity::<E>()
                && 0 <= i < component_maps(books)[f].len() && 0 <= j < component_maps(books)[f].len()
                implies (component_equality::<E>()(encoding::field_at(f), component_maps(books)[f][i].0,
                    component_maps(books)[f][j].0) == (component_maps(books)[f][i].1 == component_maps(books)[f][j].1)) by {
                assert(book_wf(books.books@[f]));
            }
        }
    }

    pub(super) proof fn lemma_component_maps_extend<E: Event>(before: ComponentBooks<E>, after: ComponentBooks<E>)
        requires before.books@.len() == after.books@.len(),
            forall|f: int| 0 <= f < before.books@.len() ==>
                book_entries(before.books@[f]).is_prefix_of(book_entries(after.books@[f])),
        ensures maps_extend::<E>(component_maps(before), component_maps(after)),
    {
        assert forall|field: Component, value: E::Component, id: u64|
            encoding::encoded(component_maps(before), component_equality::<E>(), field, value, id)
            implies encoding::encoded(component_maps(after), component_equality::<E>(), field, value, id) by {
            let f = junco_core::flat::verify::field_index(field);
            let i = choose|i: int| 0 <= i < component_maps(before)[f].len() && component_maps(before)[f][i].1 == id
                && component_equality::<E>()(field, value, component_maps(before)[f][i].0);
            assert(book_entries(before.books@[f]).is_prefix_of(book_entries(after.books@[f])));
            assert(component_maps(after)[f][i] == component_maps(before)[f][i]);
        }
    }

    /// One `intern` at `index` adds at most the interned value to the books.
    pub(super) proof fn lemma_component_maps_grow<E: Event>(before: ComponentBooks<E>, after: ComponentBooks<E>,
        index: int, value: E::Component)
        requires before.books@.len() == after.books@.len(), 0 <= index < before.books@.len(),
            forall|f: int| 0 <= f < before.books@.len() && f != index ==> after.books@[f] == before.books@[f],
            book_entries(after.books@[index]) == book_entries(before.books@[index])
                || exists|id: u64| book_entries(after.books@[index]) == book_entries(before.books@[index]).push((value, id)),
        ensures encoding::grows_by(component_maps(before), component_maps(after), encoding::only_value(Component(index as u8), value)),
    {
        let b = component_maps(before);
        let a = component_maps(after);
        assert forall|f: int, i: int| #![trigger a[f][i]] 0 <= f < a.len() && 0 <= i < a[f].len()
            implies (exists|j: int| 0 <= j < b[f].len() && (#[trigger] b[f][j]).0 == a[f][i].0)
                || encoding::only_value(Component(index as u8), value)(encoding::field_at(f), a[f][i].0) by {
            assert(a[f] == book_entries(after.books@[f]));
            assert(b[f] == book_entries(before.books@[f]));
            if f == index && i >= b[f].len() {
                assert(a[f][i].0 == value);
            } else {
                assert(a[f][i] == b[f][i]);
            }
        }
    }

    pub proof fn lemma_event_extension<E: Event>(before: ComponentMaps<E>, after: ComponentMaps<E>,
        raw: E, numeric: NumericEvent)
        requires maps_extend::<E>(before, after), event_encoded::<E>(before, raw, numeric),
        ensures event_encoded::<E>(after, raw, numeric),
    {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::hash::{Hash, Hasher};
    use history_syntax::{Component3, Component4, N3, N4};

    #[derive(Copy, Clone, Debug)]
    struct Key {
        identity: u8,
        payload: u8,
    }
    impl PartialEq for Key {
        fn eq(&self, other: &Self) -> bool {
            self.identity == other.identity
        }
    }
    impl Eq for Key {}
    impl Hash for Key {
        fn hash<H: Hasher>(&self, state: &mut H) {
            0u8.hash(state);
        }
    }
    impl history_syntax::KeyHash for Key {
        fn key_hash(&self) -> u64 {
            history_syntax::key_hash::hash_via_std(self)
        }
    }
    #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
    struct TestEvent(Key);
    impl Event for TestEvent {
        type Component = Component3<Key, Key, Key>;
        type Arity = N3;
        fn component(self, index: usize) -> Self::Component {
            match index {
                0 => Component3::C0(self.0),
                1 => Component3::C1(self.0),
                _ => Component3::C2(self.0),
            }
        }
        fn coordinate(component: Self::Component) -> usize {
            match component {
                Component3::C0(_) => 0,
                Component3::C1(_) => 1,
                Component3::C2(_) => 2,
            }
        }
    }

    #[test]
    fn checked_allocator_rejects_wrap_without_global_mutation() {
        assert_eq!(checked_successor(0, "store").unwrap(), 1);
        assert_eq!(checked_successor(u64::MAX - 1, "store").unwrap(), u64::MAX);
        assert!(matches!(
            checked_successor(u64::MAX, "store"),
            Err(HistoryError::IdExhausted { domain: "store" })
        ));
    }

    #[test]
    fn failed_allocation_preserves_reuse_and_collisions_are_not_identity() {
        let numeric = HistoryStore::new(3);
        let mut book = Codebook::new();
        let first = Key {
            identity: 7,
            payload: 1,
        };
        let equivalent = Key {
            identity: 7,
            payload: 2,
        };
        let other = Key {
            identity: 8,
            payload: 1,
        };
        assert_eq!(equivalent.payload, 2);
        let id = book
            .intern(&first, 0, "component", &numeric, Ghost::assume_new())
            .unwrap();
        assert_eq!(
            book.intern(&equivalent, 0, "component", &numeric, Ghost::assume_new())
                .unwrap(),
            id
        );
        // No shared-counter ID exceeds this book's newest one, so only reuse can succeed.
        book.last = u64::MAX;
        assert!(matches!(
            book.intern(&other, 0, "component", &numeric, Ghost::assume_new()),
            Err(HistoryError::Invariant { .. })
        ));
        assert_eq!(book.last, u64::MAX);
        assert_eq!(
            book.intern(&equivalent, 0, "component", &numeric, Ghost::assume_new())
                .unwrap(),
            id
        );
        assert_eq!(book.values.lookup(&other), None);
        let mut book = Codebook::new();
        let first_action = book
            .intern(&first, 1, "component", &numeric, Ghost::assume_new())
            .unwrap();
        assert!(
            book.intern(&other, 1, "component", &numeric, Ghost::assume_new())
                .unwrap()
                > first_action
        );
        assert_eq!(
            book.intern(&equivalent, 1, "component", &numeric, Ghost::assume_new())
                .unwrap(),
            first_action
        );
    }

    #[test]
    fn history_exhaustion_is_checked_and_does_not_change_codebooks() {
        // The shared counter's MAX boundary is covered by `store::next_history_id` on locals.
        let numeric = HistoryStore::new(3);
        let mut books = Codebooks::<TestEvent>::new(Ghost::assume_new(), Tracked::assume_new());
        books.next_history = usize::MAX;
        assert!(matches!(
            books.allocate_history_id(&numeric, Ghost::assume_new()),
            Err(HistoryError::IdExhausted { domain: "history" })
        ));
        assert_eq!(books.next_history, usize::MAX);
        assert!(books.components.books.iter().all(|book| book.last == 0));

        let store = alloc::sync::Arc::new(Store::<TestEvent>::new().unwrap());
        let history = crate::history::History::from_events(
            alloc::sync::Arc::clone(&store),
            [TestEvent(Key {
                identity: 7,
                payload: 1,
            })],
        )
        .unwrap();
        let raw = history.as_slice().to_vec();
        let numeric = history.numeric.events.clone();
        let revision = history.numeric.revision;
        store.books.inner.lock().next_history = usize::MAX;
        assert!(matches!(
            crate::history::History::new(alloc::sync::Arc::clone(&store)),
            Err(HistoryError::IdExhausted { domain: "history" })
        ));
        assert!(matches!(
            history.try_clone(),
            Err(HistoryError::IdExhausted { domain: "history" })
        ));
        assert_eq!(history.as_slice(), raw.as_slice());
        assert_eq!(history.numeric.events, numeric);
        assert_eq!(history.numeric.revision, revision);
    }

    #[test]
    fn typed_domains_and_all_event_types_use_one_store_allocator() {
        let store = Store::<TestEvent>::new().unwrap();
        #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
        struct OtherEvent(u8);
        impl Event for OtherEvent {
            type Component = Component4<u8, u8, u8, u8>;
            type Arity = N4;
            fn component(self, index: usize) -> Self::Component {
                match index {
                    0 => Component4::C0(self.0),
                    1 => Component4::C1(self.0),
                    2 => Component4::C2(self.0),
                    _ => Component4::C3(self.0),
                }
            }
            fn coordinate(component: Self::Component) -> usize {
                match component {
                    Component4::C0(_) => 0,
                    Component4::C1(_) => 1,
                    Component4::C2(_) => 2,
                    Component4::C3(_) => 3,
                }
            }
        }
        let other = Store::<OtherEvent>::new().unwrap();
        assert_ne!(store.id(), other.id());
        let first = TestEvent(Key {
            identity: 7,
            payload: 1,
        });
        let equivalent = TestEvent(Key {
            identity: 7,
            payload: 2,
        });
        let encoded = store.encode_event(&first).unwrap();
        assert_eq!(encoded, store.encode_event(&equivalent).unwrap());
        let other_encoded = other.encode_event(&OtherEvent(7)).unwrap();
        assert_eq!(encoded.arity(), 3);
        assert_eq!(other_encoded.arity(), 4);
        assert!(!Arc::ptr_eq(store.numeric_store(), other.numeric_store()));
        for index in 0..encoded.arity() {
            assert!(encoded.component(index) < other_encoded.component(index));
        }
        {
            let mut books = store.books.inner.lock();
            let mut encoder = BorrowedEncoder {
                books: &mut books.components,
                numeric_store: &store.numeric_store,
                #[cfg(verus_keep_ghost)]
                calls: Ghost(0nat),
            };
            let value = Key {
                identity: 8,
                payload: 0,
            };
            assert!(
                encoder
                    .encode(Component(0), &Component3::C0(value))
                    .unwrap()
                    > encoded.component(0)
            );
            assert!(
                encoder
                    .encode(Component(1), &Component3::C1(value))
                    .unwrap()
                    > encoded.component(1)
            );
            assert!(
                encoder
                    .encode(Component(2), &Component3::C2(value))
                    .unwrap()
                    > encoded.component(2)
            );
            assert!(matches!(
                encoder.encode(Component(2), &Component3::C0(value)),
                Err(HistoryError::InvalidPolicy {
                    message: "constant belongs to another component",
                    ..
                })
            ));
        }
    }

    #[test]
    fn typed_numeric_events_never_name_byte_store_identities() {
        use junco_core::limits::Unmetered;
        use junco_core::observation::ObservationWorld;
        let byte = HistoryStore::new(3);
        let fresh = |bytes: &[u8]| {
            byte.intern(Component(0), bytes, &mut Unmetered, &mut ObservationWorld)
                .unwrap()
        };
        let before = fresh(b"typed-vs-byte/before\xff");
        let action = byte
            .intern(
                Component(1),
                b"typed-vs-byte/edit\xfe",
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let resource = byte
            .intern(
                Component(2),
                b"typed-vs-byte/doc\x80",
                &mut Unmetered,
                &mut ObservationWorld,
            )
            .unwrap();
        let typed = alloc::sync::Arc::new(Store::<TestEvent>::new().unwrap());
        assert!(alloc::sync::Arc::ptr_eq(typed.numeric_store(), &byte));
        let history = crate::history::History::from_events(
            typed,
            [TestEvent(Key {
                identity: 7,
                payload: 1,
            })],
        )
        .unwrap();
        let exported = history.numeric().as_slice()[0];
        let after = fresh(b"typed-vs-byte/after\xff");
        // Fresh per-test names: the shared counter orders these three issuances.
        assert!(before < exported.component(0));
        assert!(exported.component(0) < after);
        assert_ne!(exported.component(1), action);
        assert_ne!(exported.component(2), resource);
        let target = byte
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let valid = NumericEvent::from_encoded(&[before, action, resource]);
        byte.append(&target, &[valid], &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        for index in 0..3 {
            let mut slots = [before, action, resource];
            slots[index] = exported.component(index);
            let invalid = NumericEvent::from_encoded(&slots);
            assert!(matches!(
                byte.append(
                    &target,
                    &[valid, invalid],
                    &mut Unmetered,
                    &mut ObservationWorld
                ),
                Err(HistoryError::UnknownId { .. })
            ));
            let record = byte.history_record(&target).unwrap();
            let record = record.read();
            assert_eq!(record.as_slice(), &[valid]);
            assert_eq!(record.revision(), 0);
        }
    }

    #[test]
    // The test proves non-Send components work; `History` still takes its store by `Arc`.
    #[allow(clippy::arc_with_non_send_sync)]
    fn borrowed_non_send_components_stay_scoped() {
        use core::cell::Cell;
        #[derive(Copy, Clone, Debug)]
        struct Borrowed<'a> {
            id: u8,
            cell: &'a Cell<u8>,
        }
        impl PartialEq for Borrowed<'_> {
            fn eq(&self, other: &Self) -> bool {
                self.id == other.id
            }
        }
        impl Eq for Borrowed<'_> {}
        impl Hash for Borrowed<'_> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.id.hash(state);
            }
        }
        impl history_syntax::KeyHash for Borrowed<'_> {
            fn key_hash(&self) -> u64 {
                history_syntax::key_hash::hash_via_std(self)
            }
        }
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        struct BorrowedEvent<'a>(Borrowed<'a>);
        impl<'a> Event for BorrowedEvent<'a> {
            type Component = Component3<Borrowed<'a>, u8, u8>;
            type Arity = N3;
            fn component(self, index: usize) -> Self::Component {
                match index {
                    0 => Component3::C0(self.0),
                    1 => Component3::C1(1),
                    _ => Component3::C2(2),
                }
            }
            fn coordinate(component: Self::Component) -> usize {
                match component {
                    Component3::C0(_) => 0,
                    Component3::C1(_) => 1,
                    Component3::C2(_) => 2,
                }
            }
        }
        let cell = Cell::new(3);
        let event = BorrowedEvent(Borrowed { id: 9, cell: &cell });
        let store = alloc::sync::Arc::new(Store::new().unwrap());
        let mut history = crate::history::History::from_events(store, [event]).unwrap();
        history.push(event).unwrap();
        cell.set(4);
        assert_eq!(history.len(), 2);
        assert!(history.iter().all(|event| event.0.cell.get() == 4));
        let numeric = history.numeric().as_slice();
        assert_eq!(numeric[0], numeric[1]);
    }

    #[test]
    fn failed_map_reservation_keeps_existing_associations() {
        let mut book = Codebook::new();
        let first = Key {
            identity: 7,
            payload: 1,
        };
        let other = Key {
            identity: 8,
            payload: 2,
        };
        let numeric = HistoryStore::new(3);
        let id = book
            .intern(&first, 2, "component", &numeric, Ghost::assume_new())
            .unwrap();
        let _failure = junco_core::observation::fail_reservations_after(0);
        assert!(matches!(
            book.intern(&other, 2, "component", &numeric, Ghost::assume_new()),
            Err(HistoryError::AllocationFailed)
        ));
        assert_eq!(book.last, id);
        assert_eq!(
            book.intern(&first, 2, "component", &numeric, Ghost::assume_new())
                .unwrap(),
            id
        );
        assert_eq!(book.values.lookup(&other), None);
    }

    #[cfg(feature = "std")]
    #[test]
    fn component_hash_unwind_releases_the_store_lock() {
        #[derive(Copy, Clone, Debug, Eq, PartialEq)]
        struct PanickingKey(u8);
        impl Hash for PanickingKey {
            fn hash<H: Hasher>(&self, state: &mut H) {
                assert_ne!(self.0, 8, "deliberate component hash failure");
                self.0.hash(state);
            }
        }
        impl history_syntax::KeyHash for PanickingKey {
            fn key_hash(&self) -> u64 {
                history_syntax::key_hash::hash_via_std(self)
            }
        }
        #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
        struct PanicEvent(PanickingKey);
        impl Event for PanicEvent {
            type Component = Component3<PanickingKey, (), ()>;
            type Arity = N3;
            fn component(self, index: usize) -> Self::Component {
                match index {
                    0 => Component3::C0(self.0),
                    1 => Component3::C1(()),
                    _ => Component3::C2(()),
                }
            }
            fn coordinate(component: Self::Component) -> usize {
                match component {
                    Component3::C0(_) => 0,
                    Component3::C1(_) => 1,
                    Component3::C2(_) => 2,
                }
            }
        }
        let store = Store::<PanicEvent>::new().unwrap();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            store.encode_event(&PanicEvent(PanickingKey(8)))
        }));
        assert!(result.is_err());
        assert!(store.books.inner.try_lock().is_some());
        assert!(store.encode_event(&PanicEvent(PanickingKey(7))).is_ok());
    }

    #[test]
    fn every_supported_arity_retains_scoped_shared_authorities() {
        let mut previous = [0; MAX_ARITY];
        macro_rules! check {
            ($arity:ty) => {{
                #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
                struct SizedEvent([u8; MAX_ARITY]);
                impl Event for SizedEvent {
                    type Component = (u8, u8);
                    type Arity = $arity;
                    fn component(self, index: usize) -> Self::Component {
                        let index = index.min(Self::Arity::value() - 1);
                        (index as u8, self.0[index])
                    }
                    fn coordinate(component: Self::Component) -> usize {
                        component.0 as usize
                    }
                }
                let width = <$arity>::value();
                let store = Store::<SizedEvent>::new().unwrap();
                let other = Store::<SizedEvent>::new().unwrap();
                assert!(Arc::ptr_eq(store.numeric_store(), other.numeric_store()));
                assert_eq!(store.numeric_store().arity(), width);
                let event = SizedEvent([17; MAX_ARITY]);
                let encoded = store.encode_event(&event).unwrap();
                let distinct = other.encode_event(&event).unwrap();
                assert_eq!(encoded.arity(), width);
                assert_eq!(encoded, store.encode_event(&event).unwrap());
                for (index, previous) in previous.iter_mut().enumerate().take(width) {
                    assert!(*previous < encoded.component(index));
                    assert!(encoded.component(index) < distinct.component(index));
                    *previous = distinct.component(index);
                }
                let mut books = store.books.inner.lock();
                assert_eq!(books.components.books.len(), width);
                let mut encoder = BorrowedEncoder {
                    books: &mut books.components,
                    numeric_store: store.numeric_store(),
                    #[cfg(verus_keep_ghost)]
                    calls: Ghost(0nat),
                };
                assert_eq!(
                    encoder
                        .encode(Component((width - 1) as u8), &((width - 1) as u8, 17))
                        .unwrap(),
                    encoded.component(width - 1)
                );
                // Even a malformed native coordinate implementation cannot index past the books.
                assert!(matches!(
                    encoder.encode(Component(width as u8), &(width as u8, 17)),
                    Err(HistoryError::InvalidPolicy { .. })
                ));
            }};
        }
        check!(history_syntax::N1);
        check!(history_syntax::N2);
        check!(history_syntax::N3);
        check!(history_syntax::N4);
        check!(history_syntax::N5);
        check!(history_syntax::N6);
        check!(history_syntax::N7);
        check!(history_syntax::N8);
    }

    #[test]
    fn partial_event_allocation_retains_committed_coordinates() {
        let store = Store::<(u8, u8, u8, u8)>::new().unwrap();
        let event = (11, 12, 13, 14);
        {
            let _failure = junco_core::observation::fail_reservations_after(2);
            assert!(matches!(
                store.encode_event(&event),
                Err(HistoryError::AllocationFailed)
            ));
        }
        let first = {
            let books = store.books.inner.lock();
            let first = books.components.books[0]
                .values
                .lookup(&Component4::C0(11))
                .unwrap();
            assert!(
                books.components.books[1]
                    .values
                    .lookup(&Component4::C1(12))
                    .is_some()
            );
            assert!(
                books.components.books[2]
                    .values
                    .lookup(&Component4::C2(13))
                    .is_none()
            );
            assert!(
                books.components.books[3]
                    .values
                    .lookup(&Component4::C3(14))
                    .is_none()
            );
            first
        };
        let encoded = store.encode_event(&event).unwrap();
        assert_eq!(encoded.component(0), first);
        assert_eq!(encoded, store.encode_event(&event).unwrap());
    }
}
