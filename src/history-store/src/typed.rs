//! Store-bound typed identities. Numeric histories never re-project retained events.

use crate::store::Event as NumericEvent;
use core::hash::Hash;
use history_syntax::Event;
#[cfg(verus_keep_ghost)]
use history_syntax::event::specs::EventSpec;
use history_syntax::syntax::Component;
use junco_core::compile::{FlatEncoder, lower_flat, validate_component};
use junco_core::error::HistoryError;
use junco_core::flat::FlatPair;
use junco_core::flatten::ComponentValue;
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
#[cfg(feature = "std")]
use parking_lot::Mutex;
#[cfg(not(feature = "std"))]
use spin::Mutex;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqSpec;

pub(crate) mod map;
use map::NativeMap;

// Ghost<T> signatures still name T after native erasure; this is the exact finite model.
pub type ComponentMaps<E> = vstd::seq::Seq<vstd::seq::Seq<(ComponentValue<E>, u64)>>;
pub type HistoryRegistration =
    vstd::resource::map::GhostPersistentPointsTo<usize, vstd::resource::Loc>;
type RegistryBirth = vstd::resource::map::GhostPointsTo<usize, vstd::resource::Loc>;

// One process allocator across every E, including on targets without AtomicU64.
static LAST_STORE_ID: spin::Mutex<u64> = spin::Mutex::new(0);

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::std_specs::vec::group_vec_axioms};

pub(crate) struct Codebook<K: Copy + Eq + Hash> {
    pub(crate) values: NativeMap<K>,
    pub(crate) last: u64,
}

/// Checked arithmetic for the process store-ID allocator.
fn checked_successor(last: u64, domain: &'static str) -> (result: Result<u64, HistoryError>)
    ensures match result {
        Ok(id) => last < u64::MAX && id == last + 1 && id > 0,
        Err(_) => last == u64::MAX,
    },
{
    match last.checked_add(1) {
        Some(id) => Ok(id),
        None => Err(HistoryError::IdExhausted { domain }),
    }
}

impl<K: Copy + Eq + Hash> Codebook<K> {
    fn new() -> (result: Self)
        ensures book_wf(result), book_entries(result) == Seq::<(K, u64)>::empty(),
    {
        Self { values: NativeMap::new(), last: 0 }
    }

    fn intern(&mut self, value: &K, index: usize, domain: &'static str) -> (result: Result<u64, HistoryError>)
        ensures map::key_obligations::<K>() && book_wf(*old(self)) ==> {
            &&& book_wf(*final(self))
            &&& book_entries(*old(self)).is_prefix_of(book_entries(*final(self)))
            &&& match result {
                Ok(id) => book_encoded(*final(self), *value, id),
                Err(_) => book_entries(*final(self)) == book_entries(*old(self))
                    && final(self).last == old(self).last,
            }
        },
    {
        let ghost before = book_entries(*self);
        let ghost initial_wf = book_wf(*self);
        if let Some(id) = self.values.lookup(value) {
            return Ok(id);
        }
        // Reuse is checked first, so an exhausted domain still accepts established keys.
        let id = crate::store::allocate_after(index, domain, self.last)?;
        self.values.reserve_one()?;
        self.values.insert_fresh(*value, id);
        self.last = id;
        proof {
            if map::key_obligations::<K>() && initial_wf {
                assert(book_entries(*self) == before.push((*value, id)));
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
    pub(crate) principal: Codebook<E::Principal>,
    pub(crate) action: Codebook<E::Action>,
    pub(crate) resource: Codebook<E::Resource>,
}

pub(crate) struct Codebooks<E: Event> {
    pub(crate) components: ComponentBooks<E>,
    pub(crate) next_history: usize,
    #[cfg(verus_keep_ghost)]
    pub(crate) owner: Ghost<u64>,
    #[cfg(verus_keep_ghost)]
    pub(crate) history_resources: Tracked<vstd::resource::map::GhostMapAuth<usize, vstd::resource::Loc>>,
}

impl<E: Event> Codebooks<E> {
    fn new(Ghost(owner): Ghost<u64>) -> (result: (Self, Tracked<RegistryBirth>))
        ensures books_wf(result.0), result.0.owner@ == owner, result.0.next_history == 1,
            books_maps(result.0) == empty_maps::<E>(), registry_wf(result.0),
            (result.0.history_resources@)@ == map![0usize => result.0.history_resources@.id()],
            result.1@.id() == result.0.history_resources@.id(), result.1@.key() == 0,
            result.1@.value() == result.0.history_resources@.id(),
    {
        let tracked (mut authority, empty) = vstd::resource::map::GhostMapAuth::new(
            Map::<usize, vstd::resource::Loc>::empty());
        // Consumed by mutex initialization; this exclusive receipt can never be reissued.
        let tracked birth = authority.insert(0, authority.id());
        let result = Self {
            components: ComponentBooks {
                principal: Codebook::new(), action: Codebook::new(), resource: Codebook::new(),
            },
            next_history: 1,
            #[cfg(verus_keep_ghost)]
            owner: Ghost(owner),
            #[cfg(verus_keep_ghost)]
            history_resources: Tracked(authority),
        };
        proof {
            lemma_books_maps_wf(result);
            assert forall|field: int| 0 <= field < 3 implies
                books_maps(result)[field] =~= empty_maps::<E>()[field] by {}
            assert(books_maps(result) =~= empty_maps::<E>());
        }
        (result, Tracked(birth))
    }

    fn allocate_history_id(&mut self) -> (result: Result<usize, HistoryError>)
        ensures self_same_books(*old(self), *final(self)),
            final(self).history_resources@ == old(self).history_resources@,
            match result {
                Ok(id) => id == old(self).next_history && id < usize::MAX
                    && final(self).next_history == id + 1,
                Err(_) => final(self).next_history == old(self).next_history
                    && old(self).next_history == usize::MAX,
            },
    {
        let id = self.next_history;
        let next = match id.checked_add(1) {
            Some(next) => next,
            None => return Err(HistoryError::IdExhausted { domain: "history" }),
        };
        self.next_history = next;
        Ok(id)
    }

    fn allocate_history_id_for_resource(&mut self, Ghost(location): Ghost<vstd::resource::Loc>,
        Tracked(prior): Tracked<Option<&HistoryRegistration>>)
        -> (result: Result<(usize, Tracked<HistoryRegistration>), HistoryError>)
        requires registry_wf(*old(self)),
            match prior { Some(registration) => registration.id() == old(self).history_resources@.id(), None => true },
        ensures registry_wf(*final(self)), self_same_books(*old(self), *final(self)),
            final(self).history_resources@.id() == old(self).history_resources@.id(),
            (old(self).history_resources@)@.submap_of((final(self).history_resources@)@),
            match result {
                Ok((id, registration)) => 0 < id < usize::MAX && id == old(self).next_history
                    && final(self).next_history == id + 1
                    && (final(self).history_resources@)@ == (old(self).history_resources@)@.insert(id, location)
                    && registration@.id() == old(self).history_resources@.id()
                    && registration@.key() == id && registration@.value() == location
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
        let id = self.allocate_history_id()?;
        proof { assert(!resources.contains_key(id)); }
        let tracked registration = self.history_resources.borrow_mut().insert(id, location).persist();
        proof {
            assert forall|previous: usize| (self.history_resources@)@.contains_key(previous)
                <==> previous < self.next_history by {
                if previous != id { assert(resources.contains_key(previous) <==> previous < frontier); }
            }
        }
        Ok((id, Tracked(registration)))
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
    fn new(books: Codebooks<E>, Tracked(birth): Tracked<RegistryBirth>) -> (result: Self)
        requires native_obligations::<E>() ==> books_wf(books), registry_wf(books),
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
            native_obligations::<E>() ==> snapshot_published::<E>(registry, first)
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

/// Three typed coordinate codebooks and a never-reused history-ID allocator.
/// Share a store with `Arc`; components and events retain their original Rust values.
pub struct Store<E: Event> {
    pub(crate) id: u64,
    pub(crate) books: NativeBooks<E>,
    #[cfg(verus_keep_ghost)]
    pub(crate) history_registry: Ghost<vstd::resource::Loc>,
}

#[verifier::external_body]
fn allocate_store_id() -> (result: Result<u64, HistoryError>)
    ensures result matches Ok(id) ==> id > 0,
{
    let mut last = LAST_STORE_ID.lock();
    let id = checked_successor(*last, "store")?;
    *last = id;
    Ok(id)
}

impl<E: Event> Store<E> {
    /// Create an empty owner. Store-ID exhaustion is reported before wrapping.
    pub fn new() -> (result: Result<Self, HistoryError>)
        ensures result matches Ok(store) ==> store_wf(store),
    {
        let id = allocate_store_id()?;
        let (state, birth) = Codebooks::new(Ghost(id));
        let ghost registry = state.history_resources@.id();
        let books = NativeBooks::new(state, birth);
        Ok(Self { id, books,
            #[cfg(verus_keep_ghost)]
            history_registry: Ghost(registry),
        })
    }

    pub(crate) fn id(&self) -> (result: u64)
        ensures result == store_id(*self),
    {
        self.id
    }

    pub(crate) fn allocate_history_id(&self) -> (result: Result<usize, HistoryError>)
        requires store_wf(*self),
        ensures result matches Ok(id) ==> 0 < id < usize::MAX,
    {
        let (id, _registration) = self.allocate_history_id_for_resource(Ghost(arbitrary()), Tracked(None))?;
        Ok(id)
    }

    /// The checked allocation body publishes an immutable resource-backed receipt.
    pub(crate) fn allocate_history_id_for_resource(&self,
        Ghost(location): Ghost<vstd::resource::Loc>, Tracked(prior): Tracked<Option<&HistoryRegistration>>)
        -> (result: Result<(usize, Tracked<HistoryRegistration>), HistoryError>)
        requires store_wf(*self),
            match prior { Some(registration) => registration.id() == registry_id(self), None => true },
        ensures result matches Ok((id, registration)) ==> 0 < id < usize::MAX
            && registration@.id() == registry_id(self) && registration@.key() == id
            && registration@.value() == location
            && match prior { Some(previous) => previous.key() < id, None => true },
    {
        proof { if native_obligations::<E>() { lemma_empty_maps_wf::<E>(); } }
        let ghost owner = self.id;
        let ghost registry = self.history_registry@;
        self.books.with_books(Ghost(owner), Ghost(empty_maps::<E>()), Ghost(empty_maps::<E>()), Ghost(registry), (),
            |books: &mut Codebooks<E>, _context: ()| -> (result: Result<(usize, Tracked<HistoryRegistration>), HistoryError>)
                requires books_acquired(*old(books), owner, registry, empty_maps::<E>(), empty_maps::<E>()),
                ensures publication_frame(*old(books), *final(books)),
                    result matches Ok((id, registration)) ==> 0 < id < usize::MAX
                        && registration@.id() == registry && registration@.key() == id
                        && registration@.value() == location
                        && match prior { Some(previous) => previous.key() < id, None => true },
            {
                books.allocate_history_id_for_resource(Ghost(location), Tracked(prior))
            })
    }

    pub(crate) fn encode_event(&self, event: &E) -> (result: Result<NumericEvent, HistoryError>)
        requires store_wf(*self),
        ensures native_obligations::<E>() ==> (result matches Ok(numeric) ==>
            exists|maps: ComponentMaps<E>| snapshot_published::<E>(registry_id(self), maps)
                && maps_wf::<E>(maps) && event_encoded::<E>(maps, *event, numeric)),
    {
        proof { if native_obligations::<E>() { lemma_empty_maps_wf::<E>(); } }
        let (result, _) = self.encode_event_with_snapshot(event,
            Ghost(empty_maps::<E>()), Ghost(empty_maps::<E>()));
        result
    }

    /// Extend two previously published finite snapshots under one lock acquisition.
    pub fn encode_event_with_snapshot(&self, event: &E,
        Ghost(first): Ghost<ComponentMaps<E>>, Ghost(second): Ghost<ComponentMaps<E>>)
        -> (result: (Result<NumericEvent, HistoryError>, Ghost<ComponentMaps<E>>))
        requires store_wf(*self),
            native_obligations::<E>() ==> maps_wf::<E>(first)
                && snapshot_published::<E>(registry_id(self), first) && maps_wf::<E>(second)
                && snapshot_published::<E>(registry_id(self), second),
        ensures snapshot_published::<E>(registry_id(self), result.1@),
            native_obligations::<E>() ==> maps_wf::<E>(result.1@)
                && maps_extend::<E>(first, result.1@) && maps_extend::<E>(second, result.1@)
                && (result.0 matches Ok(numeric) ==> event_encoded::<E>(result.1@, *event, numeric)),
    {
        let ghost owner = self.id;
        let ghost registry = self.history_registry@;
        self.books.with_books(Ghost(owner), Ghost(first), Ghost(second), Ghost(registry), (),
            |books: &mut Codebooks<E>, _context: ()| -> (output: (Result<NumericEvent, HistoryError>, Ghost<ComponentMaps<E>>))
                requires books_acquired(*old(books), owner, registry, first, second),
                ensures publication_frame(*old(books), *final(books)),
                    output.1@ == books_maps(*final(books)),
                    native_obligations::<E>() ==> maps_wf::<E>(output.1@)
                        && maps_extend::<E>(first, output.1@) && maps_extend::<E>(second, output.1@)
                        && (output.0 matches Ok(numeric) ==> event_encoded::<E>(output.1@, *event, numeric)),
            {
                let ghost initial = books_maps(*books);
                let result = {
                    let mut encoder = BorrowedEncoder { books: &mut books.components };
                    encoder.encode_event(event)
                };
                let ghost maps = books_maps(*books);
                proof {
                    if native_obligations::<E>() {
                        lemma_books_maps_wf(*books);
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
    pub fn lower_with_snapshot<L: Limits>(&self, source: &FlatPair<ComponentValue<E>>,
        limits: &mut L, world: &mut ObservationWorld, Ghost(prior): Ghost<ComponentMaps<E>>)
        -> (result: (Result<FlatPair<u64>, HistoryError>, Ghost<ComponentMaps<E>>))
        requires store_wf(*self),
            native_obligations::<E>() ==> maps_wf::<E>(prior)
                && snapshot_published::<E>(registry_id(self), prior),
        ensures result.0 matches Ok(numeric) ==> junco_core::flat::verify::structural_wf(numeric),
            snapshot_published::<E>(registry_id(self), result.1@),
            native_obligations::<E>() ==> maps_wf::<E>(result.1@)
                && maps_extend::<E>(prior, result.1@)
                && (result.0 matches Ok(numeric) ==>
                    junco_core::verify::encoding::lowering(*source, numeric, result.1@,
                        junco_core::verify::flatten::component_equality::<E>())
                    && junco_core::verify::encoding::constants_in_domain(*source, domain::<E>())),
    {
        let ghost owner = self.id;
        let ghost registry = self.history_registry@;
        self.books.with_books(Ghost(owner), Ghost(prior), Ghost(prior), Ghost(registry), (limits, world),
            |books: &mut Codebooks<E>, context: (&mut L, &mut ObservationWorld)|
                -> (output: (Result<FlatPair<u64>, HistoryError>, Ghost<ComponentMaps<E>>))
                requires books_acquired(*old(books), owner, registry, prior, prior),
                ensures publication_frame(*old(books), *final(books)),
                    output.1@ == books_maps(*final(books)),
                    output.0 matches Ok(numeric) ==> junco_core::flat::verify::structural_wf(numeric),
                    native_obligations::<E>() ==> maps_wf::<E>(output.1@) && maps_extend::<E>(prior, output.1@)
                        && (output.0 matches Ok(numeric) ==>
                            junco_core::verify::encoding::lowering(*source, numeric, output.1@,
                                junco_core::verify::flatten::component_equality::<E>())
                            && junco_core::verify::encoding::constants_in_domain(*source, domain::<E>())),
            {
                let (limits, world) = context;
                let ghost initial = books_maps(*books);
                proof { if native_obligations::<E>() { lemma_books_maps_wf(*books); } }
                let result = {
                    let mut encoder = BorrowedEncoder { books: &mut books.components };
                    lower_flat(source, &mut encoder, limits, world)
                };
                let ghost maps = books_maps(*books);
                proof {
                    if native_obligations::<E>() {
                        junco_core::verify::encoding::lemma_extends_transitive(prior, initial, maps,
                            junco_core::verify::flatten::component_equality::<E>());
                    }
                }
                (result, Ghost(maps))
            })
    }
}

/// A scoped encoder borrows the three codebooks, never a graph or history record.
pub(crate) struct BorrowedEncoder<'a, E: Event> {
    pub(crate) books: &'a mut ComponentBooks<E>,
}

impl<'a, E: Event> FlatEncoder<ComponentValue<E>> for BorrowedEncoder<'a, E> {
    open spec fn equality() -> junco_core::verify::encoding::Equality<ComponentValue<E>> {
        junco_core::verify::flatten::component_equality::<E>()
    }
    open spec fn domain() -> junco_core::verify::encoding::Domain<ComponentValue<E>> { domain::<E>() }
    open(crate) spec fn maps(&self) -> ComponentMaps<E> { component_maps(*self.books) }
    open(crate) spec fn obeys_encoding_spec(&self) -> bool {
        native_obligations::<E>() && components_wf(*self.books)
    }

    #[verifier::prophetic]
    open(crate) spec fn restoration(&self) -> (ComponentMaps<E>, bool) {
        let restored = mut_ref_future(self.books);
        (component_maps(restored), components_wf(restored))
    }

    fn encode(&mut self, field: Component, value: &ComponentValue<E>)
        -> (result: Result<u64, HistoryError>)
    {
        let ghost initial = component_maps(*self.books);
        let ghost initial_wf = components_wf(*self.books);
        let ghost initial_books = *self.books;
        validate_component(field, value)?;
        let result = match value {
            ComponentValue::Principal(value) => self.books.principal.intern(value, 0, "principal"),
            ComponentValue::Action(value) => self.books.action.intern(value, 1, "action"),
            ComponentValue::Resource(value) => self.books.resource.intern(value, 2, "resource"),
        };
        proof {
            if native_obligations::<E>() && initial_wf {
                lemma_component_maps_wf(*self.books);
                lemma_coordinate_prefix(initial_books, *self.books);
                lemma_maps_prefix_extension::<E>(initial, component_maps(*self.books));
                if let Ok(id) = result {
                    match *value {
                        ComponentValue::Principal(key) => {
                            let entries = book_entries(self.books.principal);
                            assert(book_encoded(self.books.principal, key, id));
                            let i = choose|i: int| 0 <= i < entries.len() && entries[i].1 == id
                                && key.eq_spec(&entries[i].0);
                            assert(component_maps(*self.books)[0][i]
                                == (ComponentValue::Principal(entries[i].0), id));
                            assert(field == Component::Principal);
                            assert(Self::equality()(field, *value, component_maps(*self.books)[0][i].0));
                            assert(junco_core::verify::encoding::encoded(component_maps(*self.books),
                                Self::equality(), field, *value, id)) by {
                                let maps = component_maps(*self.books);
                                let f = junco_core::flat::verify::field_index(field);
                                assert(maps.len() == 3 && id > 0);
                                assert(0 <= i < maps[f].len());
                                assert(maps[f][i].1 == id && Self::equality()(field, *value, maps[f][i].0));
                            }
                        },
                        ComponentValue::Action(key) => {
                            let entries = book_entries(self.books.action);
                            assert(book_encoded(self.books.action, key, id));
                            let i = choose|i: int| 0 <= i < entries.len() && entries[i].1 == id
                                && key.eq_spec(&entries[i].0);
                            assert(component_maps(*self.books)[1][i]
                                == (ComponentValue::Action(entries[i].0), id));
                            assert(field == Component::Action);
                            assert(Self::equality()(field, *value, component_maps(*self.books)[1][i].0));
                            assert(junco_core::verify::encoding::encoded(component_maps(*self.books),
                                Self::equality(), field, *value, id)) by {
                                let maps = component_maps(*self.books);
                                let f = junco_core::flat::verify::field_index(field);
                                assert(maps.len() == 3 && id > 0);
                                assert(0 <= i < maps[f].len());
                                assert(maps[f][i].1 == id && Self::equality()(field, *value, maps[f][i].0));
                            }
                        },
                        ComponentValue::Resource(key) => {
                            let entries = book_entries(self.books.resource);
                            assert(book_encoded(self.books.resource, key, id));
                            let i = choose|i: int| 0 <= i < entries.len() && entries[i].1 == id
                                && key.eq_spec(&entries[i].0);
                            assert(component_maps(*self.books)[2][i]
                                == (ComponentValue::Resource(entries[i].0), id));
                            assert(field == Component::Resource);
                            assert(Self::equality()(field, *value, component_maps(*self.books)[2][i].0));
                            assert(junco_core::verify::encoding::encoded(component_maps(*self.books),
                                Self::equality(), field, *value, id)) by {
                                let maps = component_maps(*self.books);
                                let f = junco_core::flat::verify::field_index(field);
                                assert(maps.len() == 3 && id > 0);
                                assert(0 <= i < maps[f].len());
                                assert(maps[f][i].1 == id && Self::equality()(field, *value, maps[f][i].0));
                            }
                        },
                    }
                    assert(domain::<E>()(field, *value));
                    assert(junco_core::verify::encoding::encoded(component_maps(*self.books),
                        Self::equality(), field, *value, id));
                }
            }
        }
        result
    }
}

impl<'a, E: Event> BorrowedEncoder<'a, E> {
    fn encode_event(&mut self, event: &E) -> (result: Result<NumericEvent, HistoryError>)
        requires native_obligations::<E>() ==> components_wf(*old(self).books),
        ensures native_obligations::<E>() ==> components_wf(*final(self).books)
            && maps_extend::<E>(component_maps(*old(self).books), component_maps(*final(self).books))
            && (result matches Ok(numeric) ==> event_encoded::<E>(component_maps(*final(self).books), *event, numeric)),
            final(self).restoration() == old(self).restoration(),
    {
        let principal = event.principal();
        let action = event.action();
        let resource = event.resource();
        let ghost before = component_maps(*self.books);
        let principal = self.encode(Component::Principal, &ComponentValue::Principal(principal))?;
        let ghost after_principal = component_maps(*self.books);
        let action = self.encode(Component::Action, &ComponentValue::Action(action))?;
        let ghost after_action = component_maps(*self.books);
        let resource = self.encode(Component::Resource, &ComponentValue::Resource(resource))?;
        proof {
            if native_obligations::<E>() {
                junco_core::verify::encoding::lemma_extends_transitive(before, after_principal,
                    after_action, Self::equality());
                junco_core::verify::encoding::lemma_extends_transitive(before, after_action,
                    component_maps(*self.books), Self::equality());
            }
        }
        Ok(NumericEvent::from_encoded(principal, action, resource))
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
    verus! {

    pub type ComponentMaps<E> = super::ComponentMaps<E>;
    pub type HistoryRegistration = super::HistoryRegistration;

    pub open spec fn domain<E: Event>() -> encoding::Domain<ComponentValue<E>> {
        |field: Component, value: ComponentValue<E>| match (field, value) {
            (Component::Principal, ComponentValue::Principal(_))
            | (Component::Action, ComponentValue::Action(_))
            | (Component::Resource, ComponentValue::Resource(_)) => true,
            _ => false,
        }
    }

    pub open(super) spec fn native_obligations<E: Event>() -> bool {
        E::obeys_projection_spec() && map::key_obligations::<E::Principal>()
            && map::key_obligations::<E::Action>() && map::key_obligations::<E::Resource>()
    }

    pub open spec fn empty_maps<E: Event>() -> ComponentMaps<E> {
        seq![Seq::<(ComponentValue<E>, u64)>::empty(),
            Seq::<(ComponentValue<E>, u64)>::empty(), Seq::<(ComponentValue<E>, u64)>::empty()]
    }

    pub open spec fn maps_wf<E: Event>(maps: ComponentMaps<E>) -> bool {
        encoding::maps_wf(maps, component_equality::<E>(), domain::<E>())
    }
    pub open spec fn maps_extend<E: Event>(before: ComponentMaps<E>, after: ComponentMaps<E>) -> bool {
        encoding::extends(before, after, component_equality::<E>())
    }

    /// Persistent provenance scoped to the unique, linearly owned mutex registry resource.
    pub uninterp spec fn snapshot_published<E: Event>(registry: vstd::resource::Loc, maps: ComponentMaps<E>) -> bool;

    pub open(super) spec fn store_id<E: Event>(store: Store<E>) -> u64 { store.id }
    pub open(super) spec fn store_wf<E: Event>(store: Store<E>) -> bool {
        store.id > 0 && mutex_valid(store.books, store.id, store.history_registry@)
            && snapshot_published::<E>(store.history_registry@, empty_maps::<E>())
    }

    pub open(super) spec fn registry_id<E: Event>(store: &Store<E>) -> vstd::resource::Loc {
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

    pub open spec fn projection<E: Event>(raw: E)
        -> junco_core::verify::dsl::EventView<E::Principal, E::Action, E::Resource>
    {
        junco_core::verify::dsl::EventView { principal: raw.principal_spec(),
            action: raw.action_spec(), resource: raw.resource_spec() }
    }

    pub open spec fn numeric_values(numeric: NumericEvent) -> Seq<u64> {
        seq![numeric.principal@ as u64, numeric.action@ as u64, numeric.resource@ as u64]
    }

    pub open spec fn event_encoded<E: Event>(maps: ComponentMaps<E>, raw: E, numeric: NumericEvent) -> bool {
        encoding::event_encoded(maps, component_equality::<E>(), domain::<E>(),
            junco_core::verify::flatten::event_values::<E>(projection(raw)), numeric_values(numeric))
            && junco_core::verify::encoding::event_representation(numeric_values(numeric), numeric@)
    }

    pub(crate) open(crate) spec fn book_entries<K: Copy + Eq + Hash>(book: Codebook<K>) -> Seq<(K, u64)> {
        map::representatives(book.values)
    }
    pub(crate) open(crate) spec fn book_wf<K: Copy + Eq + Hash>(book: Codebook<K>) -> bool {
        (forall|i: int| #![trigger book_entries(book)[i]]
            0 <= i < book_entries(book).len() ==> 0 < book_entries(book)[i].1 <= book.last)
            && (map::key_obligations::<K>() ==> forall|i: int, j: int|
                0 <= i < book_entries(book).len() && 0 <= j < book_entries(book).len()
                ==> (book_entries(book)[i].0.eq_spec(&book_entries(book)[j].0)
                    == (book_entries(book)[i].1 == book_entries(book)[j].1)))
    }
    pub(crate) open(crate) spec fn book_encoded<K: Copy + Eq + Hash>(book: Codebook<K>, value: K, id: u64) -> bool {
        id > 0 && exists|i: int| 0 <= i < book_entries(book).len()
            && book_entries(book)[i].1 == id && value.eq_spec(&book_entries(book)[i].0)
    }
    pub(crate) open(crate) spec fn components_wf<E: Event>(books: ComponentBooks<E>) -> bool {
        book_wf(books.principal) && book_wf(books.action) && book_wf(books.resource)
    }
    pub(crate) open(crate) spec fn component_maps<E: Event>(books: ComponentBooks<E>) -> ComponentMaps<E> {
        seq![book_entries(books.principal).map(|i: int, pair: (E::Principal, u64)|
                (ComponentValue::Principal(pair.0), pair.1)),
            book_entries(books.action).map(|i: int, pair: (E::Action, u64)|
                (ComponentValue::Action(pair.0), pair.1)),
            book_entries(books.resource).map(|i: int, pair: (E::Resource, u64)|
                (ComponentValue::Resource(pair.0), pair.1))]
    }
    pub(crate) open(crate) spec fn books_wf<E: Event>(books: Codebooks<E>) -> bool {
        components_wf(books.components)
    }
    pub(crate) open(crate) spec fn books_maps<E: Event>(books: Codebooks<E>) -> ComponentMaps<E> {
        component_maps(books.components)
    }
    pub(crate) open(crate) spec fn self_same_books<E: Event>(before: Codebooks<E>, after: Codebooks<E>) -> bool {
        before.components == after.components && before.owner@ == after.owner@
    }
    pub(crate) open(crate) spec fn registry_wf<E: Event>(books: Codebooks<E>) -> bool {
        books.next_history > 0 && (books.history_resources@)@[0] == books.history_resources@.id()
            && forall|id: usize| (books.history_resources@)@.contains_key(id) <==> id < books.next_history
    }
    pub(crate) uninterp spec fn mutex_valid<E: Event>(mutex: NativeBooks<E>, owner: u64, registry: vstd::resource::Loc) -> bool;

    pub(crate) open(crate) spec fn books_acquired<E: Event>(books: Codebooks<E>, owner: u64,
        registry: vstd::resource::Loc, first: ComponentMaps<E>, second: ComponentMaps<E>) -> bool {
        books.owner@ == owner && registry_wf(books) && books.history_resources@.id() == registry
            && (native_obligations::<E>() ==> books_wf(books)
                && maps_extend::<E>(first, books_maps(books)) && maps_extend::<E>(second, books_maps(books)))
    }

    pub(crate) open(crate) spec fn publication_frame<E: Event>(before: Codebooks<E>, after: Codebooks<E>) -> bool {
        before.owner@ == after.owner@ && registry_wf(after)
            && before.history_resources@.id() == after.history_resources@.id()
            && (before.history_resources@)@.submap_of((after.history_resources@)@)
            && (native_obligations::<E>() ==> books_wf(after) && maps_extend::<E>(books_maps(before), books_maps(after)))
    }

    pub proof fn lemma_empty_maps_wf<E: Event>()
        requires native_obligations::<E>(),
        ensures maps_wf::<E>(empty_maps::<E>()),
    {}

    pub(super) proof fn lemma_component_maps_wf<E: Event>(books: ComponentBooks<E>)
        requires components_wf(books),
        ensures native_obligations::<E>() ==> maps_wf::<E>(component_maps(books)),
    {
        if native_obligations::<E>() {
            assert(encoding::equality_laws(component_equality::<E>(), domain::<E>()));
            assert forall|f: int, i: int| 0 <= f < 3 && 0 <= i < component_maps(books)[f].len()
                implies domain::<E>()(encoding::field_at(f), component_maps(books)[f][i].0)
                    && component_maps(books)[f][i].1 > 0 by {
                if f == 0 {} else if f == 1 {} else {}
            }
            assert forall|f: int, i: int, j: int| 0 <= f < 3
                && 0 <= i < component_maps(books)[f].len() && 0 <= j < component_maps(books)[f].len()
                implies (component_equality::<E>()(encoding::field_at(f), component_maps(books)[f][i].0,
                    component_maps(books)[f][j].0) == (component_maps(books)[f][i].1 == component_maps(books)[f][j].1)) by {
                if f == 0 {} else if f == 1 {} else {}
            }
        }
    }

    pub(super) proof fn lemma_books_maps_wf<E: Event>(books: Codebooks<E>)
        requires books_wf(books),
        ensures native_obligations::<E>() ==> maps_wf::<E>(books_maps(books)),
    {
        lemma_component_maps_wf(books.components);
    }

    pub(super) proof fn lemma_coordinate_prefix<E: Event>(before: ComponentBooks<E>, after: ComponentBooks<E>)
        requires book_entries(before.principal).is_prefix_of(book_entries(after.principal)),
            book_entries(before.action).is_prefix_of(book_entries(after.action)),
            book_entries(before.resource).is_prefix_of(book_entries(after.resource)),
        ensures forall|f: int| 0 <= f < 3 ==> component_maps(before)[f].is_prefix_of(component_maps(after)[f]),
    {
        assert forall|f: int| 0 <= f < 3 implies
            component_maps(before)[f].is_prefix_of(component_maps(after)[f]) by {
            let a = component_maps(before)[f];
            let b = component_maps(after)[f];
            if f == 0 {} else if f == 1 {} else {}
            assert(a.len() <= b.len());
            assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
                if f == 0 {} else if f == 1 {} else {}
            }
            assert(a =~= b.subrange(0, a.len() as int));
        }
    }

    pub(super) proof fn lemma_maps_prefix_extension<E: Event>(before: ComponentMaps<E>, after: ComponentMaps<E>)
        requires before.len() == 3, after.len() == 3,
            forall|f: int| 0 <= f < 3 ==> before[f].is_prefix_of(after[f]),
        ensures maps_extend::<E>(before, after),
    {
        assert forall|field: Component, value: ComponentValue<E>, id: u64|
            encoding::encoded(before, component_equality::<E>(), field, value, id)
            implies encoding::encoded(after, component_equality::<E>(), field, value, id) by {
            let f = junco_core::flat::verify::field_index(field);
            let i = choose|i: int| 0 <= i < before[f].len() && before[f][i].1 == id
                && component_equality::<E>()(field, value, before[f][i].0);
            assert(after[f][i] == before[f][i]);
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
    #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
    struct TestEvent(Key);
    impl Event for TestEvent {
        type Principal = Key;
        type Action = Key;
        type Resource = Key;
        fn principal(self) -> Key {
            self.0
        }
        fn action(self) -> Key {
            self.0
        }
        fn resource(self) -> Key {
            self.0
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
        let id = book.intern(&first, 0, "principal").unwrap();
        assert_eq!(book.intern(&equivalent, 0, "principal").unwrap(), id);
        // No shared-counter ID exceeds this book's newest one, so only reuse can succeed.
        book.last = u64::MAX;
        assert!(matches!(
            book.intern(&other, 0, "principal"),
            Err(HistoryError::Invariant { .. })
        ));
        assert_eq!(book.last, u64::MAX);
        assert_eq!(book.intern(&equivalent, 0, "principal").unwrap(), id);
        assert_eq!(book.values.lookup(&other), None);
        let mut book = Codebook::new();
        let first_action = book.intern(&first, 1, "action").unwrap();
        assert!(book.intern(&other, 1, "action").unwrap() > first_action);
        assert_eq!(book.intern(&equivalent, 1, "action").unwrap(), first_action);
    }

    #[test]
    fn history_exhaustion_is_checked_and_does_not_change_codebooks() {
        let (mut books, _birth) = Codebooks::<TestEvent>::new(Ghost::assume_new());
        books.next_history = usize::MAX - 1;
        assert_eq!(books.allocate_history_id().unwrap(), usize::MAX - 1);
        assert!(matches!(
            books.allocate_history_id(),
            Err(HistoryError::IdExhausted { domain: "history" })
        ));
        assert_eq!(books.next_history, usize::MAX);
        assert_eq!(books.components.principal.last, 0);
        assert_eq!(books.components.action.last, 0);
        assert_eq!(books.components.resource.last, 0);

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
            type Principal = u8;
            type Action = u8;
            type Resource = u8;
            fn principal(self) -> u8 {
                self.0
            }
            fn action(self) -> u8 {
                self.0
            }
            fn resource(self) -> u8 {
                self.0
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
        {
            let mut books = store.books.inner.lock();
            let mut encoder = BorrowedEncoder {
                books: &mut books.components,
            };
            let value = Key {
                identity: 8,
                payload: 0,
            };
            assert!(
                encoder
                    .encode(Component::Principal, &ComponentValue::Principal(value))
                    .unwrap()
                    > encoded.principal.get()
            );
            assert!(
                encoder
                    .encode(Component::Action, &ComponentValue::Action(value))
                    .unwrap()
                    > encoded.action.get()
            );
            assert!(
                encoder
                    .encode(Component::Resource, &ComponentValue::Resource(value))
                    .unwrap()
                    > encoded.resource.get()
            );
            assert!(matches!(
                encoder.encode(Component::Resource, &ComponentValue::Principal(value)),
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
        let byte = alloc::sync::Arc::new(crate::store::HistoryStore::new());
        let before = byte
            .intern_principal("alice", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        byte.intern_action("edit", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        byte.intern_resource("doc", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        let typed = alloc::sync::Arc::new(Store::<TestEvent>::new().unwrap());
        let history = crate::history::History::from_events(
            typed,
            [TestEvent(Key {
                identity: 7,
                payload: 1,
            })],
        )
        .unwrap();
        let exported = history.numeric().as_slice()[0];
        let after = byte
            .intern_principal("bob", &mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert!(before.get() < exported.principal.get());
        assert!(exported.principal.get() < after.get());
        let target = byte
            .new_history(&mut Unmetered, &mut ObservationWorld)
            .unwrap();
        assert!(matches!(
            byte.append(&target, &[exported], &mut Unmetered, &mut ObservationWorld),
            Err(HistoryError::UnknownId { .. })
        ));
        assert_eq!(byte.history_record(&target).unwrap().read().len(), 0);
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
        let id = book.intern(&first, 2, "resource").unwrap();
        let _failure = junco_core::observation::fail_reservations_after(0);
        assert!(matches!(
            book.intern(&other, 2, "resource"),
            Err(HistoryError::AllocationFailed)
        ));
        assert_eq!(book.last, id);
        assert_eq!(book.intern(&first, 2, "resource").unwrap(), id);
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
        #[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
        struct PanicEvent(PanickingKey);
        impl Event for PanicEvent {
            type Principal = PanickingKey;
            type Action = ();
            type Resource = ();
            fn principal(self) -> PanickingKey {
                self.0
            }
            fn action(self) {}
            fn resource(self) {}
        }
        let store = Store::<PanicEvent>::new().unwrap();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            store.encode_event(&PanicEvent(PanickingKey(8)))
        }));
        assert!(result.is_err());
        assert!(store.books.inner.try_lock().is_some());
        assert!(store.encode_event(&PanicEvent(PanickingKey(7))).is_ok());
    }
}
