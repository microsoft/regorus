// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(verus_keep_ghost)]
use super::kernel::verify as model;
#[cfg(verus_keep_ghost)]
use super::normalize::verify as norm;
#[cfg(verus_keep_ghost)]
use super::symbolic;
use super::{
    error::HistoryError,
    graph::{
        allocation, sequence_bytes, ArenaStorage, CanonicalStore, ObservationWorld, RuntimeKernel,
    },
    kernel::*,
    WorkVec,
};
#[cfg(verus_keep_ghost)]
use crate::verify::history_assumptions::*;
#[cfg(verus_keep_ghost)]
use crate::verify::history_specs as language;
#[cfg(verus_keep_ghost)]
use crate::verify::history_specs::{EventView, Subst};
use crate::{languages::history_table::Event, utils::limits::ExecutionTimer};
use alloc::{collections::BTreeSet, vec::Vec};
use core::num::NonZeroUsize;
use lru::LruCache;
use smallvec::SmallVec;
#[cfg(verus_keep_ghost)]
use verify::*;
use vstd::prelude::*;

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct EventClass {
    pub(crate) transition: TransitionId,
    pub(crate) words: SmallVec<[u64; 2]>,
}

/// Self-loop certificate for one residual: when any atom of `transition` whose bit is set in
/// `mask` is false on an event, the event's successor is the residual itself. `mask == 0`
/// means "computed, nothing usable" (constant, wide, or budget-limited transition).
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Guard {
    pub(crate) transition: TransitionId,
    pub(crate) mask: u64,
}

/// Atoms per transition the guard enumeration accepts: 2^8 = 256 `TransitionId::interpret` runs,
/// one truth word, the same ceiling `precompile` uses.
// ponytail: 8 atoms = 256 interpretations per residual; raise if wider transitions show up hot.
#[verus_verify]
const GUARD_MAX_ATOMS: usize = 8;

#[cfg(test)]
#[derive(Debug, Default)]
pub(crate) struct WorkCounters {
    pub(crate) events: usize,
    pub(crate) derivative_misses: usize,
    pub(crate) event_classes: usize,
    pub(crate) successor_hits: usize,
    pub(crate) successor_misses: usize,
    pub(crate) guard_hits: usize,
    pub(crate) skip_guards: bool,
    pub(crate) fail_answer_checkpoint: bool,
}

/// Successor-cache capacity, also `precompile`'s class budget, so nothing it builds is evicted.
/// `u64` because only `u64::checked_shl` is specified.
#[verus_verify]
const SUCCESSOR_CAPACITY: u64 = 256;

/// Residual states `precompile` explores before leaving the rest to the lazy path.
#[cfg(feature = "cache")]
#[verus_verify]
const PRECOMPILE_STATES: usize = 64;

/// Hash-consed graph and graph-local derivative, primitive, guard and successor caches.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub(crate) struct CompiledPair {
    pub(crate) store: CanonicalStore<ArenaStorage>,
    pub(crate) root: RegexId,
    pub(crate) derivatives: Vec<Option<TransitionId>>,
    pub(crate) atoms: Vec<Option<AtomSet>>,
    pub(crate) guards: Vec<Option<Guard>>,
    pub(crate) successors: Option<LruCache<EventClass, RegexId>>,
    #[cfg(test)]
    pub(crate) work: WorkCounters,
}
#[verus_verify]
impl CompiledPair {
    // Concrete LRU leaves expose semantic keys and membership, not policy semantics.
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures result matches Some(cache) ==> successor_cache_view(cache) == Map::<ClassKey, RegexId>::empty())]
    fn successor_cache() -> Option<LruCache<EventClass, RegexId>> {
        usize::try_from(SUCCESSOR_CAPACITY)
            .ok()
            .and_then(NonZeroUsize::new)
            .map(LruCache::new)
    }

    #[verus_verify(external_body)]
    #[verus_spec(result =>
        ensures successor_entries(*final(cache)) == successor_entries(*old(cache)),
            result == if successor_entries(*old(cache)).contains_key(class_key(*key)) {
                Some(successor_entries(*old(cache))[class_key(*key)])
            } else { None },
    )]
    fn successor_get(
        cache: &mut Option<LruCache<EventClass, RegexId>>,
        key: &EventClass,
    ) -> Option<RegexId> {
        cache.as_mut().and_then(|cache| cache.get(key)).copied()
    }

    #[verus_verify(external_body)]
    #[verus_spec(
        ensures *old(cache) is Some ==> *final(cache) is Some
            && successor_entries(*final(cache)).contains_key(class_key(key))
            && successor_entries(*final(cache))[class_key(key)] == value,
            *old(cache) is None ==> *final(cache) is None,
            forall|other: ClassKey| #[trigger] successor_entries(*final(cache)).contains_key(other) ==> other == class_key(key)
                || (successor_entries(*old(cache)).contains_key(other)
                    && successor_entries(*final(cache))[other] == successor_entries(*old(cache))[other]),
    )]
    fn successor_put(
        cache: &mut Option<LruCache<EventClass, RegexId>>,
        key: EventClass,
        value: RegexId,
    ) {
        if let Some(cache) = cache.as_mut() {
            cache.put(key, value);
        }
    }

    // Borrow only the atom slice so callers can mutate the disjoint graph store.
    #[verus_verify]
    #[verus_spec(result =>
        ensures result matches Ok(set) ==> transition@ < atoms@.len() && atoms@[transition@ as int] == Some(*set),
    )]
    fn cached_atoms(atoms: &[Option<AtomSet>], transition: TransitionId) -> KernelResult<&AtomSet> {
        match atoms.get(transition.index()?) {
            Some(Some(set)) => Ok(set),
            _ => Err(HistoryError::invariant("missing transition atoms")),
        }
    }

    #[verus_verify]
    #[verus_spec(result =>
        requires model::graph_wf(store.graph()), store.valid_store(), root@ < store.graph().regexes.len(),
        ensures pair_wf(result), result.store.graph() == store.graph(), result.root == root,
    )]
    pub(crate) const fn new(store: CanonicalStore<ArenaStorage>, root: RegexId) -> Self {
        let pair = Self {
            store,
            root,
            derivatives: Vec::new(),
            atoms: Vec::new(),
            guards: Vec::new(),
            successors: None,
            #[cfg(test)]
            work: WorkCounters {
                events: 0,
                derivative_misses: 0,
                event_classes: 0,
                successor_hits: 0,
                successor_misses: 0,
                guard_hits: 0,
                skip_guards: false,
                fail_answer_checkpoint: false,
            },
        };
        proof! {
            assert(pair.store.graph() == store.graph());
            assert(pair.store.valid_store());
            assert(model::graph_wf(pair.store.graph()));
            assert(pair.root@ < pair.store.graph().regexes.len());
            assert(symbolic::verify::derivative_cache_wf(pair.store.graph(), pair.derivatives@));
            assert(atom_cache_wf(pair.store.graph(), pair.atoms@));
            assert(guard_cache_wf(pair.store.graph(), pair.atoms@, pair.guards@));
            assert(pair_wf(pair));
        }
        pair
    }
    #[verus_verify]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), residual@ < (*old(self)).store.graph().regexes.len(),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
            (*final(self)).store.graph() == (*old(self)).store.graph(),
            result matches Ok(answer) ==> answer == language::nullable(model::lift_regex((*final(self)).store.graph(), residual@)),
    )]
    pub(crate) fn answer(
        &mut self,
        residual: RegexId,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<bool> {
        let kernel = RuntimeKernel {
            store: &mut self.store,
            timer,
            world,
        };
        let answer = residual.nullable(&kernel)?;
        #[cfg(test)]
        if self.work.fail_answer_checkpoint {
            return Err(HistoryError::Limit(
                crate::utils::limits::LimitError::TimeLimitExceeded {
                    elapsed: core::time::Duration::from_secs(2),
                    limit: core::time::Duration::from_secs(1),
                },
            ));
        }
        kernel.world.checkpoint(kernel.timer)?;
        Ok(answer)
    }
    /// Folds `events` into `residual`: the result denotes `events⁻¹ L(residual)`
    /// under `bindings`. Errors publish no residual.
    #[allow(
        clippy::indexing_slicing,
        reason = "The loop condition and invariant bound the event index."
    )]
    #[verus_verify]
    #[verus_spec(result =>
        requires pair_wf(*old(self)),
            residual@ < (*old(self)).store.graph().regexes.len(),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
            result matches Ok(out) ==> residual_folds(*final(self), bindings@, residual, model::events_view(events@), out),
    )]
    pub(crate) fn fold(
        &mut self,
        residual: RegexId,
        events: &[Event],
        bindings: &Bindings,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<RegexId> {
        proof_decl! { let ghost entry = *self; let ghost from = residual; }
        let mut residual = residual;
        proof! {
            lemma_fold_start(*self, bindings@, from);
            assert(model::events_view(events@).take(0) =~= Seq::<EventView>::empty());
            assert(model::events_view(events@).take(events@.len() as int) =~= model::events_view(events@));
        }
        let mut failure = None;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pair_wf(entry), pair_wf(*self), pair_frame(entry, *self),
                index <= events@.len(),
                residual_folds(*self, bindings@, from, model::events_view(events@).take(index as int), residual),
                model::events_view(events@).take(events@.len() as int) == model::events_view(events@),
            ensures pair_wf(*self), pair_frame(entry, *self),
                failure is Some || residual_folds(*self, bindings@, from, model::events_view(events@), residual),
            decreases events@.len() - index,
        ))]
        while index < events.len() {
            let event = &events[index];
            proof_decl! {
                let ghost before = *self;
                let ghost done = model::events_view(events@).take(index as int);
            }
            proof! {
                model::lemma_graph_wf_elim(entry.store.graph());
                model::lemma_lift_stable_under_extends(entry.store.graph(), before.store.graph());
                assert(model::events_view(events@).take(index as int + 1) =~= done.push(event@));
            }
            loop_try!(world.checkpoint(timer), failure);
            let constants = self.store.constants();
            if residual == constants.all || residual == constants.empty {
                proof! {
                    lemma_fold_absorbing(*self, bindings@, from, done, model::events_view(events@).skip(index as int), residual);
                    assert(done + model::events_view(events@).skip(index as int) =~= model::events_view(events@));
                }
                break;
            }
            #[cfg(test)]
            {
                self.work.events = self.work.events.saturating_add(1);
                if self
                    .derivatives
                    .get(residual.index()?)
                    .copied()
                    .flatten()
                    .is_none()
                {
                    self.work.derivative_misses = self.work.derivative_misses.saturating_add(1);
                }
            }
            let derivative_result = {
                let mut kernel = RuntimeKernel {
                    store: &mut self.store,
                    timer,
                    world,
                };
                residual.derivative(&mut kernel, &mut self.derivatives)
            };
            proof! { lemma_pair_symbolic_frame(before, *self); lemma_fold_frame(before, *self, bindings@, from, done, residual); }
            let transition = loop_try!(derivative_result, failure);
            #[cfg(test)]
            let guards_enabled = !self.work.skip_guards;
            #[cfg(not(test))]
            let guards_enabled = true;
            if guards_enabled {
                proof_decl! { let ghost before_guard = *self; }
                let ensured = self.ensure_guard(residual, transition, timer, world);
                proof! { lemma_fold_frame(before_guard, *self, bindings@, from, done, residual); symbolic::verify::derivative_correct_stable(before_guard.store.graph(), self.store.graph(), residual@, transition); }
                loop_try!(ensured, failure);
                proof_decl! { let ghost before_hit = *self; }
                let hit = self.guard_hit(residual, transition, event, bindings, timer, world);
                proof! { lemma_fold_frame(before_hit, *self, bindings@, from, done, residual); symbolic::verify::derivative_correct_stable(before_hit.store.graph(), self.store.graph(), residual@, transition); }
                if loop_try!(hit, failure) {
                    #[cfg(test)]
                    {
                        self.work.guard_hits = self.work.guard_hits.saturating_add(1);
                    }
                    proof! { lemma_fold_step(*self, bindings@, from, done, residual, transition, *event, residual); }
                    index = index.saturating_add(1);
                    continue;
                }
            }
            proof_decl! { let ghost before_instantiate = *self; }
            let successor_result = self.instantiate(transition, event, bindings, timer, world);
            proof! { lemma_fold_frame(before_instantiate, *self, bindings@, from, done, residual); symbolic::verify::derivative_correct_stable(before_instantiate.store.graph(), self.store.graph(), residual@, transition); }
            let successor = loop_try!(successor_result, failure);
            proof! { lemma_fold_step(*self, bindings@, from, done, residual, transition, *event, successor); }
            residual = successor;
            index = index.saturating_add(1);
        }
        if let Some(error) = failure {
            return Err(error);
        }
        Ok(residual)
    }
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[verus_verify]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), transition@ < old(self).store.graph().transitions.len(),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
            result is Ok ==> has_atoms(*final(self), transition),
    )]
    fn ensure_atoms(
        &mut self,
        transition: TransitionId,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<()> {
        proof_decl! { let ghost entry = *self; }
        let index = transition.index()?;
        if matches!(self.atoms.get(index), Some(Some(_))) {
            return Ok(());
        }
        let atoms = {
            let mut kernel = RuntimeKernel {
                store: &mut self.store,
                timer,
                world,
            };
            AtomSet::from_transition(&mut kernel, transition)
        };
        proof! {
            symbolic::verify::derivative_extends(entry.store.graph(), self.store.graph());
            lemma_pair_symbolic_frame(entry, *self);
        }
        let atoms = atoms?;
        let needed = index
            .checked_add(1)
            .ok_or_else(|| HistoryError::invariant("atom table length overflow"))?;
        let growth = needed.saturating_sub(self.atoms.len());
        let bytes = sequence_bytes::<Option<AtomSet>>(growth)?
            .checked_add(sequence_bytes::<TestId>(atoms.ids().len())?)
            .ok_or_else(|| HistoryError::invariant("atom payload overflow"))?;
        let projected = self.store.projected(bytes)?;
        proof_decl! { let ghost reserved_pair = *self; }
        let reserved = world.try_reserve_vec(&mut self.atoms, growth);
        proof! { lemma_pair_symbolic_frame(reserved_pair, *self); }
        allocation(reserved)?;
        world.checkpoint(timer)?;
        proof_decl! { let ghost prior_atoms = self.atoms@; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pair_wf(*self), pair_frame(entry, *self),
                self.store.graph() == old(self).store.graph() || model::graph_extends(old(self).store.graph(), self.store.graph()),
                prior_atoms.is_prefix_of(self.atoms@),
                forall|i: int| prior_atoms.len() <= i < self.atoms@.len() ==> self.atoms@[i] is None,
                index == transition@, transition@ < self.store.graph().transitions.len(),
                atoms_wf(self.store.graph(), transition@, atoms@),
                successor_entries((*self).successors) == successor_entries(entry.successors),
                self.atoms@.len() <= needed || self.atoms@ == prior_atoms,
            decreases needed - self.atoms@.len(),
        ))]
        while self.atoms.len() < needed {
            proof_decl! { let ghost before_push = *self; }
            self.atoms.push(None);
            proof! {
                assert(atom_cache_wf(self.store.graph(), self.atoms@));
                assert(successor_entries_wf(self.store.graph(), self.atoms@, successor_entries((*self).successors)));
                assert(symbolic::verify::derivative_cache_wf(self.store.graph(), self.derivatives@));
                assert forall|key: ClassKey| successor_entries((*self).successors).contains_key(key) implies
                    key.transition@ < before_push.atoms@.len() && self.atoms@[key.transition@ as int] == before_push.atoms@[key.transition@ as int] by {
                    assert(successor_entries(before_push.successors).contains_key(key));
                }
                assert forall|r: int| 0 <= r < self.guards@.len() && self.guards@[r] is Some
                    implies guard_wf(self.store.graph(), self.atoms@, r, self.guards@[r].unwrap()) by {
                    let guard = self.guards@[r].unwrap();
                    assert(guard_wf(before_push.store.graph(), before_push.atoms@, r, guard));
                    if guard.mask != 0 {
                        assert(self.atoms@[guard.transition@ as int] == before_push.atoms@[guard.transition@ as int]);
                    }
                }
                assert(guard_cache_wf(self.store.graph(), self.atoms@, self.guards@));
                assert(model::graph_wf(self.store.graph()));
                assert(self.store.valid_store());
                assert(self.root@ < self.store.graph().regexes.len());
                assert(match self.successors { Some(cache) => successor_entries_wf(self.store.graph(), self.atoms@, successor_cache_view(cache)), None => true });
                assert(pair_wf(*self));
            }
        }
        proof_decl! { let ghost before_slot = *self; }
        proof! {
            if index < prior_atoms.len() { assert(prior_atoms[index as int] == entry.atoms@[index as int]); }
            assert(before_slot.atoms@[index as int] is None);
        }
        let atom_slots = self.atoms.as_mut_slice();
        let slot = atom_slots
            .get_mut(index)
            .ok_or_else(|| HistoryError::invariant("invalid atom table slot"))?;
        *slot = Some(atoms);
        proof! {
            assert forall|key: ClassKey| successor_entries((*self).successors).contains_key(key) implies
                self.atoms@[key.transition@ as int] == entry.atoms@[key.transition@ as int] by {
                assert(entry.atoms@[key.transition@ as int] is Some);
                assert(key.transition != transition);
            }
            assert forall|r: int| 0 <= r < self.guards@.len() && self.guards@[r] is Some
                implies guard_wf(self.store.graph(), self.atoms@, r, self.guards@[r].unwrap()) by {
                let guard = self.guards@[r].unwrap();
                assert(guard_wf(before_slot.store.graph(), before_slot.atoms@, r, guard));
                if guard.mask != 0 {
                    assert(guard.transition@ != index);
                    assert(self.atoms@[guard.transition@ as int] == before_slot.atoms@[guard.transition@ as int]);
                }
            }
            assert(guard_cache_wf(self.store.graph(), self.atoms@, self.guards@));
            assert(pair_wf(*self));
        }
        proof_decl! { let ghost before_charge = *self; }
        self.store.set_charged_bytes(projected);
        proof! { lemma_pair_symbolic_frame(before_charge, *self); }
        world.checkpoint(timer)
    }
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), transition@ < old(self).store.graph().transitions.len(),
            residual@ < old(self).store.graph().regexes.len(),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
            result is Ok ==> has_guard(*final(self), residual),
    )]
    /// Stores `residual`'s self-loop guard for `transition` once per residual.
    fn ensure_guard(
        &mut self,
        residual: RegexId,
        transition: TransitionId,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<()> {
        proof_decl! { let ghost entry = *self; }
        let index = residual.index()?;
        if matches!(self.guards.get(index), Some(Some(_))) {
            return Ok(());
        }
        let constant = {
            let kernel = RuntimeKernel {
                store: &mut self.store,
                timer,
                world,
            };
            match kernel.transition(transition) {
                Ok(TransitionView::Const(_)) => Ok(true),
                Ok(_) => Ok(false),
                Err(error) => Err(error),
            }
        }?;
        let mask = if constant {
            0
        } else {
            self.ensure_atoms(transition, timer, world)?;
            self.guard_mask(residual, transition, timer, world)?
        };
        proof_decl! { let ghost guard = Guard { transition, mask }; let ghost certified = *self; }
        proof! { assert(guard_wf(self.store.graph(), self.atoms@, index as int, guard)); }
        let needed = index
            .checked_add(1)
            .ok_or_else(|| HistoryError::invariant("guard table length overflow"))?;
        let growth = needed.saturating_sub(self.guards.len());
        let projected = self
            .store
            .projected(sequence_bytes::<Option<Guard>>(growth)?)?;
        let reserved = world.try_reserve_vec(&mut self.guards, growth);
        proof! { lemma_pair_guard_update(certified, *self); }
        allocation(reserved)?;
        world.checkpoint(timer)?;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pair_wf(*self), pair_frame(entry, *self),
                self.store == certified.store, self.atoms@ == certified.atoms@,
                guard_wf(self.store.graph(), self.atoms@, index as int, guard),
                index == residual@, needed == index + 1,
            decreases needed - self.guards@.len(),
        ))]
        while self.guards.len() < needed {
            proof_decl! { let ghost before_push = *self; }
            self.guards.push(None);
            proof! {
                assert forall|r: int| 0 <= r < self.guards@.len() && self.guards@[r] is Some
                    implies guard_wf(self.store.graph(), self.atoms@, r, self.guards@[r].unwrap()) by {
                    assert(self.guards@[r] == before_push.guards@[r]);
                }
                lemma_pair_guard_update(before_push, *self);
            }
        }
        proof_decl! { let ghost before_slot = *self; }
        let guard_slots = self.guards.as_mut_slice();
        let slot = guard_slots
            .get_mut(index)
            .ok_or_else(|| HistoryError::invariant("invalid guard table slot"))?;
        *slot = Some(Guard { transition, mask });
        proof! {
            assert forall|r: int| 0 <= r < self.guards@.len() && self.guards@[r] is Some
                implies guard_wf(self.store.graph(), self.atoms@, r, self.guards@[r].unwrap()) by {
                if r != index { assert(self.guards@[r] == before_slot.guards@[r]); }
            }
            lemma_pair_guard_update(before_slot, *self);
        }
        proof_decl! { let ghost before_charge = *self; }
        self.store.set_charged_bytes(projected);
        proof! { lemma_pair_symbolic_frame(before_charge, *self); }
        world.checkpoint(timer)
    }
    #[allow(
        clippy::arithmetic_side_effects,
        reason = "The bounded nonzero atom count makes the class count at least two."
    )]
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), has_atoms(*old(self), transition),
            transition@ < old(self).store.graph().transitions.len(),
            residual@ < old(self).store.graph().regexes.len(),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
            final(self).atoms@ == old(self).atoms@, final(self).guards@ == old(self).guards@,
            result matches Ok(mask) ==> guard_wf(final(self).store.graph(), final(self).atoms@, residual@ as int, Guard { transition, mask }),
    )]
    /// Atoms true in every truth word whose successor leaves `residual`: each of the 2^k words
    /// is interpreted once and the leaving words are intersected. `GraphLimit` yields mask 0.
    fn guard_mask(
        &mut self,
        residual: RegexId,
        transition: TransitionId,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<u64> {
        proof_decl! { let ghost entry = *self; }
        let atoms = Self::cached_atoms(self.atoms.as_slice(), transition)?;
        let count = atoms.ids().len();
        if count == 0 || count > GUARD_MAX_ATOMS {
            return Ok(0);
        }
        let shift = u32::try_from(count)
            .map_err(|_| HistoryError::invariant("invalid guard atom count"))?;
        let classes = 1_u64
            .checked_shl(shift)
            .ok_or_else(|| HistoryError::invariant("invalid guard class count"))?;
        proof! { assert(classes >= 2) by(bit_vector) requires classes == (1u64 << shift), 1 <= shift <= 8; }
        let mut mask = classes - 1;
        let mut minterm = 0_u64;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pair_wf(*self), entry == *old(self), pair_frame(entry, *self),
                self.atoms@ == entry.atoms@, self.guards@ == entry.guards@,
                has_atoms(*self, transition), atoms@ == self.atoms@[transition@ as int].unwrap()@,
                transition@ < self.store.graph().transitions.len(), residual@ < self.store.graph().regexes.len(),
                count == atoms@.len(), 1 <= count <= 8, classes == (1u64 << (count as u32)), minterm <= classes,
                mask == 0 || forall|w: u64| w < minterm && (w & mask) != mask
                    ==> #[trigger] guard_class_covered(self.store.graph(), atoms@, residual, transition, w),
            ensures mask == 0 || minterm == classes,
            decreases classes - minterm,
        ))]
        while minterm < classes {
            world.checkpoint(timer)?;
            let words = [minterm];
            proof_decl! { let ghost before = *self; }
            let successor = {
                let mut kernel = RuntimeKernel {
                    store: &mut self.store,
                    timer,
                    world,
                };
                transition.interpret(&mut kernel, atoms, words.as_slice())
            };
            proof! {
                symbolic::verify::derivative_extends(before.store.graph(), self.store.graph());
                lemma_pair_symbolic_frame(before, *self);
                symbolic::verify::truth_words_realize_extends(before.store.graph(), self.store.graph(), atoms@, seq![minterm]);
                assert(words@ =~= seq![minterm]);
                if mask != 0 {
                    assert forall|w: u64| w < minterm && (w & mask) != mask
                        implies #[trigger] guard_class_covered(self.store.graph(), atoms@, residual, transition, w) by {
                        lemma_guard_class_covered_frame(before.store.graph(), self.store.graph(), atoms@, residual, transition, w);
                    }
                }
            }
            let successor = match successor {
                Ok(successor) => successor,
                Err(HistoryError::GraphLimit { .. }) => {
                    mask = 0;
                    break;
                }
                Err(error) => return Err(error),
            };
            if successor != residual {
                proof! {
                    let next = mask & minterm;
                    if next != 0 {
                        assert((minterm & next) == next) by(bit_vector) requires next == mask & minterm;
                        assert forall|w: u64| w <= minterm && (w & next) != next
                            implies #[trigger] guard_class_covered(self.store.graph(), atoms@, residual, transition, w) by {
                            lemma_mask_shrink(w, mask, minterm);
                            assert(mask != 0) by(bit_vector) requires next == mask & minterm, next != 0;
                        }
                    }
                }
                mask &= minterm;
            } else if mask != 0 {
                proof! {
                    assert(guard_class_covered(self.store.graph(), atoms@, residual, transition, minterm));
                    assert forall|w: u64| w <= minterm && (w & mask) != mask
                        implies #[trigger] guard_class_covered(self.store.graph(), atoms@, residual, transition, w) by {
                        if w == minterm {} else { assert(w < minterm); }
                    }
                }
            }
            proof! { assert(minterm < classes); }
            minterm = minterm.saturating_add(1);
        }
        proof! {
            let g = self.store.graph();
            if mask != 0 {
                assert forall|theta: Subst, event: EventView, word: Seq<EventView>|
                    language::event_wf(theta) && guard_blocks(g, atoms@, mask, theta, event)
                    implies model::regex_lang(g, theta, residual@, word)
                        == norm::transition_lang(g, theta, transition, event, word) by {
                    lemma_guard_blocks_word(g, atoms@, mask, theta, event);
                    let w = realized_word(g, atoms@, theta, event, atoms@.len());
                    assert(guard_class_covered(g, atoms@, residual, transition, w));
                }
            }
        }
        Ok(mask)
    }
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), has_guard(*old(self), residual),
            transition@ < old(self).store.graph().transitions.len(),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
            final(self).atoms@ == old(self).atoms@, final(self).guards@ == old(self).guards@,
            successor_entries((*final(self)).successors) == successor_entries((*old(self)).successors),
            result matches Ok(true) ==> instantiation_result(*final(self), transition, bindings@, *event, residual),
    )]
    /// `Ok(true)` when the stored guard for `residual` names `transition` and one of its masked
    /// atoms is false on `event`, i.e. the event is a certified self-loop.
    fn guard_hit(
        &mut self,
        residual: RegexId,
        transition: TransitionId,
        event: &Event,
        bindings: &Bindings,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<bool> {
        proof_decl! { let ghost entry = *self; }
        let guard = match self.guards.get(residual.index()?) {
            Some(Some(guard)) => *guard,
            _ => return Err(HistoryError::invariant("missing progress guard")),
        };
        if guard.transition != transition || guard.mask == 0 {
            return Ok(false);
        }
        let atoms = Self::cached_atoms(self.atoms.as_slice(), transition)?;
        let masks = [guard.mask];
        proof! { assert(masks@ =~= seq![guard.mask]); }
        let mut hit = false;
        let mut failure = None;
        let mut index = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pair_wf(*self), pair_frame(entry, *self),
                self.store.graph() == entry.store.graph(), self.derivatives@ == entry.derivatives@,
                successor_entries((*self).successors) == successor_entries(entry.successors), self.atoms@ == entry.atoms@, self.guards@ == entry.guards@,
                index <= atoms@.len(), has_atoms(*self, transition), atoms@ == self.atoms@[transition@ as int].unwrap()@,
                has_guard(*self, residual), self.guards@[residual@ as int] == Some(guard), guard.transition == transition, guard.mask != 0,
                masks@ == seq![guard.mask],
                hit ==> instantiation_result(*self, transition, bindings@, *event, residual),
            decreases atoms@.len() - index,
        ))]
        while index < atoms.ids().len() {
            let masked = match AtomSet::truth(masks.as_slice(), index) {
                Ok(masked) => masked,
                Err(_) => break,
            };
            if masked {
                let id = loop_try!(
                    atoms
                        .ids()
                        .get(index)
                        .ok_or_else(|| HistoryError::invariant("invalid primitive atom index")),
                    failure
                );
                let primitive = {
                    let kernel = RuntimeKernel {
                        store: &mut self.store,
                        timer,
                        world,
                    };
                    match kernel.test(*id) {
                        Ok(TestView::Atom {
                            primitive,
                            positive: true,
                        }) => Ok(primitive),
                        Ok(_) => Err(HistoryError::invariant("invalid primitive atom set")),
                        Err(error) => Err(error),
                    }
                };
                let primitive = loop_try!(primitive, failure);
                let classified = primitive.classify(event, bindings, timer, world);
                if !loop_try!(classified, failure) {
                    proof! {
                        let g = self.store.graph();
                        assert(symbolic::verify::truth_word_bit(seq![guard.mask], index as nat));
                        assert(atoms@[index as int] == *id);
                        assert(g.tests[id@ as int] == model::TestNode::Atom(primitive@, true));
                        assert(model::lift_test(g, atoms@[index as int]@) == model::Test::Atom(primitive@, true));
                        assert(!model::test_holds(bindings@,
                            model::lift_test(g, atoms@[index as int]@), event@));
                        let i = index as int;
                        assert(i as nat == index as nat);
                        assert(self.atoms@[guard.transition@ as int].unwrap()@ == atoms@);
                        assert(0 <= i < atoms@.len() && symbolic::verify::truth_word_bit(seq![guard.mask], i as nat)
                            && !model::test_holds(bindings@,
                                model::lift_test(g, atoms@[i]@), event@));
                        assert(guard_blocks(g, self.atoms@[guard.transition@ as int].unwrap()@, guard.mask,
                            bindings@, event@));
                        lemma_guard_hit(*self, residual, guard, bindings@, *event);
                    }
                    hit = true;
                    break;
                }
            }
            index = index.saturating_add(1);
        }
        if let Some(error) = failure {
            return Err(error);
        }
        Ok(hit)
    }
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), transition@ < old(self).store.graph().transitions.len(),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
            result matches Ok(id) ==> instantiation_result(*final(self), transition, bindings@, *event, id),
    )]
    fn instantiate(
        &mut self,
        transition: TransitionId,
        event: &Event,
        bindings: &Bindings,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<RegexId> {
        proof_decl! { let ghost entry = *self; }
        {
            let kernel = RuntimeKernel {
                store: &mut self.store,
                timer,
                world,
            };
            if let TransitionView::Const(regex) = kernel.transition(transition)? {
                proof! {
                    model::lemma_graph_transition_wf(self.store.graph(), transition@);
                    norm::transition_unfold(self.store.graph(), transition@);
                    assert(instantiation_result(*self, transition, bindings@, *event, regex));
                }
                return Ok(regex);
            }
        }
        self.ensure_atoms(transition, timer, world)?;
        proof_decl! { let ghost classified = *self; }
        #[cfg(test)]
        {
            self.work.event_classes = self.work.event_classes.saturating_add(1);
        }
        let atoms = Self::cached_atoms(self.atoms.as_slice(), transition)?;
        let word_count = atoms
            .ids()
            .len()
            .checked_add(63)
            .ok_or_else(|| HistoryError::invariant("truth word length overflow"))?
            .checked_div(64)
            .ok_or_else(|| HistoryError::invariant("invalid truth word divisor"))?;
        let mut words: SmallVec<[u64; 2]> = SmallVec::new();
        allocation(world.try_reserve_words(&mut words, word_count))?;
        words.resize(word_count, 0);
        proof! { lemma_zero_truth_words(words.view()); }
        let mut failure = None;
        let mut index = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pair_wf(*self), pair_frame(entry, *self),
                index <= atoms@.len(), words.view().len() == word_count,
                self.store.graph() == classified.store.graph(), self.derivatives@ == classified.derivatives@,
                successor_entries((*self).successors) == successor_entries(classified.successors), self.atoms@ == classified.atoms@,
                has_atoms(*self, transition), atom_cache_wf(self.store.graph(), self.atoms@),
                atoms@ == self.atoms@[transition@ as int].unwrap()@,
                atoms_wf(self.store.graph(), transition@, atoms@),
                forall|j: int| 0 <= j < index ==> symbolic::verify::truth_word_bit(words.view(), j as nat)
                    == model::test_holds(bindings@, model::lift_test(self.store.graph(), atoms@[j]@), event@),
                forall|j: nat| index <= j ==> !symbolic::verify::truth_word_bit(words.view(), j),
            ensures failure is None ==> index == atoms@.len(),
            decreases atoms@.len() - index,
        ))]
        while index < atoms.ids().len() {
            let id = loop_try!(
                atoms
                    .ids()
                    .get(index)
                    .ok_or_else(|| HistoryError::invariant("invalid primitive atom index")),
                failure
            );
            proof_decl! { let ghost before_words = words.view(); }
            loop_try!(world.checkpoint(timer), failure);
            let primitive = {
                let kernel = RuntimeKernel {
                    store: &mut self.store,
                    timer,
                    world,
                };
                match kernel.test(*id) {
                    Ok(TestView::Atom {
                        primitive,
                        positive: true,
                    }) => Ok(primitive),
                    Ok(_) => Err(HistoryError::invariant("invalid primitive atom set")),
                    Err(error) => Err(error),
                }
            };
            let primitive = loop_try!(primitive, failure);
            let classified = primitive.classify(event, bindings, timer, world);
            if loop_try!(classified, failure) {
                let word_index = loop_try!(
                    index
                        .checked_div(64)
                        .ok_or_else(|| HistoryError::invariant("invalid truth word divisor")),
                    failure
                );
                let bit = loop_try!(
                    u32::try_from(loop_try!(
                        index
                            .checked_rem(64)
                            .ok_or_else(|| HistoryError::invariant("invalid truth bit divisor")),
                        failure
                    ),)
                    .map_err(|_| HistoryError::invariant("invalid truth bit")),
                    failure
                );
                let truth_word = loop_try!(
                    words
                        .as_mut_slice()
                        .get_mut(word_index)
                        .ok_or_else(|| HistoryError::invariant("invalid truth word index")),
                    failure
                );
                *truth_word |= loop_try!(
                    1_u64
                        .checked_shl(bit)
                        .ok_or_else(|| HistoryError::invariant("invalid truth bit")),
                    failure
                );
                proof! { lemma_truth_word_set(before_words, words.view(), index as nat); }
            }
            index = index.saturating_add(1);
        }
        if let Some(error) = failure {
            return Err(error);
        }
        proof! {
            assert(index == atoms@.len());
            assert(symbolic::verify::truth_words_realize(self.store.graph(), atoms@, words.view(), bindings@, event@));
        }
        proof_decl! { let ghost words_view = words.view(); let ghost atoms_view = atoms@; }
        let successor = self.successor(EventClass { transition, words }, timer, world)?;
        proof! {
            assert(successor_entries((*self).successors).contains_key(ClassKey { transition, words: words_view }));
            symbolic::verify::truth_words_realize_extends(classified.store.graph(), self.store.graph(), atoms_view, words_view);
            assert(instantiation_result(*self, transition, bindings@, *event, successor));
        }
        Ok(successor)
    }
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), has_atoms(*old(self), key.transition),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
            final(self).atoms@ == old(self).atoms@,
            result matches Ok(id) ==> successor_entries((*final(self)).successors).contains_key(class_key(key))
                && successor_entries((*final(self)).successors)[class_key(key)] == id,
    )]
    /// Cached or freshly interpreted successor of `key`; every entry it publishes is covered by
    /// `successor_entries_wf`, so callers read the language equivalence from `pair_wf`.
    fn successor(
        &mut self,
        key: EventClass,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<RegexId> {
        proof_decl! { let ghost entry = *self; }
        let atoms = Self::cached_atoms(self.atoms.as_slice(), key.transition)?;
        if let Some(successor) = Self::successor_get(&mut self.successors, &key) {
            #[cfg(test)]
            {
                self.work.successor_hits = self.work.successor_hits.saturating_add(1);
            }
            return Ok(successor);
        }
        #[cfg(test)]
        {
            self.work.successor_misses = self.work.successor_misses.saturating_add(1);
        }
        let successor = {
            let mut kernel = RuntimeKernel {
                store: &mut self.store,
                timer,
                world,
            };
            key.transition.interpret(&mut kernel, atoms, &key.words)
        };
        proof! {
            symbolic::verify::derivative_extends(entry.store.graph(), self.store.graph());
            lemma_pair_symbolic_frame(entry, *self);
            symbolic::verify::truth_words_realize_extends(entry.store.graph(), self.store.graph(), atoms@, key.words.view());
        }
        let successor = successor?;
        proof! {
            assert forall|theta: Subst, current: EventView, word: Seq<EventView>|
                language::event_wf(theta) && symbolic::verify::truth_words_realize(self.store.graph(), atoms@, key.words.view(), theta, current)
                    implies model::regex_lang(self.store.graph(), theta, successor@, word)
                        == norm::transition_lang(self.store.graph(), theta, key.transition, current, word) by {}
        }
        if self.successors.is_none() {
            let cache = Self::successor_cache()
                .ok_or_else(|| HistoryError::invariant("invalid successor cache capacity"))?;
            self.successors = Some(cache);
        }
        proof_decl! { let ghost entries = successor_entries((*self).successors); }
        world.checkpoint(timer)?;
        Self::successor_put(&mut self.successors, key, successor);
        proof! {
            assert(successor_entries(self.successors).contains_key(class_key(key)));
            assert(successor_entries(self.successors)[class_key(key)] == successor);
            assert forall|other: ClassKey| successor_entries(self.successors).contains_key(other) implies
                other == class_key(key) || entries.contains_key(other) by {}
            assert forall|other: ClassKey| successor_entries((*self).successors).contains_key(other) implies {
                let i = other.transition@ as int;
                other.transition@ < self.store.graph().transitions.len() && 0 <= i < self.atoms@.len() && self.atoms@[i] is Some
                    && successor_entries((*self).successors)[other]@ < self.store.graph().regexes.len()
                    && forall|theta: Subst, current: EventView, word: Seq<EventView>|
                        language::event_wf(theta) && symbolic::verify::truth_words_realize(self.store.graph(), self.atoms@[i].unwrap()@, other.words, theta, current)
                            ==> model::regex_lang(self.store.graph(), theta, successor_entries((*self).successors)[other]@, word)
                                == norm::transition_lang(self.store.graph(), theta, other.transition, current, word)
            } by {
                if other == class_key(key) { assert(other.transition == key.transition); }
                else { assert(entries.contains_key(other)); }
            }
        }
        world.checkpoint(timer)?;
        Ok(successor)
    }
    #[cfg(feature = "cache")]
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[verus_spec(result =>
        requires pair_wf(*old(self)),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
    )]
    /// Eagerly builds derivatives, atom sets and successor classes for up to `PRECOMPILE_STATES`
    /// residual states reachable from `root`, depth-first, within the successor cache's capacity;
    /// anything beyond the budget is left to the lazy path. Errors leave the pair well-formed;
    /// `GraphLimit` means the caller should discard it.
    pub(crate) fn precompile(
        &mut self,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<()> {
        proof_decl! { let ghost entry = *self; }
        proof! { lemma_graph_ids_obey_cmp(); }
        let mut pending: WorkVec<RegexId> = WorkVec::new();
        pending.push(self.root);
        let mut seen = BTreeSet::new();
        let mut states: usize = 0;
        let mut used: u64 = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pair_wf(*self), pair_frame(entry, *self),
                entry == *old(self),
                forall|j: int| 0 <= j < pending.view().len() ==> pending.view()[j]@ < self.store.graph().regexes.len(),
                states <= PRECOMPILE_STATES, used <= SUCCESSOR_CAPACITY,
            ensures pair_wf(*self), pair_frame(entry, *self),
            decreases pending.view().len() + 2 * (SUCCESSOR_CAPACITY - used) + 2 * (PRECOMPILE_STATES - states),
        ))]
        while let Some(residual) = pending.pop() {
            if states >= PRECOMPILE_STATES {
                break;
            }
            proof! { lemma_graph_ids_obey_cmp(); }
            world.checkpoint(timer)?;
            if !seen.insert(residual) {
                continue;
            }
            states = states.saturating_add(1);
            proof_decl! { let ghost before = *self; }
            let derivative = {
                let mut kernel = RuntimeKernel {
                    store: &mut self.store,
                    timer,
                    world,
                };
                residual.derivative(&mut kernel, &mut self.derivatives)
            };
            proof! { lemma_pair_symbolic_frame(before, *self); }
            let transition = derivative?;
            let constant = {
                let kernel = RuntimeKernel {
                    store: &mut self.store,
                    timer,
                    world,
                };
                match kernel.transition(transition) {
                    Ok(TransitionView::Const(regex)) => {
                        proof! {
                            model::lemma_graph_transition_wf(self.store.graph(), transition@);
                            norm::transition_unfold(self.store.graph(), transition@);
                        }
                        Ok(Some(regex))
                    }
                    Ok(_) => Ok(None),
                    Err(error) => Err(error),
                }
            };
            if let Some(regex) = constant? {
                pending.push(regex);
                continue;
            }
            self.ensure_atoms(transition, timer, world)?;
            let atom_count = Self::cached_atoms(self.atoms.as_slice(), transition)?
                .ids()
                .len();
            // 2^atoms classes; transitions whose classes overflow the budget stay lazy.
            let shift = match u32::try_from(atom_count) {
                Ok(shift) => shift,
                Err(_) => continue,
            };
            let classes = match 1_u64.checked_shl(shift) {
                Some(classes) => classes,
                None => continue,
            };
            used = match used.checked_add(classes) {
                Some(total) if total <= SUCCESSOR_CAPACITY => total,
                _ => continue,
            };
            proof_decl! { let ghost base_len = pending.view().len(); }
            let mut minterm: u64 = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant pair_wf(*self), pair_frame(entry, *self),
                    entry == *old(self), has_atoms(*self, transition),
                    forall|j: int| 0 <= j < pending.view().len() ==> pending.view()[j]@ < self.store.graph().regexes.len(),
                    minterm <= classes, pending.view().len() == base_len + minterm,
                    states <= PRECOMPILE_STATES, used <= SUCCESSOR_CAPACITY,
                decreases classes - minterm,
            ))]
            while minterm < classes {
                world.checkpoint(timer)?;
                // The class budget admits at most 8 atoms: one truth word, as `instantiate` lays out.
                let mut words: SmallVec<[u64; 2]> = SmallVec::new();
                if atom_count > 0 {
                    words.push(minterm);
                }
                let key = EventClass { transition, words };
                proof_decl! { let ghost class = class_key(key); }
                let successor = self.successor(key, timer, world)?;
                proof! { assert(successor_entries((*self).successors).contains_key(class)); }
                pending.push(successor);
                minterm = minterm.saturating_add(1);
            }
        }
        Ok(())
    }
}

#[verus_verify]
enum Walk {
    Transition(TransitionId),
    TransitionChildren(TransitionId, usize),
    Test(TestId),
    TestChildren(TestId, usize),
}
#[verus_verify]
impl AtomSet {
    /// Collect every unsigned base primitive read anywhere in the transition DAG.
    /// Branches are deliberately not pruned using an event or request substitution.
    #[allow(
        clippy::semicolon_if_nothing_returned,
        reason = "Preserve the existing Verus-verified match arms."
    )]
    #[verus_verify]
    #[verus_spec(result =>
    requires old(store).valid_store(), model::graph_wf(old(store).graph()), root@ < old(store).graph().transitions.len(),
    ensures final(store).valid_store(), model::graph_wf(final(store).graph()),
        model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        result matches Ok(atoms) ==> atoms_wf(final(store).graph(), root@, atoms@),
)]
    pub(crate) fn from_transition<G: KernelStore>(
        store: &mut G,
        root: TransitionId,
    ) -> KernelResult<Self> {
        proof_decl! { let ghost base = store.graph(); }
        proof! { lemma_graph_ids_obey_cmp(); }
        let mut work: WorkVec<Walk> = WorkVec::new();
        work.push(Walk::Transition(root));
        let mut transitions = BTreeSet::new();
        let mut tests = BTreeSet::new();
        let mut primitives = Vec::new();
        proof! {
            reveal(collector);
            lemma_frontier_push(base, Seq::empty(), Walk::Transition(root));
            assert(visited(transitions@, tests@) =~= ISet::empty());
            assert(collector(base, root@, visited(transitions@, tests@), frontier(base, work.view()), found(store.graph(), primitives@)));
        }
        proof_decl! { let ghost mut pending_work = work.view(); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            store.valid_store(), model::graph_wf(store.graph()),
            store.restoration() == old(store).restoration(),
            model::graph_extends(base, store.graph()),
            base == old(store).graph(),
            work.view() == pending_work,
            model::graph_wf(base),
            forall|j: int| 0 <= j < work.view().len() ==> walk_wf(base, work.view()[j]),
            collector(base, root@, visited(transitions@, tests@), frontier(base, work.view()), found(store.graph(), primitives@)),
        ensures work.view().len() == 0,
            store.valid_store(), model::graph_wf(store.graph()), model::graph_extends(base, store.graph()),
            store.restoration() == old(store).restoration(),
            collector(base, root@, visited(transitions@, tests@), frontier(base, work.view()), found(store.graph(), primitives@)),
        decreases transition_atoms_work(base, work.view()),
    ))]
        while let Some(task) = work.pop() {
            proof_decl! {
                let ghost before_work = pending_work;
                let ghost rest = work.view();
                let ghost before_graph = store.graph();
                let ghost before_ids = primitives@;
                let ghost before_transitions = transitions@;
                let ghost before_tests = tests@;
                let ghost before_done = visited(transitions@, tests@);
                let ghost before_pending = frontier(base, before_work);
                let ghost before_atoms = found(store.graph(), primitives@);
            }
            proof! {
                lemma_frontier_push(base, work.view(), task);
                assert(work.view().push(task) =~= pending_work);
                assert(collector(base, root@, before_done, before_pending, before_atoms));
                assert(walk_wf(base, task));
                lemma_graph_ids_obey_cmp();
                lemma_walk_work_push(base);
            }
            store.checkpoint()?;
            match task {
                Walk::Transition(id) => {
                    if !transitions.insert(id) {
                        proof! {
                            lemma_visited_insert_transition(before_transitions, before_tests, id);
                            lemma_frontier_discharge(base, rest, task, work.view(), visited(transitions@, tests@));
                            lemma_collector_advance(base, root@, before_done, before_pending, before_atoms,
                                visited(transitions@, tests@), frontier(base, work.view()), found(store.graph(), primitives@));
                            pending_work = work.view();
                        }
                        continue;
                    }
                    proof! {
                        lemma_visited_insert_transition(before_transitions, before_tests, id);
                        model::lemma_graph_transition_wf(base, id@);
                        if base.transitions[id@ as int] is Union || base.transitions[id@ as int] is Intersect {
                            lemma_transition_walk_start(base, id);
                        }
                    }
                    match store.transition(id)? {
                        TransitionView::Const(_) => {}
                        TransitionView::If {
                            test,
                            then_transition,
                            else_transition,
                        } => {
                            work.push(Walk::Test(test));
                            work.push(Walk::Transition(then_transition));
                            work.push(Walk::Transition(else_transition));
                        }
                        TransitionView::Union(_) | TransitionView::Intersect(_) => {
                            work.push(Walk::TransitionChildren(id, 0))
                        }
                        TransitionView::Not(child)
                        | TransitionView::Append {
                            transition: child, ..
                        } => work.push(Walk::Transition(child)),
                    }
                }
                Walk::TransitionChildren(id, index) => {
                    proof! { model::lemma_graph_transition_wf(base, id@); }
                    let child = match store.transition(id)? {
                        TransitionView::Union(children) | TransitionView::Intersect(children) => {
                            children.get(index).copied()
                        }
                        _ => return Err(HistoryError::invariant("invalid transition traversal")),
                    };
                    if let Some(child) = child {
                        proof! {
                            assert(model::transition_node_child(base.transitions[id@ as int], index as nat) == Some(child@));
                            assert(child@ < base.transitions.len());
                        }
                        let next = index.checked_add(1).ok_or_else(|| {
                            HistoryError::invariant("transition child index overflow")
                        })?;
                        work.push(Walk::TransitionChildren(id, next));
                        work.push(Walk::Transition(child));
                        proof! { lemma_transition_children_walk(base, id, index, child, next); }
                    }
                }
                Walk::Test(id) => {
                    if !tests.insert(id) {
                        proof! {
                            lemma_visited_insert_test(before_transitions, before_tests, id);
                            lemma_frontier_discharge(base, rest, task, work.view(), visited(transitions@, tests@));
                            lemma_collector_advance(base, root@, before_done, before_pending, before_atoms,
                                visited(transitions@, tests@), frontier(base, work.view()), found(store.graph(), primitives@));
                            pending_work = work.view();
                        }
                        continue;
                    }
                    proof! { lemma_visited_insert_test(before_transitions, before_tests, id); }
                    proof! {
                        model::lemma_graph_test_wf(base, id@);
                        if base.tests[id@ as int] is And || base.tests[id@ as int] is Or {
                            lemma_test_walk_start(base, id);
                        }
                    }
                    match store.test(id)? {
                        TestView::True | TestView::False => {}
                        TestView::Atom { primitive, .. } => {
                            let positive = store.intern_test(TestView::Atom {
                                primitive,
                                positive: true,
                            })?;
                            store.reserve_atoms(&mut primitives, 1)?;
                            primitives.push(positive);
                            proof! {
                                lemma_found_extends(before_graph, store.graph(), before_ids);
                                lemma_found_push(store.graph(), before_ids, positive);
                                assert(primitives@[before_ids.len() as int] == positive);
                                assert(store.graph().tests[positive@ as int] == model::TestNode::Atom(primitive@, true));
                                assert(has_positive(store.graph(), primitives@, primitive@));
                            }
                        }
                        TestView::And(_) | TestView::Or(_) => work.push(Walk::TestChildren(id, 0)),
                    }
                }
                Walk::TestChildren(id, index) => {
                    proof! { model::lemma_graph_test_wf(base, id@); }
                    let child = match store.test(id)? {
                        TestView::And(children) | TestView::Or(children) => {
                            children.get(index).copied()
                        }
                        _ => return Err(HistoryError::invariant("invalid test traversal")),
                    };
                    if let Some(child) = child {
                        proof! {
                            assert(model::test_node_child(base.tests[id@ as int], index as nat) == Some(child@));
                            assert(child@ < base.tests.len());
                        }
                        let next = index
                            .checked_add(1)
                            .ok_or_else(|| HistoryError::invariant("test child index overflow"))?;
                        work.push(Walk::TestChildren(id, next));
                        work.push(Walk::Test(child));
                        proof! { lemma_test_children_walk(base, id, index, child, next); }
                    }
                }
            }
            proof! {
                lemma_work_tail_wf(base, rest, work.view());
                lemma_frontier_tail(base, work.view());
                lemma_frontier_discharge(base, rest, task, work.view(), visited(transitions@, tests@));
                lemma_collector_advance(base, root@, before_done, before_pending, before_atoms,
                    visited(transitions@, tests@), frontier(base, work.view()), found(store.graph(), primitives@));
                pending_work = work.view();
            }
        }
        proof! {
            assert(frontier(base, work.view()) =~= ISet::empty());
            lemma_collector_complete(base, root@, visited(transitions@, tests@), found(store.graph(), primitives@));
            assert forall|p: model::Primitive| transition_reaches_primitive(store.graph(), root@, p)
                implies has_positive(store.graph(), primitives@, p) by {
                lemma_transition_reaches_stable(base, store.graph(), root@, p);
                assert(transition_reaches_primitive(base, root@, p));
                assert(found(store.graph(), primitives@).contains(p));
            }
        }
        store.checkpoint()?;
        proof_decl! { let ghost collected = primitives@; }
        let primitive_slice = primitives.as_mut_slice();
        primitive_slice.sort_unstable();
        proof_decl! { let ghost sorted = primitives@; }
        proof! {
            norm::lemma_multiset_members(collected, sorted);
            lemma_found_membership(store.graph(), collected, sorted);
        }
        primitives.dedup();
        proof! {
            norm::lemma_dedup_properties(sorted);
            lemma_found_membership(store.graph(), sorted, primitives@);
            assert forall|p: model::Primitive| transition_reaches_primitive(store.graph(), root@, p)
                implies has_positive(store.graph(), primitives@, p) by {
                assert(found(store.graph(), sorted).contains(p));
                assert(found(store.graph(), primitives@).contains(p));
            }
        }
        store.checkpoint()?;
        Self::new(store, primitives)
    }
}

#[cfg(verus_keep_ghost)]
pub(crate) mod verify {
    use super::*;

    verus! {
        pub enum Vertex { Transition(nat), Test(nat) }

        pub open spec fn test_edges(g: model::Graph, id: nat) -> Seq<nat> {
            if id < g.tests.len() { match g.tests[id as int] {
                model::TestNode::And(cs) | model::TestNode::Or(cs) => cs,
                _ => Seq::empty(),
            } } else { Seq::empty() }
        }
        pub open spec fn transition_edges(g: model::Graph, id: nat) -> Seq<nat> {
            if id < g.transitions.len() { match g.transitions[id as int] {
                model::TransitionNode::If(_, a, b) => seq![a, b],
                model::TransitionNode::Union(cs) | model::TransitionNode::Intersect(cs) => cs,
                model::TransitionNode::Not(t) | model::TransitionNode::Append(t, _) => seq![t],
                _ => Seq::empty(),
            } } else { Seq::empty() }
        }
        pub open spec fn transition_tests(g: model::Graph, id: nat) -> Seq<nat> {
            if id < g.transitions.len() { match g.transitions[id as int] {
                model::TransitionNode::If(t, _, _) => seq![t], _ => Seq::empty(),
            } } else { Seq::empty() }
        }
        pub open spec fn test_reaches_primitive(g: model::Graph, id: nat, p: model::Primitive) -> bool
            decreases id,
        {
            id < g.tests.len() && (g.tests[id as int] matches model::TestNode::Atom(q, _) && q == p
                || exists|j: int| 0 <= j < test_edges(g, id).len()
                    && test_edges(g, id)[j] < id
                    && test_reaches_primitive(g, test_edges(g, id)[j], p))
        }
        pub open spec fn transition_reaches_primitive(g: model::Graph, id: nat, p: model::Primitive) -> bool
            decreases id,
        {
            id < g.transitions.len() && (
                (exists|j: int| 0 <= j < transition_tests(g, id).len()
                    && test_reaches_primitive(g, transition_tests(g, id)[j], p))
                || exists|j: int| 0 <= j < transition_edges(g, id).len()
                    && transition_edges(g, id)[j] < id
                    && transition_reaches_primitive(g, transition_edges(g, id)[j], p))
        }
        pub open spec fn has_positive(g: model::Graph, ids: Seq<TestId>, p: model::Primitive) -> bool {
            exists|j: int| 0 <= j < ids.len() && ids[j]@ < g.tests.len()
                && g.tests[ids[j]@ as int] == model::TestNode::Atom(p, true)
        }
        pub open spec fn atoms_wf(g: model::Graph, root: nat, ids: Seq<TestId>) -> bool {
            model::atom_ids_wf(g, ids) && forall|p: model::Primitive|
                transition_reaches_primitive(g, root, p) ==> has_positive(g, ids, p)
        }
        pub open spec fn found(g: model::Graph, ids: Seq<TestId>) -> ISet<model::Primitive> {
            ISet::new(|p: model::Primitive| has_positive(g, ids, p))
        }
        pub open spec fn visited(ts: Set<TransitionId>, es: Set<TestId>) -> ISet<Vertex> {
            ISet::new(|v: Vertex| match v {
                Vertex::Transition(n) => exists|id: TransitionId| ts.contains(id) && id@ == n,
                Vertex::Test(n) => exists|id: TestId| es.contains(id) && id@ == n,
            })
        }
        pub open spec fn successors(g: model::Graph, v: Vertex) -> ISet<Vertex> {
            ISet::new(|c: Vertex| match (v, c) {
                (Vertex::Transition(n), Vertex::Transition(k)) => transition_edges(g, n).contains(k),
                (Vertex::Transition(n), Vertex::Test(k)) => transition_tests(g, n).contains(k),
                (Vertex::Test(n), Vertex::Test(k)) => test_edges(g, n).contains(k),
                _ => false,
            })
        }
        pub open spec fn primitive_at(g: model::Graph, v: Vertex, p: model::Primitive) -> bool {
            match v { Vertex::Test(n) => n < g.tests.len() && (g.tests[n as int] matches model::TestNode::Atom(q, _) && q == p),
                _ => false }
        }
        pub(super) open spec fn frame(g: model::Graph, task: Walk) -> ISet<Vertex> {
            match task {
                Walk::Transition(id) => ISet::empty().insert(Vertex::Transition(id@)),
                Walk::Test(id) => ISet::empty().insert(Vertex::Test(id@)),
                Walk::TransitionChildren(id, start) => ISet::new(|v: Vertex| exists|j: int|
                    start <= j < transition_edges(g, id@).len() && v == Vertex::Transition(transition_edges(g, id@)[j])),
                Walk::TestChildren(id, start) => ISet::new(|v: Vertex| exists|j: int|
                    start <= j < test_edges(g, id@).len() && v == Vertex::Test(test_edges(g, id@)[j])),
            }
        }
        pub(super) open spec fn frontier(g: model::Graph, work: Seq<Walk>) -> ISet<Vertex> {
            ISet::new(|v: Vertex| exists|j: int| 0 <= j < work.len() && frame(g, work[j]).contains(v))
        }
        #[verifier::opaque]
        // Visiting records only immediate obligations. Recursive coverage is concluded
        // below only after the frontier is empty, by induction over acyclic graph IDs.
        pub open spec fn collector(g: model::Graph, root: nat, done: ISet<Vertex>, pending: ISet<Vertex>, atoms: ISet<model::Primitive>) -> bool {
            done.union(pending).contains(Vertex::Transition(root))
            && (forall|v: Vertex| done.contains(v) ==> successors(g, v).subset_of(done.union(pending)))
            && (forall|v: Vertex, p: model::Primitive| done.contains(v) && primitive_at(g, v, p) ==> atoms.contains(p))
        }
        pub(super) proof fn lemma_frontier_push(g: model::Graph, work: Seq<Walk>, task: Walk)
            ensures frontier(g, work.push(task)) == frontier(g, work).union(frame(g, task)),
        {
            assert forall|v: Vertex| frontier(g, work.push(task)).contains(v) == frontier(g, work).union(frame(g, task)).contains(v) by {
                if frontier(g, work.push(task)).contains(v) {
                    let j = choose|j: int| 0 <= j < work.push(task).len() && frame(g, work.push(task)[j]).contains(v);
                    if j < work.len() { assert(frame(g, work[j]).contains(v)); }
                }
                if frontier(g, work).contains(v) {
                    let j = choose|j: int| 0 <= j < work.len() && frame(g, work[j]).contains(v);
                    assert(frame(g, work.push(task)[j]).contains(v));
                }
                if frame(g, task).contains(v) { assert(frame(g, work.push(task)[work.len() as int]).contains(v)); }
            }
            assert(frontier(g, work.push(task)) =~= frontier(g, work).union(frame(g, task)));
        }
        pub proof fn lemma_visited_insert_transition(ts: Set<TransitionId>, es: Set<TestId>, id: TransitionId)
            ensures visited(ts.insert(id), es) == visited(ts, es).insert(Vertex::Transition(id@)),
        {
            assert forall|v: Vertex| visited(ts.insert(id), es).contains(v) == visited(ts, es).insert(Vertex::Transition(id@)).contains(v) by {
                match v { Vertex::Transition(n) => {
                    if visited(ts.insert(id), es).contains(v) {
                        let x = choose|x: TransitionId| ts.insert(id).contains(x) && x@ == n;
                    }
                    if visited(ts, es).contains(v) { let x = choose|x: TransitionId| ts.contains(x) && x@ == n; }
                }, Vertex::Test(n) => {} }
            }
            assert(visited(ts.insert(id), es) =~= visited(ts, es).insert(Vertex::Transition(id@)));
        }
        pub proof fn lemma_visited_insert_test(ts: Set<TransitionId>, es: Set<TestId>, id: TestId)
            ensures visited(ts, es.insert(id)) == visited(ts, es).insert(Vertex::Test(id@)),
        {
            assert forall|v: Vertex| visited(ts, es.insert(id)).contains(v) == visited(ts, es).insert(Vertex::Test(id@)).contains(v) by {
                match v { Vertex::Test(n) => {
                    if visited(ts, es.insert(id)).contains(v) { let x = choose|x: TestId| es.insert(id).contains(x) && x@ == n; }
                    if visited(ts, es).contains(v) { let x = choose|x: TestId| es.contains(x) && x@ == n; }
                }, Vertex::Transition(n) => {} }
            }
            assert(visited(ts, es.insert(id)) =~= visited(ts, es).insert(Vertex::Test(id@)));
        }
        pub proof fn lemma_collector_advance(g: model::Graph, root: nat, d0: ISet<Vertex>, p0: ISet<Vertex>, a0: ISet<model::Primitive>, d1: ISet<Vertex>, p1: ISet<Vertex>, a1: ISet<model::Primitive>)
            requires collector(g, root, d0, p0, a0), d0.subset_of(d1),
                d0.union(p0).subset_of(d1.union(p1)), a0.subset_of(a1),
                forall|v: Vertex| d1.contains(v) && !d0.contains(v) ==> successors(g, v).subset_of(d1.union(p1)),
                forall|v: Vertex, p: model::Primitive| d1.contains(v) && !d0.contains(v) && primitive_at(g, v, p) ==> a1.contains(p),
            ensures collector(g, root, d1, p1, a1),
        {
            reveal(collector);
            assert forall|v: Vertex| d1.contains(v) implies successors(g, v).subset_of(d1.union(p1)) by {
                if d0.contains(v) { assert(successors(g, v).subset_of(d0.union(p0))); }
            }
        }
        pub proof fn lemma_test_closed(g: model::Graph, done: ISet<Vertex>, atoms: ISet<model::Primitive>, id: nat, p: model::Primitive)
            requires done.contains(Vertex::Test(id)), test_reaches_primitive(g, id, p),
                forall|v: Vertex| done.contains(v) ==> successors(g, v).subset_of(done),
                forall|v: Vertex, p: model::Primitive| done.contains(v) && primitive_at(g, v, p) ==> atoms.contains(p),
            ensures atoms.contains(p),
            decreases id,
        {
            if !(g.tests[id as int] matches model::TestNode::Atom(q, _) && q == p) {
                let j = choose|j: int| 0 <= j < test_edges(g, id).len() && test_edges(g, id)[j] < id
                    && test_reaches_primitive(g, test_edges(g, id)[j], p);
                assert(test_edges(g, id).contains(test_edges(g, id)[j]));
                assert(successors(g, Vertex::Test(id)).contains(Vertex::Test(test_edges(g, id)[j])));
                lemma_test_closed(g, done, atoms, test_edges(g, id)[j], p);
            } else {
                assert(primitive_at(g, Vertex::Test(id), p));
            }
        }
        pub proof fn lemma_transition_closed(g: model::Graph, done: ISet<Vertex>, atoms: ISet<model::Primitive>, id: nat, p: model::Primitive)
            requires done.contains(Vertex::Transition(id)), transition_reaches_primitive(g, id, p),
                forall|v: Vertex| done.contains(v) ==> successors(g, v).subset_of(done),
                forall|v: Vertex, p: model::Primitive| done.contains(v) && primitive_at(g, v, p) ==> atoms.contains(p),
            ensures atoms.contains(p),
            decreases id,
        {
            if exists|j: int| 0 <= j < transition_tests(g, id).len() && test_reaches_primitive(g, transition_tests(g, id)[j], p) {
                let j = choose|j: int| 0 <= j < transition_tests(g, id).len() && test_reaches_primitive(g, transition_tests(g, id)[j], p);
                assert(transition_tests(g, id).contains(transition_tests(g, id)[j]));
                assert(successors(g, Vertex::Transition(id)).contains(Vertex::Test(transition_tests(g, id)[j])));
                lemma_test_closed(g, done, atoms, transition_tests(g, id)[j], p);
            } else {
                let j = choose|j: int| 0 <= j < transition_edges(g, id).len() && transition_edges(g, id)[j] < id
                    && transition_reaches_primitive(g, transition_edges(g, id)[j], p);
                assert(transition_edges(g, id).contains(transition_edges(g, id)[j]));
                assert(successors(g, Vertex::Transition(id)).contains(Vertex::Transition(transition_edges(g, id)[j])));
                lemma_transition_closed(g, done, atoms, transition_edges(g, id)[j], p);
            }
        }
        pub proof fn lemma_collector_complete(g: model::Graph, root: nat, done: ISet<Vertex>, atoms: ISet<model::Primitive>)
            requires collector(g, root, done, ISet::empty(), atoms),
            ensures forall|p: model::Primitive| transition_reaches_primitive(g, root, p) ==> atoms.contains(p),
        {
            reveal(collector);
            assert forall|p: model::Primitive| transition_reaches_primitive(g, root, p) implies atoms.contains(p) by {
                lemma_transition_closed(g, done, atoms, root, p);
            }
        }

        pub proof fn lemma_graph_ids_obey_cmp()
            ensures vstd::laws_cmp::obeys_cmp::<TestId>(), vstd::laws_cmp::obeys_cmp::<TransitionId>(),
                vstd::laws_cmp::obeys_cmp::<RegexId>(),
        {
            reveal(vstd::laws_eq::obeys_eq_spec_properties);
            reveal(vstd::laws_cmp::obeys_partial_cmp_spec_properties);
            reveal(vstd::laws_cmp::obeys_cmp_partial_ord);
            reveal(vstd::laws_cmp::obeys_cmp_ord);
        }

        pub proof fn lemma_found_extends(a: model::Graph, b: model::Graph, ids: Seq<TestId>)
            requires model::graph_extends(a, b),
            ensures found(a, ids).subset_of(found(b, ids)),
        {
            assert forall|p: model::Primitive| found(a, ids).contains(p) implies found(b, ids).contains(p) by {
                let j = choose|j: int| 0 <= j < ids.len() && ids[j]@ < a.tests.len()
                    && a.tests[ids[j]@ as int] == model::TestNode::Atom(p, true);
                assert(b.tests[ids[j]@ as int] == model::TestNode::Atom(p, true));
            }
        }

        pub proof fn lemma_found_push(g: model::Graph, ids: Seq<TestId>, id: TestId)
            ensures found(g, ids).subset_of(found(g, ids.push(id))),
        {
            assert forall|p: model::Primitive| found(g, ids).contains(p) implies found(g, ids.push(id)).contains(p) by {
                let j = choose|j: int| 0 <= j < ids.len() && ids[j]@ < g.tests.len()
                    && g.tests[ids[j]@ as int] == model::TestNode::Atom(p, true);
                assert(ids.push(id)[j] == ids[j]);
            }
        }

        pub(super) open spec fn walk_wf(g: model::Graph, task: Walk) -> bool {
            match task {
                Walk::Transition(id) => id@ < g.transitions.len(),
                Walk::Test(id) => id@ < g.tests.len(),
                Walk::TransitionChildren(id, _) => id@ < g.transitions.len()
                    && (g.transitions[id@ as int] is Union || g.transitions[id@ as int] is Intersect),
                Walk::TestChildren(id, _) => id@ < g.tests.len()
                    && (g.tests[id@ as int] is And || g.tests[id@ as int] is Or),
            }
        }

        // Termination measure for `AtomSet::from_transition`: the tree-unfolded size of the walk
        // over `base`. A children frame pays 1 for each continuation that pops it.
        pub open spec fn test_walk_node_work(g: model::Graph, id: nat) -> nat
            decreases id, 1nat,
        {
            if id >= g.tests.len() { 1 } else {
                match g.tests[id as int] {
                    model::TestNode::And(cs) | model::TestNode::Or(cs) => 1 + test_walk_children_work(g, cs, id),
                    _ => 1,
                }
            }
        }
        pub open spec fn test_walk_children_work(g: model::Graph, children: Seq<nat>, bound: nat) -> nat
            decreases bound, 0nat, children.len(),
        {
            if children.len() == 0 { 1 } else {
                1 + (if children[0] < bound { test_walk_node_work(g, children[0]) } else { 0 })
                    + test_walk_children_work(g, children.skip(1), bound)
            }
        }
        pub open spec fn transition_walk_node_work(g: model::Graph, id: nat) -> nat
            decreases id, 1nat,
        {
            if id >= g.transitions.len() { 1 } else {
                match g.transitions[id as int] {
                    model::TransitionNode::If(t, a, b) => 1 + test_walk_node_work(g, t)
                        + (if a < id { transition_walk_node_work(g, a) } else { 0 })
                        + (if b < id { transition_walk_node_work(g, b) } else { 0 }),
                    model::TransitionNode::Union(cs) | model::TransitionNode::Intersect(cs) =>
                        1 + transition_walk_children_work(g, cs, id),
                    model::TransitionNode::Not(c) | model::TransitionNode::Append(c, _) =>
                        1 + (if c < id { transition_walk_node_work(g, c) } else { 0 }),
                    _ => 1,
                }
            }
        }
        pub open spec fn transition_walk_children_work(g: model::Graph, children: Seq<nat>, bound: nat) -> nat
            decreases bound, 0nat, children.len(),
        {
            if children.len() == 0 { 1 } else {
                1 + (if children[0] < bound { transition_walk_node_work(g, children[0]) } else { 0 })
                    + transition_walk_children_work(g, children.skip(1), bound)
            }
        }
        pub(super) open spec fn walk_task_work(g: model::Graph, task: Walk) -> nat {
            match task {
                Walk::Transition(id) => transition_walk_node_work(g, id@),
                Walk::Test(id) => test_walk_node_work(g, id@),
                Walk::TransitionChildren(id, i) => if i < transition_edges(g, id@).len() {
                    transition_walk_children_work(g, transition_edges(g, id@).skip(i as int), id@)
                } else { 1 },
                Walk::TestChildren(id, i) => if i < test_edges(g, id@).len() {
                    test_walk_children_work(g, test_edges(g, id@).skip(i as int), id@)
                } else { 1 },
            }
        }
        pub(super) open spec fn transition_atoms_work(g: model::Graph, work: Seq<Walk>) -> nat
            decreases work.len(),
        {
            if work.len() == 0 { 0 } else {
                transition_atoms_work(g, work.drop_last()) + walk_task_work(g, work.last())
            }
        }

        pub(super) proof fn lemma_walk_work_push(g: model::Graph)
            ensures forall|work: Seq<Walk>, task: Walk| #[trigger] transition_atoms_work(g, work.push(task))
                == transition_atoms_work(g, work) + walk_task_work(g, task),
        {
            assert forall|work: Seq<Walk>, task: Walk| #[trigger] transition_atoms_work(g, work.push(task))
                == transition_atoms_work(g, work) + walk_task_work(g, task) by {
                assert(work.push(task).drop_last() =~= work);
            }
        }

        /// Entering a composite pops `1 + children` and pushes the `*Children(id, 0)` frame.
        pub(super) proof fn lemma_transition_walk_start(g: model::Graph, id: TransitionId)
            requires id@ < g.transitions.len(), g.transitions[id@ as int] is Union || g.transitions[id@ as int] is Intersect,
            ensures walk_task_work(g, Walk::Transition(id)) == 1 + walk_task_work(g, Walk::TransitionChildren(id, 0)),
        {
            assert(transition_edges(g, id@).skip(0) =~= transition_edges(g, id@));
        }

        pub(super) proof fn lemma_test_walk_start(g: model::Graph, id: TestId)
            requires id@ < g.tests.len(), g.tests[id@ as int] is And || g.tests[id@ as int] is Or,
            ensures walk_task_work(g, Walk::Test(id)) == 1 + walk_task_work(g, Walk::TestChildren(id, 0)),
        {
            assert(test_edges(g, id@).skip(0) =~= test_edges(g, id@));
        }

        /// A live continuation pops `1 + child + rest` and pushes `child` and `rest`.
        pub(super) proof fn lemma_transition_children_walk(g: model::Graph, id: TransitionId, index: usize, child: TransitionId, next: usize)
            requires model::graph_wf(g), id@ < g.transitions.len(), index < transition_edges(g, id@).len(),
                (g.transitions[id@ as int] is Union || g.transitions[id@ as int] is Intersect),
                child@ == transition_edges(g, id@)[index as int], next == index + 1,
            ensures walk_task_work(g, Walk::TransitionChildren(id, index))
                == 1 + walk_task_work(g, Walk::Transition(child)) + walk_task_work(g, Walk::TransitionChildren(id, next)),
        {
            model::lemma_graph_transition_wf(g, id@);
            let cs = transition_edges(g, id@);
            assert(cs[index as int] < id@);
            assert(cs.skip(index as int)[0] == cs[index as int]);
            assert(cs.skip(index as int).skip(1) =~= cs.skip(next as int));
            assert(transition_walk_children_work(g, cs.skip(index as int), id@)
                == 1 + transition_walk_node_work(g, cs[index as int]) + transition_walk_children_work(g, cs.skip(next as int), id@));
            if next >= cs.len() {
                assert(cs.skip(next as int).len() == 0);
                assert(transition_walk_children_work(g, cs.skip(next as int), id@) == 1);
            }
        }

        pub(super) proof fn lemma_test_children_walk(g: model::Graph, id: TestId, index: usize, child: TestId, next: usize)
            requires model::graph_wf(g), id@ < g.tests.len(), index < test_edges(g, id@).len(),
                (g.tests[id@ as int] is And || g.tests[id@ as int] is Or),
                child@ == test_edges(g, id@)[index as int], next == index + 1,
            ensures walk_task_work(g, Walk::TestChildren(id, index))
                == 1 + walk_task_work(g, Walk::Test(child)) + walk_task_work(g, Walk::TestChildren(id, next)),
        {
            model::lemma_graph_test_wf(g, id@);
            let cs = test_edges(g, id@);
            assert(cs[index as int] < id@);
            assert(cs.skip(index as int)[0] == cs[index as int]);
            assert(cs.skip(index as int).skip(1) =~= cs.skip(next as int));
            assert(test_walk_children_work(g, cs.skip(index as int), id@)
                == 1 + test_walk_node_work(g, cs[index as int]) + test_walk_children_work(g, cs.skip(next as int), id@));
            if next >= cs.len() {
                assert(cs.skip(next as int).len() == 0);
                assert(test_walk_children_work(g, cs.skip(next as int), id@) == 1);
            }
        }

        pub(super) proof fn lemma_frontier_prefix(g: model::Graph, a: Seq<Walk>, b: Seq<Walk>)
            requires a.is_prefix_of(b),
            ensures frontier(g, a).subset_of(frontier(g, b)),
        {
            assert forall|v: Vertex| frontier(g, a).contains(v) implies frontier(g, b).contains(v) by {
                let j = choose|j: int| 0 <= j < a.len() && frame(g, a[j]).contains(v);
                assert(frame(g, b[j]).contains(v));
            }
        }

        pub(super) proof fn lemma_frontier_discharge(g: model::Graph, rest: Seq<Walk>, task: Walk, after: Seq<Walk>, done: ISet<Vertex>)
            requires rest.is_prefix_of(after), frame(g, task).subset_of(done.union(frontier(g, after))),
            ensures frontier(g, rest.push(task)).subset_of(done.union(frontier(g, after))),
        {
            lemma_frontier_push(g, rest, task);
            lemma_frontier_prefix(g, rest, after);
        }

        pub(super) proof fn lemma_frontier_index(g: model::Graph, work: Seq<Walk>, index: int)
            requires 0 <= index < work.len(),
            ensures frame(g, work[index]).subset_of(frontier(g, work)),
        {
            assert forall|v: Vertex| frame(g, work[index]).contains(v) implies frontier(g, work).contains(v) by {}
        }

        pub(super) proof fn lemma_frontier_tail(g: model::Graph, work: Seq<Walk>)
            ensures
                work.len() > 0 ==> frame(g, work[work.len() - 1]).subset_of(frontier(g, work)),
                work.len() > 1 ==> frame(g, work[work.len() - 2]).subset_of(frontier(g, work)),
                work.len() > 2 ==> frame(g, work[work.len() - 3]).subset_of(frontier(g, work)),
        {
            if work.len() > 0 { lemma_frontier_index(g, work, work.len() - 1); }
            if work.len() > 1 { lemma_frontier_index(g, work, work.len() - 2); }
            if work.len() > 2 { lemma_frontier_index(g, work, work.len() - 3); }
        }

        pub proof fn lemma_test_reaches_stable(a: model::Graph, b: model::Graph, id: nat, p: model::Primitive)
            requires model::graph_extends(a, b), id < a.tests.len(),
            ensures test_reaches_primitive(a, id, p) == test_reaches_primitive(b, id, p),
            decreases id,
        {
            assert(test_edges(a, id) == test_edges(b, id));
            assert forall|j: int| 0 <= j < test_edges(a, id).len() && test_edges(a, id)[j] < id
                implies test_reaches_primitive(a, test_edges(a, id)[j], p)
                    == test_reaches_primitive(b, test_edges(a, id)[j], p) by {
                lemma_test_reaches_stable(a, b, test_edges(a, id)[j], p);
            }
        }

        pub proof fn lemma_transition_reaches_stable(a: model::Graph, b: model::Graph, id: nat, p: model::Primitive)
            requires model::graph_wf(a), model::graph_extends(a, b), id < a.transitions.len(),
            ensures transition_reaches_primitive(a, id, p) == transition_reaches_primitive(b, id, p),
            decreases id,
        {
            model::lemma_graph_transition_wf(a, id);
            assert(transition_edges(a, id) == transition_edges(b, id));
            assert(transition_tests(a, id) == transition_tests(b, id));
            assert forall|j: int| 0 <= j < transition_tests(a, id).len()
                implies test_reaches_primitive(a, transition_tests(a, id)[j], p)
                    == test_reaches_primitive(b, transition_tests(a, id)[j], p) by {
                lemma_test_reaches_stable(a, b, transition_tests(a, id)[j], p);
            }
            assert forall|j: int| 0 <= j < transition_edges(a, id).len() && transition_edges(a, id)[j] < id
                implies transition_reaches_primitive(a, transition_edges(a, id)[j], p)
                    == transition_reaches_primitive(b, transition_edges(a, id)[j], p) by {
                lemma_transition_reaches_stable(a, b, transition_edges(a, id)[j], p);
            }
        }

        pub proof fn lemma_found_membership(g: model::Graph, a: Seq<TestId>, b: Seq<TestId>)
            requires forall|id: TestId| a.contains(id) <==> b.contains(id),
            ensures found(g, a) == found(g, b),
        {
            assert forall|p: model::Primitive| found(g, a).contains(p) == found(g, b).contains(p) by {
                if found(g, a).contains(p) {
                    let j = choose|j: int| 0 <= j < a.len() && a[j]@ < g.tests.len()
                        && g.tests[a[j]@ as int] == model::TestNode::Atom(p, true);
                    assert(a.contains(a[j]));
                    let k = choose|k: int| 0 <= k < b.len() && b[k] == a[j];
                }
                if found(g, b).contains(p) {
                    let j = choose|j: int| 0 <= j < b.len() && b[j]@ < g.tests.len()
                        && g.tests[b[j]@ as int] == model::TestNode::Atom(p, true);
                    assert(b.contains(b[j]));
                    let k = choose|k: int| 0 <= k < a.len() && a[k] == b[j];
                }
            }
            assert(found(g, a) =~= found(g, b));
        }

        pub(super) proof fn lemma_work_tail_wf(g: model::Graph, rest: Seq<Walk>, after: Seq<Walk>)
            requires rest.is_prefix_of(after), after.len() <= rest.len() + 3,
                forall|j: int| 0 <= j < rest.len() ==> walk_wf(g, rest[j]),
                after.len() > rest.len() ==> walk_wf(g, after[after.len() - 1]),
                after.len() > rest.len() + 1 ==> walk_wf(g, after[after.len() - 2]),
                after.len() > rest.len() + 2 ==> walk_wf(g, after[after.len() - 3]),
            ensures forall|j: int| 0 <= j < after.len() ==> walk_wf(g, after[j]),
        {
            assert forall|j: int| 0 <= j < after.len() implies walk_wf(g, after[j]) by {
                if j < rest.len() { assert(after[j] == rest[j]); }
            }
        }

        pub proof fn lemma_atoms_wf_extends(a: model::Graph, b: model::Graph, root: nat, ids: Seq<TestId>)
            requires model::graph_wf(a), model::graph_extends(a, b), root < a.transitions.len(), atoms_wf(a, root, ids),
            ensures atoms_wf(b, root, ids),
        {
            lemma_found_extends(a, b, ids);
            assert forall|j: int| 0 <= j < ids.len() implies ids[j]@ < b.tests.len()
                && (b.tests[ids[j]@ as int] matches model::TestNode::Atom(_, true)) by {
                assert(a.tests[ids[j]@ as int] == b.tests[ids[j]@ as int]);
            }
            assert forall|p: model::Primitive| transition_reaches_primitive(b, root, p) implies has_positive(b, ids, p) by {
                lemma_transition_reaches_stable(a, b, root, p);
                assert(has_positive(a, ids, p));
                assert(found(a, ids).contains(p));
                assert(found(b, ids).contains(p));
            }
        }


    pub(crate) struct ClassKey { pub transition: TransitionId, pub words: Seq<u64> }
    pub(super) open spec fn class_key(key: EventClass) -> ClassKey {
        ClassKey { transition: key.transition, words: key.words.view() }
    }
    pub(crate) uninterp spec fn successor_cache_view(cache: LruCache<EventClass, RegexId>) -> Map<ClassKey, RegexId>;
    pub(super) open spec fn successor_entries(cache: Option<LruCache<EventClass, RegexId>>) -> Map<ClassKey, RegexId> {
        match cache { Some(cache) => successor_cache_view(cache), None => Map::empty() }
    }
    pub open(crate) spec fn atom_cache_wf(g: model::Graph, atoms: Seq<Option<AtomSet>>) -> bool {
        forall|i: int| 0 <= i < atoms.len() && atoms[i] is Some ==> i < g.transitions.len()
            && atoms_wf(g, i as nat, atoms[i].unwrap()@)
    }

    pub open(crate) spec fn successor_entries_wf(
        g: model::Graph, atoms: Seq<Option<AtomSet>>, entries: Map<ClassKey, RegexId>,
    ) -> bool {
        forall|key: ClassKey| entries.contains_key(key) ==> {
            let index = key.transition@ as int;
            key.transition@ < g.transitions.len() && 0 <= index < atoms.len() && atoms[index] is Some
            && entries[key]@ < g.regexes.len()
            && forall|theta: Subst, event: EventView, word: Seq<EventView>|
                language::event_wf(theta) && symbolic::verify::truth_words_realize(g, atoms[index].unwrap()@, key.words, theta, event)
                    ==> model::regex_lang(g, theta, entries[key]@, word)
                        == norm::transition_lang(g, theta, key.transition, event, word)
        }
    }

    /// Some masked atom of `atoms` is false on `event`.
    pub open(crate) spec fn guard_blocks(
        g: model::Graph, atoms: Seq<TestId>, mask: u64, theta: Subst, event: EventView,
    ) -> bool {
        exists|i: int| 0 <= i < atoms.len() && #[trigger] symbolic::verify::truth_word_bit(seq![mask], i as nat)
            && !model::test_holds(theta, model::lift_test(g, atoms[i]@), event)
    }

    pub open(crate) spec fn guard_wf(g: model::Graph, atoms_cache: Seq<Option<AtomSet>>, residual: int, guard: Guard) -> bool {
        guard.mask == 0 || {
            let t = guard.transition@ as int;
            0 <= residual < g.regexes.len() && guard.transition@ < g.transitions.len()
            && 0 <= t < atoms_cache.len() && atoms_cache[t] is Some
            && forall|theta: Subst, event: EventView, word: Seq<EventView>|
                language::event_wf(theta) && guard_blocks(g, atoms_cache[t].unwrap()@, guard.mask, theta, event)
                    ==> model::regex_lang(g, theta, residual as nat, word)
                        == norm::transition_lang(g, theta, guard.transition, event, word)
        }
    }

    pub open(crate) spec fn guard_cache_wf(g: model::Graph, atoms_cache: Seq<Option<AtomSet>>, guards: Seq<Option<Guard>>) -> bool {
        forall|r: int| 0 <= r < guards.len() && guards[r] is Some ==> guard_wf(g, atoms_cache, r, guards[r].unwrap())
    }

    pub(super) open spec fn has_guard(pair: CompiledPair, residual: RegexId) -> bool {
        residual@ < pair.guards@.len() && pair.guards@[residual@ as int] is Some
    }

    /// Every (theta, event) realising truth word `w` of `atoms` maps `transition` to `residual`.
    pub(super) open spec fn guard_class_covered(
        g: model::Graph, atoms: Seq<TestId>, residual: RegexId, transition: TransitionId, w: u64,
    ) -> bool {
        forall|theta: Subst, event: EventView, word: Seq<EventView>|
            language::event_wf(theta) && symbolic::verify::truth_words_realize(g, atoms, seq![w], theta, event)
                ==> model::regex_lang(g, theta, residual@, word) == norm::transition_lang(g, theta, transition, event, word)
    }

    /// Truth word of the first `n` atoms on (theta, event).
    pub(super) open spec fn realized_word(
        g: model::Graph, atoms: Seq<TestId>, theta: Subst, event: EventView, n: nat,
    ) -> u64
        decreases n,
    {
        if n == 0 { 0 } else {
            let m = (n - 1) as nat;
            realized_word(g, atoms, theta, event, m)
                | (if model::test_holds(theta, model::lift_test(g, atoms[m as int]@), event) { 1u64 << (m as u32) } else { 0u64 })
        }
    }



    pub open(crate) spec fn pair_wf(pair: CompiledPair) -> bool {
        model::graph_wf(pair.store.graph()) && pair.store.valid_store()
        && pair.root@ < pair.store.graph().regexes.len()
        && symbolic::verify::derivative_cache_wf(pair.store.graph(), pair.derivatives@)
        && atom_cache_wf(pair.store.graph(), pair.atoms@)
        && (match pair.successors { Some(cache) => successor_entries_wf(pair.store.graph(), pair.atoms@, successor_cache_view(cache)), None => true })
        && guard_cache_wf(pair.store.graph(), pair.atoms@, pair.guards@)
    }



    pub open(crate) spec fn pair_frame(before: CompiledPair, after: CompiledPair) -> bool {
        model::graph_extends(before.store.graph(), after.store.graph()) && after.root == before.root
    }


    pub open(crate) spec fn has_atoms(pair: CompiledPair, transition: TransitionId) -> bool {
        transition@ < pair.atoms@.len() && pair.atoms@[transition@ as int] is Some
    }

    pub open(crate) spec fn instantiation_result(
        pair: CompiledPair, transition: TransitionId, bindings: Subst, event: Event, result: RegexId,
    ) -> bool {
        result@ < pair.store.graph().regexes.len()
            && forall|word: Seq<EventView>| model::regex_lang(pair.store.graph(), bindings, result@, word)
                == norm::transition_lang(pair.store.graph(), bindings, transition, event@, word)
    }

    pub open(crate) spec fn residual_after_prefix(
        pair: CompiledPair, history: Seq<EventView>, bindings: Subst, count: nat, residual: RegexId,
    ) -> bool {
        count <= history.len() && residual@ < pair.store.graph().regexes.len()
            && forall|word: Seq<EventView>| model::regex_lang(pair.store.graph(), bindings, residual@, word)
                == model::regex_lang(pair.store.graph(), bindings, pair.root@,
                    history.take(count as int) + word)
    }

    pub(crate) proof fn lemma_residual_after_prefix_frame(
        before: CompiledPair, after: CompiledPair, history: Seq<EventView>,
        bindings: Subst, count: nat, residual: RegexId,
    )
        requires pair_wf(before), pair_wf(after), pair_frame(before, after),
            residual_after_prefix(before, history, bindings, count, residual),
        ensures residual_after_prefix(after, history, bindings, count, residual),
    {
        hide(language::lang); hide(model::lift_regex); hide(model::lift_transition); hide(model::test_holds);
        model::lemma_graph_wf_elim(before.store.graph());
        model::lemma_lift_regex_stable(before.store.graph(), after.store.graph(), before.root@);
        model::lemma_lift_regex_stable(before.store.graph(), after.store.graph(), residual@);
        assert forall|word: Seq<EventView>| model::regex_lang(after.store.graph(), bindings, residual@, word)
            == model::regex_lang(after.store.graph(), bindings, after.root@,
                history.take(count as int) + word) by {
            assert(model::regex_lang(before.store.graph(), bindings, residual@, word)
                == model::regex_lang(before.store.graph(), bindings, before.root@,
                    history.take(count as int) + word));
        }
    }

    pub(crate) proof fn lemma_residual_after_prefix_history_extends(
        pair: CompiledPair, before: Seq<EventView>, after: Seq<EventView>,
        bindings: Subst, count: nat, residual: RegexId,
    )
        requires before.is_prefix_of(after),
            residual_after_prefix(pair, before, bindings, count, residual),
        ensures residual_after_prefix(pair, after, bindings, count, residual),
    {
        hide(language::lang); hide(model::lift_regex); hide(model::lift_transition); hide(model::test_holds);
        assert(before.take(count as int) =~= after.take(count as int));
    }





    pub(super) proof fn lemma_zero_truth_words(words: Seq<u64>)
        requires forall|i: int| 0 <= i < words.len() ==> words[i] == 0,
        ensures forall|j: nat| !symbolic::verify::truth_word_bit(words, j),
    {
        assert forall|j: nat| !symbolic::verify::truth_word_bit(words, j) by {
            if j / 64 < words.len() {
                let bit = (j % 64) as u32;
                assert(((0u64 >> bit) & 1u64) == 0) by(bit_vector);
            }
        }
    }

    pub(super) proof fn lemma_truth_word_set(before: Seq<u64>, after: Seq<u64>, index: nat)
        requires index / 64 < before.len(),
            after == before.update((index / 64) as int, before[(index / 64) as int] | (1u64 << ((index % 64) as u32))),
        ensures symbolic::verify::truth_word_bit(after, index),
            forall|j: nat| j != index ==> symbolic::verify::truth_word_bit(after, j) == symbolic::verify::truth_word_bit(before, j),
    {
        let bit = (index % 64) as u32;
        let value = before[(index / 64) as int];
        assert(bit < 64);
        assert((((value | (1u64 << bit)) >> bit) & 1u64) != 0) by(bit_vector)
            requires bit < 64;
        assert forall|j: nat| j != index implies symbolic::verify::truth_word_bit(after, j) == symbolic::verify::truth_word_bit(before, j) by {
            if j / 64 < before.len() && j / 64 == index / 64 {
                let other = (j % 64) as u32;
                assert(other < 64);
                assert(other != bit);
                assert((((value | (1u64 << bit)) >> other) & 1u64) == ((value >> other) & 1u64)) by(bit_vector)
                    requires bit < 64, other < 64, other != bit;
            }
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    pub(super) proof fn lemma_successor_entries_frame(a: model::Graph, b: model::Graph, atoms: Seq<Option<AtomSet>>, entries: Map<ClassKey, RegexId>)
        requires model::graph_wf(a), model::graph_extends(a, b), atom_cache_wf(a, atoms), successor_entries_wf(a, atoms, entries),
        ensures successor_entries_wf(b, atoms, entries),
    {
        hide(language::lang);
        hide(language::interp_transition);
        hide(model::test_holds);
        hide(model::lift_regex);
        hide(model::lift_transition);
        model::lemma_graph_wf_elim(a);
        assert forall|key: ClassKey| entries.contains_key(key) implies {
            let index = key.transition@ as int;
            key.transition@ < b.transitions.len() && 0 <= index < atoms.len() && atoms[index] is Some
            && entries[key]@ < b.regexes.len()
            && forall|theta: Subst, event: EventView, word: Seq<EventView>|
                language::event_wf(theta) && symbolic::verify::truth_words_realize(b, atoms[index].unwrap()@, key.words, theta, event)
                    ==> model::regex_lang(b, theta, entries[key]@, word)
                        == norm::transition_lang(b, theta, key.transition, event, word)
        } by {
            let index = key.transition@ as int;
            symbolic::verify::truth_words_realize_extends(a, b, atoms[index].unwrap()@, key.words);
            model::lemma_lift_regex_stable(a, b, entries[key]@);
            model::lemma_lift_transition_stable(a, b, key.transition@);
            assert forall|theta: Subst, event: EventView, word: Seq<EventView>|
                language::event_wf(theta) && symbolic::verify::truth_words_realize(b, atoms[index].unwrap()@, key.words, theta, event)
                implies model::regex_lang(b, theta, entries[key]@, word)
                    == norm::transition_lang(b, theta, key.transition, event, word) by {
                assert(symbolic::verify::truth_words_realize(a, atoms[index].unwrap()@, key.words, theta, event));
                assert(model::regex_lang(a, theta, entries[key]@, word) == norm::transition_lang(a, theta, key.transition, event, word));
            }
        }
    }

    pub(super) proof fn lemma_pair_symbolic_frame(before: CompiledPair, after: CompiledPair)
        requires pair_wf(before), after.store.valid_store(), model::graph_wf(after.store.graph()),
            pair_frame(before, after),
            after.atoms@ == before.atoms@, after.guards@ == before.guards@, successor_entries(after.successors) == successor_entries(before.successors),
            symbolic::verify::derivative_cache_wf(after.store.graph(), after.derivatives@),
        ensures pair_wf(after),
    {
        symbolic::verify::derivative_extends(before.store.graph(), after.store.graph());
        assert forall|i: int| 0 <= i < after.atoms@.len() && after.atoms@[i] is Some implies i < after.store.graph().transitions.len()
            && atoms_wf(after.store.graph(), i as nat, after.atoms@[i].unwrap()@) by {
            lemma_atoms_wf_extends(before.store.graph(), after.store.graph(), i as nat, before.atoms@[i].unwrap()@);
        }
        lemma_successor_entries_frame(before.store.graph(), after.store.graph(), before.atoms@, successor_entries(before.successors));
        lemma_guard_cache_frame(before.store.graph(), after.store.graph(), before.atoms@, before.guards@);
    }

    /// `pair_wf` survives an update of the guard table alone.
    pub(super) proof fn lemma_pair_guard_update(before: CompiledPair, after: CompiledPair)
        requires pair_wf(before), after.store == before.store,
            after.root == before.root, after.derivatives@ == before.derivatives@,
            after.atoms@ == before.atoms@, successor_entries(after.successors) == successor_entries(before.successors),
            guard_cache_wf(after.store.graph(), after.atoms@, after.guards@),
        ensures pair_wf(after), pair_frame(before, after),
    {
    }

    pub(super) proof fn lemma_guard_cache_frame(a: model::Graph, b: model::Graph, atoms_cache: Seq<Option<AtomSet>>, guards: Seq<Option<Guard>>)
        requires model::graph_wf(a), model::graph_extends(a, b), atom_cache_wf(a, atoms_cache), guard_cache_wf(a, atoms_cache, guards),
        ensures guard_cache_wf(b, atoms_cache, guards),
    {
        assert forall|r: int| 0 <= r < guards.len() && guards[r] is Some implies guard_wf(b, atoms_cache, r, guards[r].unwrap()) by {
            lemma_guard_wf_frame(a, b, atoms_cache, r, guards[r].unwrap());
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    pub(super) proof fn lemma_guard_wf_frame(a: model::Graph, b: model::Graph, atoms_cache: Seq<Option<AtomSet>>, r: int, guard: Guard)
        requires model::graph_wf(a), model::graph_extends(a, b), atom_cache_wf(a, atoms_cache), guard_wf(a, atoms_cache, r, guard),
        ensures guard_wf(b, atoms_cache, r, guard),
    {
        hide(language::lang);
        hide(language::interp_transition);
        hide(model::test_holds);
        hide(model::lift_test);
        hide(model::lift_regex);
        hide(model::lift_transition);
        if guard.mask != 0 {
            let t = guard.transition@ as int;
            let atoms = atoms_cache[t].unwrap()@;
            assert(model::atom_ids_wf(a, atoms));
            model::lemma_graph_wf_elim(a);
            model::lemma_lift_regex_stable(a, b, r as nat);
            model::lemma_lift_transition_stable(a, b, guard.transition@);
            assert forall|theta: Subst, event: EventView, word: Seq<EventView>|
                language::event_wf(theta) && guard_blocks(b, atoms, guard.mask, theta, event)
                implies model::regex_lang(b, theta, r as nat, word)
                    == norm::transition_lang(b, theta, guard.transition, event, word) by {
                lemma_guard_blocks_frame(a, b, atoms, guard.mask, theta, event);
                assert(model::regex_lang(a, theta, r as nat, word) == norm::transition_lang(a, theta, guard.transition, event, word));
            }
        }
    }

    pub(super) proof fn lemma_guard_blocks_frame(a: model::Graph, b: model::Graph, atoms: Seq<TestId>, mask: u64, theta: Subst, event: EventView)
        requires model::graph_extends(a, b), model::atom_ids_wf(a, atoms), guard_blocks(b, atoms, mask, theta, event),
        ensures guard_blocks(a, atoms, mask, theta, event),
    {
        hide(model::test_holds);
        let i = choose|i: int| 0 <= i < atoms.len() && #[trigger] symbolic::verify::truth_word_bit(seq![mask], i as nat)
            && !model::test_holds(theta, model::lift_test(b, atoms[i]@), event);
        model::lemma_lift_test_stable(a, b, atoms[i]@);
    }

    pub(super) proof fn lemma_guard_class_covered_frame(
        before: model::Graph, after: model::Graph, atoms: Seq<TestId>, residual: RegexId, transition: TransitionId, w: u64,
    )
        requires model::graph_extends(before, after), model::graph_wf(before), model::atom_ids_wf(before, atoms),
            residual@ < before.regexes.len(), transition@ < before.transitions.len(),
            guard_class_covered(before, atoms, residual, transition, w),
        ensures guard_class_covered(after, atoms, residual, transition, w),
    {
        hide(language::lang);
        hide(language::interp_transition);
        hide(model::test_holds);
        hide(model::lift_regex);
        hide(model::lift_transition);
        model::lemma_graph_wf_elim(before);
        symbolic::verify::truth_words_realize_extends(before, after, atoms, seq![w]);
        model::lemma_lift_regex_stable(before, after, residual@);
        model::lemma_lift_transition_stable(before, after, transition@);
        assert forall|theta: Subst, event: EventView, word: Seq<EventView>|
            language::event_wf(theta) && symbolic::verify::truth_words_realize(after, atoms, seq![w], theta, event)
            implies model::regex_lang(after, theta, residual@, word) == norm::transition_lang(after, theta, transition, event, word) by {
            assert(symbolic::verify::truth_words_realize(before, atoms, seq![w], theta, event));
            assert(model::regex_lang(before, theta, residual@, word) == norm::transition_lang(before, theta, transition, event, word));
        }
    }

    pub(super) proof fn lemma_word_bit(w: u64, i: nat)
        requires i < 64,
        ensures symbolic::verify::truth_word_bit(seq![w], i) == (((w >> (i as u32)) & 1u64) != 0u64),
    {
        assert(i / 64 == 0);
        assert(i % 64 == i);
        assert(seq![w][0] == w);
    }

    pub(super) proof fn lemma_realized_word(g: model::Graph, atoms: Seq<TestId>, theta: Subst, event: EventView, n: nat)
        requires n <= atoms.len(), n <= 8,
        ensures realized_word(g, atoms, theta, event, n) < (1u64 << (n as u32)),
            forall|i: nat| i < n ==> #[trigger] symbolic::verify::truth_word_bit(seq![realized_word(g, atoms, theta, event, n)], i)
                == model::test_holds(theta, model::lift_test(g, atoms[i as int]@), event),
            forall|i: nat| n <= i ==> !#[trigger] symbolic::verify::truth_word_bit(seq![realized_word(g, atoms, theta, event, n)], i),
        decreases n,
    {
        let w = realized_word(g, atoms, theta, event, n);
        if n == 0 {
            assert(w == 0u64);
            assert((1u64 << 0u32) == 1u64) by(bit_vector);
            assert forall|i: nat| n <= i implies !#[trigger] symbolic::verify::truth_word_bit(seq![w], i) by {
                if i < 64 {
                    lemma_word_bit(w, i);
                    let j = i as u32;
                    assert(((0u64 >> j) & 1u64) == 0u64) by(bit_vector);
                }
            }
        } else {
            let m = (n - 1) as nat;
            lemma_realized_word(g, atoms, theta, event, m);
            let prev = realized_word(g, atoms, theta, event, m);
            let s = m as u32;
            let t = n as u32;
            assert(t == s + 1);
            assert(!symbolic::verify::truth_word_bit(seq![prev], m));
            if model::test_holds(theta, model::lift_test(g, atoms[m as int]@), event) {
                assert(w == prev | (1u64 << s));
                assert((prev | (1u64 << s)) < (1u64 << t)) by(bit_vector)
                    requires prev < (1u64 << s), s < 8, t == s + 1;
                assert forall|i: nat| i < 64 implies #[trigger] symbolic::verify::truth_word_bit(seq![w], i)
                    == (i == m || symbolic::verify::truth_word_bit(seq![prev], i)) by {
                    lemma_word_bit(w, i);
                    lemma_word_bit(prev, i);
                    let j = i as u32;
                    if i == m {
                        assert((((prev | (1u64 << s)) >> s) & 1u64) != 0u64) by(bit_vector) requires s < 64;
                    } else {
                        assert((((prev | (1u64 << s)) >> j) & 1u64) == ((prev >> j) & 1u64)) by(bit_vector)
                            requires s < 64, j < 64, j != s;
                    }
                }
            } else {
                assert(w == prev | 0u64);
                assert((prev | 0u64) == prev) by(bit_vector);
                assert(prev < (1u64 << t)) by(bit_vector)
                    requires prev < (1u64 << s), s < 8, t == s + 1;
            }
        }
    }

    pub(super) proof fn lemma_guard_blocks_word(g: model::Graph, atoms: Seq<TestId>, mask: u64, theta: Subst, event: EventView)
        requires atoms.len() <= 8, guard_blocks(g, atoms, mask, theta, event),
        ensures ({
            let w = realized_word(g, atoms, theta, event, atoms.len());
            w < (1u64 << (atoms.len() as u32))
                && symbolic::verify::truth_words_realize(g, atoms, seq![w], theta, event)
                && (w & mask) != mask
        }),
    {
        let w = realized_word(g, atoms, theta, event, atoms.len());
        lemma_realized_word(g, atoms, theta, event, atoms.len());
        let i = choose|i: int| 0 <= i < atoms.len() && #[trigger] symbolic::verify::truth_word_bit(seq![mask], i as nat)
            && !model::test_holds(theta, model::lift_test(g, atoms[i]@), event);
        assert(symbolic::verify::truth_word_bit(seq![w], i as nat) == model::test_holds(theta, model::lift_test(g, atoms[i]@), event));
        lemma_word_bit(w, i as nat);
        lemma_word_bit(mask, i as nat);
        let j = i as u32;
        assert(((mask >> j) & 1u64) != 0u64 && ((w >> j) & 1u64) == 0u64 ==> (w & mask) != mask) by(bit_vector)
            requires j < 64;
        assert forall|k: int| 0 <= k < atoms.len() implies #[trigger] symbolic::verify::truth_word_bit(seq![w], k as nat)
            == model::test_holds(theta, model::lift_test(g, atoms[k]@), event) by {}
    }

    pub(super) proof fn lemma_mask_shrink(w: u64, old_mask: u64, m: u64)
        ensures (w & (old_mask & m)) != (old_mask & m) ==> (w & old_mask) != old_mask,
    {
        assert((w & (old_mask & m)) != (old_mask & m) ==> (w & old_mask) != old_mask) by(bit_vector);
    }


    pub(super) proof fn lemma_guard_hit(pair: CompiledPair, residual: RegexId, guard: Guard, bindings: Subst, event: Event)
        requires pair_wf(pair), has_guard(pair, residual), pair.guards@[residual@ as int] == Some(guard), guard.mask != 0,
            language::event_wf(bindings),
            guard_blocks(pair.store.graph(), pair.atoms@[guard.transition@ as int].unwrap()@, guard.mask,
                bindings, event@),
        ensures instantiation_result(pair, guard.transition, bindings, event, residual),
    {
        assert(guard_wf(pair.store.graph(), pair.atoms@, residual@ as int, guard));
    }



    pub(super) proof fn lemma_absorbing_language(pair: CompiledPair, bindings: Subst, residual: RegexId)
        requires model::graph_wf(pair.store.graph()), residual@ == pair.store.graph().constants.all || residual@ == pair.store.graph().constants.empty,
        ensures forall|word: Seq<EventView>| model::regex_lang(pair.store.graph(), bindings, residual@, word)
            == (residual@ == pair.store.graph().constants.all),
    {
        model::lemma_graph_wf_elim(pair.store.graph());
        assert forall|word: Seq<EventView>| model::regex_lang(pair.store.graph(), bindings, residual@, word)
            == (residual@ == pair.store.graph().constants.all) by {
            if residual@ == pair.store.graph().constants.all {
                assert(model::lift_regex(pair.store.graph(), residual@) == language::Regex::All);
            } else {
                assert(model::lift_regex(pair.store.graph(), residual@) == language::Regex::Empty);
            }
        }
    }




    /// `to` denotes the quotient of `from` by `events`, under `bindings`.
    pub open(crate) spec fn residual_folds(
        pair: CompiledPair, bindings: Subst, from: RegexId, events: Seq<EventView>, to: RegexId,
    ) -> bool {
        from@ < pair.store.graph().regexes.len() && to@ < pair.store.graph().regexes.len()
            && forall|word: Seq<EventView>| model::regex_lang(pair.store.graph(), bindings, to@, word)
                == model::regex_lang(pair.store.graph(), bindings, from@, events + word)
    }

    pub(super) proof fn lemma_fold_start(pair: CompiledPair, bindings: Subst, from: RegexId)
        requires from@ < pair.store.graph().regexes.len(),
        ensures residual_folds(pair, bindings, from, Seq::empty(), from),
    {
        assert forall|word: Seq<EventView>| model::regex_lang(pair.store.graph(), bindings, from@, word)
            == model::regex_lang(pair.store.graph(), bindings, from@, Seq::<EventView>::empty() + word) by {
            assert(Seq::<EventView>::empty() + word =~= word);
        }
    }

    pub(super) proof fn lemma_fold_frame(before: CompiledPair, after: CompiledPair, bindings: Subst, from: RegexId, events: Seq<EventView>, to: RegexId)
        requires pair_wf(before), pair_frame(before, after), residual_folds(before, bindings, from, events, to),
        ensures residual_folds(after, bindings, from, events, to),
    {
        hide(language::lang); hide(model::lift_regex); hide(model::lift_transition); hide(model::test_holds);
        model::lemma_graph_wf_elim(before.store.graph());
        model::lemma_lift_regex_stable(before.store.graph(), after.store.graph(), from@);
        model::lemma_lift_regex_stable(before.store.graph(), after.store.graph(), to@);
        assert forall|word: Seq<EventView>| model::regex_lang(after.store.graph(), bindings, to@, word)
            == model::regex_lang(after.store.graph(), bindings, from@, events + word) by {
            assert(model::regex_lang(before.store.graph(), bindings, to@, word)
                == model::regex_lang(before.store.graph(), bindings, from@, events + word));
        }
    }

    pub(super) proof fn lemma_fold_step(pair: CompiledPair, bindings: Subst, from: RegexId, events: Seq<EventView>, residual: RegexId, transition: TransitionId, event: Event, successor: RegexId)
        requires pair_wf(pair), residual_folds(pair, bindings, from, events, residual),
            language::event_wf(bindings),
            symbolic::verify::derivative_correct(pair.store.graph(), residual@, transition),
            instantiation_result(pair, transition, bindings, event, successor),
        ensures residual_folds(pair, bindings, from, events.push(event@), successor),
    {
        assert forall|word: Seq<EventView>| model::regex_lang(pair.store.graph(), bindings, successor@, word)
            == model::regex_lang(pair.store.graph(), bindings, from@, events.push(event@) + word) by {
            assert(events.push(event@) + word =~= events + (seq![event@] + word));
        }
    }

    pub(super) proof fn lemma_fold_absorbing(pair: CompiledPair, bindings: Subst, from: RegexId, events: Seq<EventView>, rest: Seq<EventView>, residual: RegexId)
        requires pair_wf(pair), residual_folds(pair, bindings, from, events, residual),
            residual@ == pair.store.graph().constants.all || residual@ == pair.store.graph().constants.empty,
        ensures residual_folds(pair, bindings, from, events + rest, residual),
    {
        // Keep recursive semantics opaque: absorption only needs their established equalities.
        hide(pair_wf); hide(model::regex_lang);
        hide(language::lang); hide(model::lift_regex); hide(model::test_holds); hide(model::lift_transition);
        assert(model::graph_wf(pair.store.graph())) by { reveal(pair_wf); }
        lemma_absorbing_language(pair, bindings, residual);
        assert forall|word: Seq<EventView>| model::regex_lang(pair.store.graph(), bindings, residual@, word)
            == model::regex_lang(pair.store.graph(), bindings, from@, (events + rest) + word) by {
            assert(model::regex_lang(pair.store.graph(), bindings, residual@, word)
                == (residual@ == pair.store.graph().constants.all));
            assert(model::regex_lang(pair.store.graph(), bindings, residual@, rest + word)
                == (residual@ == pair.store.graph().constants.all));
            assert(model::regex_lang(pair.store.graph(), bindings, residual@, rest + word)
                == model::regex_lang(pair.store.graph(), bindings, from@, events + (rest + word)));
            vstd::seq_lib::lemma_concat_associative(events, rest, word);
        }
    }



        }
}
