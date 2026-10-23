// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(verus_keep_ghost)]
use super::kernel::verify as model;
#[cfg(verus_keep_ghost)]
use super::normalize::verify::{test_lemma_dedup_properties, test_lemma_multiset_membership};
use super::{
    graph::{
        allocation, checkpoint, invariant, sequence_bytes, ArenaStorage, CanonicalStore,
        ObservationWorld, RuntimeKernel,
    },
    kernel::*,
    source::{classify, CompiledPattern, Symbols},
    symbolic,
    work::WorkVec,
};
#[cfg(verus_keep_ghost)]
use crate::verify::history_assumptions::*;
use crate::{utils::limits::ExecutionTimer, value::Array, Rc, Value};
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
struct EventClass {
    transition: TransitionId,
    words: SmallVec<[u64; 2]>,
}

// Concrete LRU leaves expose semantic keys and membership, not policy semantics.
#[verus_verify(external_body)]
#[verus_spec(result => ensures result matches Some(cache) ==> successor_cache_view(cache) == Map::<ClassKey, RegexId>::empty())]
fn successor_cache() -> Option<LruCache<EventClass, RegexId>> {
    NonZeroUsize::new(256).map(LruCache::new)
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

#[cfg(test)]
#[derive(Debug, Default)]
pub(crate) struct WorkCounters {
    pub(crate) events: usize,
    #[cfg(feature = "cache")]
    pub(crate) prefix_comparisons: usize,
    pub(crate) derivative_misses: usize,
    pub(crate) event_classes: usize,
    pub(crate) successor_hits: usize,
    pub(crate) successor_misses: usize,
    pub(crate) equal_event_hits: usize,
    pub(crate) self_loops: usize,
}

#[cfg(feature = "cache")]
#[verus_verify]
const CURSOR_CAPACITY: usize = 16;

#[cfg(feature = "cache")]
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
struct Cursor {
    bindings: Vec<Value>,
    consumed_len: usize,
    residual: RegexId,
}

/// Hash-consed bump graph plus graph-local derivative, primitive and event-class
/// caches. Without feature `cache`, the whole pair is released after each call.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug)]
pub(crate) struct CompiledPair {
    pub(crate) store: CanonicalStore<ArenaStorage>,
    pub(crate) symbols: Symbols,
    pub(crate) pattern: CompiledPattern,
    pub(crate) root: RegexId,
    pub(crate) derivatives: Vec<Option<TransitionId>>,
    atoms: Vec<Option<AtomSet>>,
    successors: Option<LruCache<EventClass, RegexId>>,
    #[cfg(feature = "cache")]
    snapshot: Option<Rc<Array>>,
    #[cfg(feature = "cache")]
    cursors: Vec<Cursor>,
    #[cfg(test)]
    pub(crate) work: WorkCounters,
}
#[verus_verify]
impl CompiledPair {
    pub(crate) fn release(self) {
        self.store.release();
    }

    #[verus_spec(result =>
        requires model::graph_wf(store.graph()), store.valid_store(), model::symbols_wf(symbols@), root@ < store.graph().regexes.len(),
            exists|head: crate::verify::history_specs::Head| super::source::verify::pattern_represents(pattern, symbols@, head),
        ensures pair_wf(result),
            forall|head: crate::verify::history_specs::Head, tail: crate::verify::history_specs::Regex<crate::verify::history_specs::SrcTest>|
                #[trigger] super::source::verify::pattern_represents(pattern, symbols@, head)
                && #[trigger] super::source::verify::tail_represents(store.graph(), symbols@, root, tail)
                    ==> pair_represents(result, head, tail),
    )]
    pub(crate) const fn new(
        store: CanonicalStore<ArenaStorage>,
        symbols: Symbols,
        pattern: CompiledPattern,
        root: RegexId,
    ) -> Self {
        proof_decl! { let ghost head = choose|head: crate::verify::history_specs::Head| super::source::verify::pattern_represents(pattern, symbols@, head); }
        let pair = Self {
            store,
            symbols,
            pattern,
            root,
            derivatives: Vec::new(),
            atoms: Vec::new(),
            successors: None,
            #[cfg(feature = "cache")]
            snapshot: None,
            #[cfg(feature = "cache")]
            cursors: Vec::new(),
            #[cfg(test)]
            work: WorkCounters {
                events: 0,
                #[cfg(feature = "cache")]
                prefix_comparisons: 0,
                derivative_misses: 0,
                event_classes: 0,
                successor_hits: 0,
                successor_misses: 0,
                equal_event_hits: 0,
                self_loops: 0,
            },
        };
        proof! {
            assert(pair.store.graph() == store.graph());
            assert(pair.store.valid_store());
            assert(model::graph_wf(pair.store.graph()));
            assert(model::symbols_wf(pair.symbols@));
            assert(pair.root@ < pair.store.graph().regexes.len());
            assert(super::source::verify::pattern_represents(pair.pattern, pair.symbols@, head));
            assert(exists|head: crate::verify::history_specs::Head| super::source::verify::pattern_represents(pair.pattern, pair.symbols@, head));
            assert(symbolic::verify::derivative_cache_wf(pair.store.graph(), pair.derivatives@));
            assert(atom_cache_wf(pair.store.graph(), pair.atoms@));
            assert(cursor_cache_wf(pair));
            assert(pair_wf(pair));
        }
        pair
    }
}

impl CompiledPair {
    #[verus_verify]
    #[verus_spec(result =>
        requires pair_wf(*old(self)),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
            forall|head: crate::verify::history_specs::Head, tail: crate::verify::history_specs::Regex<crate::verify::history_specs::SrcTest>|
                #[trigger] pair_represents(*old(self), head, tail) ==> pair_represents(*final(self), head, tail)
                    && (result matches Ok(answer) ==> answer == crate::verify::history_specs::pair_lang(head, tail,
                        crate::verify::value_specs::value_view(*request), crate::verify::value_specs::history_view(*history))),
    )]
    pub(crate) fn evaluate(
        &mut self,
        history: &Rc<Array>,
        request: &Value,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<bool> {
        proof_decl! { let ghost entry = *self; }
        proof! { lemma_pair_all_frames(entry); super::source::verify::lemma_array_data(*history); }
        let Some(bindings) = self.pattern.matches(request, &self.symbols, timer, world)? else {
            return Ok(false);
        };
        #[cfg(not(feature = "cache"))]
        {
            let answer = self.replay(history, &bindings, timer, world)?;
            proof! {
                assert forall|head: crate::verify::history_specs::Head, tail: crate::verify::history_specs::Regex<crate::verify::history_specs::SrcTest>|
                    pair_represents(entry, head, tail) implies answer == crate::verify::history_specs::pair_lang(head, tail, crate::verify::value_specs::value_view(*request), crate::verify::value_specs::history_view(*history)) by {
                    lemma_bind_compile_substitutions(*self, head, tail, crate::verify::value_specs::value_view(*request), crate::verify::value_specs::history_view(*history), bindings@, answer);
                }
            }
            Ok(answer)
        }
        #[cfg(feature = "cache")]
        {
            let continuous = self.validate_prefix(history, timer, world)?;
            proof! {
                if continuous { lemma_cursor_continuity(*self, crate::verify::value_specs::history_view(*history)); }
            }
            let mut selected: Option<usize> = None;
            if continuous {
                // ponytail: at most 16 exact binding vectors; keep the bounded
                // move-to-front scan unless profiling calls for another index.
                let mut failure = None;
                let mut index = 0;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant index <= self.cursors@.len(),
                        forall|i: int| 0 <= i < self.cursors@.len() ==> cursor_ready(*self, self.cursors@[i], crate::verify::value_specs::history_view(*history)),
                        selected matches Some(i) ==> i < self.cursors@.len()
                            && super::source::verify::values_data(bindings@) == super::source::verify::values_data(self.cursors@[i as int].bindings@),
                    decreases self.cursors@.len() - index,
                ))]
                while index < self.cursors.len() {
                    let cursor = &self.cursors[index];
                    if loop_try!(
                        equal_bindings(&bindings, &cursor.bindings, timer, world),
                        failure
                    ) {
                        selected = Some(index);
                        break;
                    }
                    index = index.saturating_add(1);
                }
                if let Some(error) = failure {
                    return Err(error);
                }
            }
            let (start, residual) = if let Some(index) = selected {
                let cursor = self
                    .cursors
                    .get(index)
                    .ok_or_else(|| invariant("invalid progress cursor index"))?;
                proof! {
                    assert(cursor_ready(*self, *cursor, crate::verify::value_specs::history_view(*history)));
                    assert(residual_after_prefix(*self, super::source::verify::values_data(history@), bindings@, cursor.consumed_len as nat, cursor.residual));
                }
                (cursor.consumed_len, cursor.residual)
            } else {
                (0, self.root)
            };
            let residual = self.replay_suffix(history, &bindings, start, residual, timer, world)?;
            let answer = self.answer(residual, timer, world)?;
            proof! {
                lemma_full_residual_answer(*self, crate::verify::value_specs::history_view(*history), bindings@, residual, answer);
                assert forall|head: crate::verify::history_specs::Head, tail: crate::verify::history_specs::Regex<crate::verify::history_specs::SrcTest>|
                    pair_represents(entry, head, tail) implies answer == crate::verify::history_specs::pair_lang(head, tail, crate::verify::value_specs::value_view(*request), crate::verify::value_specs::history_view(*history)) by {
                    lemma_bind_compile_substitutions(*self, head, tail, crate::verify::value_specs::value_view(*request), crate::verify::value_specs::history_view(*history), bindings@, answer);
                }
                if continuous { lemma_cursor_continuity(*self, crate::verify::value_specs::history_view(*history)); }
            }
            proof_decl! { let ghost publication = *self; }

            // Every fallible operation precedes metadata publication. An aborted
            // suffix may extend the pure DAG caches, never the retained prefix.
            if let Some(index) = selected {
                let cursors = self.cursors.as_mut_slice();
                let prefix = cursors
                    .get_mut(..=index)
                    .ok_or_else(|| invariant("invalid progress cursor prefix"))?;
                let cursor = prefix
                    .last_mut()
                    .ok_or_else(|| invariant("missing progress cursor"))?;
                checkpoint(timer, world)?;
                cursor.consumed_len = history.len();
                cursor.residual = residual;
                prefix.rotate_right(1);
            } else {
                if self.cursors.is_empty() || (continuous && self.cursors.len() < CURSOR_CAPACITY) {
                    allocation(world.try_reserve_vec(&mut self.cursors, 1))?;
                }
                checkpoint(timer, world)?;
                if !continuous {
                    self.cursors.clear();
                }
                if self.cursors.len() == CURSOR_CAPACITY {
                    self.cursors.pop();
                }
                self.cursors.insert(
                    0,
                    Cursor {
                        bindings,
                        consumed_len: history.len(),
                        residual,
                    },
                );
            }
            self.snapshot = Some(Rc::clone(history));
            proof! {
                assert forall|i: int| 0 <= i < self.cursors@.len() implies cursor_ready(*self, self.cursors@[i], crate::verify::value_specs::history_view(*history)) by {}
                assert(cursor_cache_wf(*self));
                lemma_publication_frame(publication, *self);
            }
            Ok(answer)
        }
    }
    #[cfg(feature = "cache")]
    #[verus_verify]
    #[verus_spec(result =>
        requires pair_wf(*old(self)),
        ensures progress_metadata_unchanged(*old(self), *final(self)), pair_frame(*old(self), *final(self)), pair_wf(*final(self)),
            result matches Ok(true) ==> old(self).snapshot is Some
                && crate::verify::value_specs::history_view(old(self).snapshot.unwrap()).is_prefix_of(crate::verify::value_specs::history_view(*history)),
    )]
    fn validate_prefix(
        &mut self,
        history: &Rc<Array>,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<bool> {
        proof! {
            super::source::verify::lemma_array_data(*history);
            if let Some(snapshot) = &self.snapshot { super::source::verify::lemma_array_data(*snapshot); }
        }
        let Some(snapshot) = self.snapshot.as_ref() else {
            return Ok(false);
        };
        if Rc::ptr_eq(snapshot, history) {
            return Ok(true);
        }
        if history.len() < snapshot.len() {
            return Ok(false);
        }
        let mut prefix_equal = true;
        let mut failure = None;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= snapshot@.len(), snapshot@.len() <= history@.len(),
                prefix_equal ==> forall|i: int| 0 <= i < index ==> crate::verify::value_specs::value_view(snapshot@[i]) == crate::verify::value_specs::value_view(history@[i]),
            ensures failure is Some || !prefix_equal || index == snapshot@.len(),
            decreases snapshot@.len() - index,
        ))]
        while index < snapshot.len() {
            loop_try!(checkpoint(timer, world), failure);
            #[cfg(test)]
            {
                self.work.prefix_comparisons = self.work.prefix_comparisons.saturating_add(1);
            }
            let equal = snapshot.as_slice()[index] == history.as_slice()[index];
            loop_try!(checkpoint(timer, world), failure);
            if !equal {
                prefix_equal = false;
                break;
            }
            index = index.saturating_add(1);
        }
        if let Some(error) = failure {
            return Err(error);
        }
        proof! {
            if prefix_equal {
                assert(crate::verify::value_specs::history_view(*snapshot) =~= crate::verify::value_specs::history_view(*history).take(snapshot@.len() as int));
            }
        }
        Ok(prefix_equal)
    }
    #[cfg(any(test, not(feature = "cache")))]
    #[verus_verify]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), bindings@.len() == pair_symbols(*old(self)).variables.len(),
            forall|i: int| 0 <= i < bindings@.len() ==> crate::verify::value_specs::value_view(bindings@[i]) != crate::verify::value_specs::Data::Undefined,
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)), progress_metadata_unchanged(*old(self), *final(self)),
            result matches Ok(answer) ==> answer == model::regex_lang(pair_graph(*final(self)), pair_symbols(*final(self)),
                super::source::verify::values_data(bindings@), pair_root(*final(self))@, super::source::verify::values_data(history@)),
    )]
    pub(crate) fn replay(
        &mut self,
        history: &Array,
        bindings: &[Value],
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<bool> {
        let residual = self.replay_suffix(history, bindings, 0, self.root, timer, world)?;
        let answer = self.answer(residual, timer, world)?;
        proof! {
            lemma_full_residual_answer(*self, super::source::verify::values_data(history@), bindings@, residual, answer);
        }
        Ok(answer)
    }
    #[verus_verify]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), residual@ < old(self).store.graph().regexes.len(),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)), progress_metadata_unchanged(*old(self), *final(self)),
            final(self).store.graph() == old(self).store.graph(),
            result matches Ok(answer) ==> answer == crate::verify::history_specs::nullable(model::lift_regex(final(self).store.graph(), residual@)),
    )]
    fn answer(
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
        let answer = super::normalize::nullable(&kernel, residual)?;
        checkpoint(kernel.timer, kernel.world)?;
        Ok(answer)
    }
    #[verus_verify]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), bindings@.len() == old(self).symbols@.variables.len(),
            forall|i: int| 0 <= i < bindings@.len() ==> crate::verify::value_specs::value_view(bindings@[i]) != crate::verify::value_specs::Data::Undefined,
            residual_after_prefix(*old(self), super::source::verify::values_data(history@), bindings@, start as nat, residual),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)), progress_metadata_unchanged(*old(self), *final(self)),
            result matches Ok(out) ==> residual_after_prefix(*final(self), super::source::verify::values_data(history@), bindings@, history@.len(), out),
    )]
    fn replay_suffix(
        &mut self,
        history: &Array,
        bindings: &[Value],
        start: usize,
        mut residual: RegexId,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<RegexId> {
        proof_decl! { let ghost entry = *self; }
        let suffix = history
            .as_slice()
            .get(start..)
            .ok_or_else(|| invariant("invalid progress cursor length"))?;
        let mut previous: Option<(TransitionId, &Value, RegexId)> = None;
        let mut failure = None;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pair_wf(*self), pair_frame(entry, *self), progress_metadata_unchanged(entry, *self),
                index <= suffix@.len(), suffix@ == history@.subrange(start as int, history@.len() as int),
                start <= history@.len(), bindings@.len() == self.symbols@.variables.len(),
                forall|i: int| 0 <= i < bindings@.len() ==> crate::verify::value_specs::value_view(bindings@[i]) != crate::verify::value_specs::Data::Undefined,
                residual_after_prefix(*self, super::source::verify::values_data(history@), bindings@, (start + index) as nat, residual),
                previous matches Some((t, e, r)) ==> t@ < self.store.graph().transitions.len() && instantiation_result(*self, t, bindings@, *e, r),
            ensures pair_wf(*self), pair_frame(entry, *self), progress_metadata_unchanged(entry, *self),
                failure is Some || residual_after_prefix(*self, super::source::verify::values_data(history@), bindings@, history@.len(), residual),
            decreases suffix@.len() - index,
        ))]
        while index < suffix.len() {
            let event = &suffix[index];
            proof_decl! { let ghost before = *self; }
            proof! { super::source::verify::lemma_source_graph_future(entry.store.graph(), before.store.graph()); }
            loop_try!(checkpoint(timer, world), failure);
            let constants = self.store.constants();
            if residual == constants.all || residual == constants.empty {
                proof! { lemma_replay_absorbing(*self, super::source::verify::values_data(history@), bindings@, (start + index) as nat, residual); }
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
                symbolic::symbolic_derivative(&mut kernel, &mut self.derivatives, residual)
            };
            proof! {
                lemma_pair_symbolic_frame(before, *self);
                lemma_replay_frame(before, *self, super::source::verify::values_data(history@), bindings@, (start + index) as nat, residual);
                if let Some((t, e, r)) = previous { lemma_previous_frame(before, *self, t, bindings@, *e, r); }
            }
            let transition = loop_try!(derivative_result, failure);
            if let Some((old_transition, old_event, successor)) = previous {
                if old_transition == transition {
                    loop_try!(checkpoint(timer, world), failure);
                    let equal = old_event == event;
                    loop_try!(checkpoint(timer, world), failure);
                    if equal {
                        #[cfg(test)]
                        {
                            self.work.equal_event_hits =
                                self.work.equal_event_hits.saturating_add(1);
                            if residual == successor {
                                self.work.self_loops = self.work.self_loops.saturating_add(1);
                            }
                        }
                        proof! { lemma_replay_step(*self, super::source::verify::values_data(history@), bindings@, (start + index) as nat, residual, transition, *event, successor); }
                        residual = successor;
                        index = index.saturating_add(1);
                        continue;
                    }
                }
            }
            proof_decl! { let ghost before_instantiate = *self; }
            let successor_result = self.instantiate(transition, event, bindings, timer, world);
            proof! {
                lemma_replay_frame(before_instantiate, *self, super::source::verify::values_data(history@), bindings@, (start + index) as nat, residual);
                if let Some((t, e, r)) = previous { lemma_previous_frame(before_instantiate, *self, t, bindings@, *e, r); }
                symbolic::verify::derivative_correct_stable(before_instantiate.store.graph(), self.store.graph(), residual@, transition);
            }
            let successor = loop_try!(successor_result, failure);
            proof! { lemma_replay_step(*self, super::source::verify::values_data(history@), bindings@, (start + index) as nat, residual, transition, *event, successor); }
            previous = Some((transition, event, successor));
            #[cfg(test)]
            {
                if residual == successor {
                    self.work.self_loops = self.work.self_loops.saturating_add(1);
                }
            }
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
            progress_metadata_unchanged(*old(self), *final(self)),
            result is Ok ==> has_atoms(*final(self), transition),
    )]
    fn ensure_atoms(
        &mut self,
        transition: TransitionId,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<()> {
        proof_decl! { let ghost entry = *self; }
        proof_decl! { let ghost compiled_head = choose|head: crate::verify::history_specs::Head| super::source::verify::pattern_represents(self.pattern, self.symbols@, head); }
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
            transition_atoms(&mut kernel, transition)
        };
        proof! {
            symbolic::verify::derivative_extends(entry.store.graph(), self.store.graph());
            lemma_pair_symbolic_frame(entry, *self);
        }
        let atoms = atoms?;
        let needed = index
            .checked_add(1)
            .ok_or_else(|| invariant("atom table length overflow"))?;
        let growth = needed.saturating_sub(self.atoms.len());
        let bytes = sequence_bytes::<Option<AtomSet>>(growth)?
            .checked_add(sequence_bytes::<TestId>(atoms.ids().len())?)
            .ok_or_else(|| invariant("atom payload overflow"))?;
        let projected = self.store.projected(bytes)?;
        proof_decl! { let ghost reserved_pair = *self; }
        let reserved = world.try_reserve_vec(&mut self.atoms, growth);
        proof! { lemma_pair_symbolic_frame(reserved_pair, *self); }
        allocation(reserved)?;
        checkpoint(timer, world)?;
        proof_decl! { let ghost prior_atoms = self.atoms@; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pair_wf(*self), pair_frame(entry, *self), progress_metadata_unchanged(entry, *self),
                super::source::verify::pattern_represents(self.pattern, self.symbols@, compiled_head),
                self.store.graph() == old(self).store.graph() || model::graph_extends(old(self).store.graph(), self.store.graph()),
                prior_atoms.is_prefix_of(self.atoms@),
                forall|i: int| prior_atoms.len() <= i < self.atoms@.len() ==> self.atoms@[i] is None,
                index == transition@, transition@ < self.store.graph().transitions.len(),
                atoms_wf(self.store.graph(), transition@, atoms@),
                successor_map(*self) == successor_map(entry),
                self.atoms@.len() <= needed || self.atoms@ == prior_atoms,
            decreases needed - self.atoms@.len(),
        ))]
        while self.atoms.len() < needed {
            proof_decl! { let ghost before_push = *self; }
            self.atoms.push(None);
            proof! {
                lemma_pair_cursor_frame(before_push, *self);
                assert(atom_cache_wf(self.store.graph(), self.atoms@));
                assert(successor_entries_wf(self.store.graph(), self.atoms@, successor_map(*self)));
                assert(symbolic::verify::derivative_cache_wf(self.store.graph(), self.derivatives@));
                assert forall|key: ClassKey| successor_map(*self).contains_key(key) implies
                    key.transition@ < before_push.atoms@.len() && self.atoms@[key.transition@ as int] == before_push.atoms@[key.transition@ as int] by {
                    assert(successor_map(before_push).contains_key(key));
                }
                assert(model::graph_wf(self.store.graph()));
                assert(self.store.valid_store());
                assert(model::symbols_wf(self.symbols@));
                assert(self.root@ < self.store.graph().regexes.len());
                assert(super::source::verify::pattern_represents(self.pattern, self.symbols@, compiled_head));
                assert(exists|head: crate::verify::history_specs::Head| super::source::verify::pattern_represents(self.pattern, self.symbols@, head));
                assert(cursor_cache_wf(*self));
                assert(match self.successors { Some(cache) => successor_entries_wf(self.store.graph(), self.atoms@, successor_cache_view(cache)), None => true });
                assert(pair_wf(*self));
            }
        }
        let atom_slots = self.atoms.as_mut_slice();
        let slot = atom_slots
            .get_mut(index)
            .ok_or_else(|| invariant("invalid atom table slot"))?;
        *slot = Some(atoms);
        proof! {
            assert forall|key: ClassKey| successor_map(*self).contains_key(key) implies
                self.atoms@[key.transition@ as int] == entry.atoms@[key.transition@ as int] by {
                assert(entry.atoms@[key.transition@ as int] is Some);
                assert(key.transition != transition);
            }
            assert(pair_wf(*self));
        }
        proof_decl! { let ghost before_charge = *self; }
        self.store.set_charged_bytes(projected);
        proof! { lemma_pair_symbolic_frame(before_charge, *self); }
        checkpoint(timer, world)
    }
    #[verus_verify]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[verus_spec(result =>
        requires pair_wf(*old(self)), transition@ < old(self).store.graph().transitions.len(),
        ensures pair_wf(*final(self)), pair_frame(*old(self), *final(self)),
            progress_metadata_unchanged(*old(self), *final(self)),
            result matches Ok(id) ==> instantiation_result(*final(self), transition, bindings@, *event, id),
    )]
    fn instantiate(
        &mut self,
        transition: TransitionId,
        event: &Value,
        bindings: &[Value],
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
                    super::normalize::verify::transition_unfold(self.store.graph(), transition@);
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
        let transition_index = transition.index()?;
        let atoms = self
            .atoms
            .get(transition_index)
            .ok_or_else(|| invariant("missing transition atoms"))?
            .as_ref()
            .ok_or_else(|| invariant("missing transition atoms"))?;
        let word_count = atoms
            .ids()
            .len()
            .checked_add(63)
            .ok_or_else(|| invariant("truth word length overflow"))?
            .checked_div(64)
            .ok_or_else(|| invariant("invalid truth word divisor"))?;
        let mut words: SmallVec<[u64; 2]> = SmallVec::new();
        allocation(world.try_reserve_words(&mut words, word_count))?;
        words.resize(word_count, 0);
        proof! { lemma_zero_truth_words(words.view()); }
        let mut failure = None;
        let mut index = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant pair_wf(*self), pair_frame(entry, *self), progress_metadata_unchanged(entry, *self),
                index <= atoms@.len(), words.view().len() == word_count,
                self.store.graph() == classified.store.graph(), self.derivatives@ == classified.derivatives@,
                successor_map(*self) == successor_map(classified), self.atoms@ == classified.atoms@,
                transition_index == transition@, has_atoms(*self, transition),
                atom_cache_wf(self.store.graph(), self.atoms@),
                atoms@ == self.atoms@[transition_index as int].unwrap()@,
                atoms_wf(self.store.graph(), transition@, atoms@),
                forall|j: int| 0 <= j < index ==> symbolic::verify::truth_word_bit(words.view(), j as nat)
                    == model::test_holds(self.symbols@, super::source::verify::values_data(bindings@), model::lift_test(self.store.graph(), atoms@[j]@), crate::verify::value_specs::value_view(*event)),
                forall|j: nat| index <= j ==> !symbolic::verify::truth_word_bit(words.view(), j),
            ensures failure is None ==> index == atoms@.len(),
            decreases atoms@.len() - index,
        ))]
        while index < atoms.ids().len() {
            let id = loop_try!(
                atoms
                    .ids()
                    .get(index)
                    .ok_or_else(|| invariant("invalid primitive atom index")),
                failure
            );
            proof_decl! { let ghost before_words = words.view(); }
            loop_try!(checkpoint(timer, world), failure);
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
                    Ok(_) => Err(invariant("invalid primitive atom set")),
                    Err(error) => Err(error),
                }
            };
            let primitive = loop_try!(primitive, failure);
            if loop_try!(
                classify(primitive, event, bindings, &self.symbols, timer, world),
                failure
            ) {
                let word_index = loop_try!(
                    index
                        .checked_div(64)
                        .ok_or_else(|| invariant("invalid truth word divisor")),
                    failure
                );
                let bit = loop_try!(
                    u32::try_from(loop_try!(
                        index
                            .checked_rem(64)
                            .ok_or_else(|| invariant("invalid truth bit divisor")),
                        failure
                    ),)
                    .map_err(|_| invariant("invalid truth bit")),
                    failure
                );
                let truth_word = loop_try!(
                    words
                        .as_mut_slice()
                        .get_mut(word_index)
                        .ok_or_else(|| invariant("invalid truth word index")),
                    failure
                );
                *truth_word |= loop_try!(
                    1_u64
                        .checked_shl(bit)
                        .ok_or_else(|| invariant("invalid truth bit")),
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
            assert(symbolic::verify::truth_words_realize(self.store.graph(), atoms@, words.view(), self.symbols@, super::source::verify::values_data(bindings@), crate::verify::value_specs::value_view(*event)));
        }
        let key = EventClass { transition, words };
        if let Some(successor) = successor_get(&mut self.successors, &key) {
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
            symbolic::interpret_transition(&mut kernel, transition, atoms, &key.words)
        };
        proof! {
            symbolic::verify::derivative_extends(classified.store.graph(), self.store.graph());
            lemma_pair_symbolic_frame(classified, *self);
            symbolic::verify::truth_words_realize_extends(classified.store.graph(), self.store.graph(), atoms@, key.words.view());
        }
        let successor = successor?;
        proof! {
            assert(instantiation_result(*self, transition, bindings@, *event, successor));
            assert forall|sym: model::Symbols, theta: Seq<crate::verify::value_specs::Data>, current: crate::verify::value_specs::Data, word: Seq<crate::verify::value_specs::Data>|
                model::symbols_wf(sym) && symbolic::verify::truth_words_realize(self.store.graph(), atoms@, key.words.view(), sym, theta, current)
                    implies model::regex_lang(self.store.graph(), sym, theta, successor@, word)
                        == super::normalize::verify::transition_lang(self.store.graph(), sym, theta, transition, current, word) by {}
        }
        if self.successors.is_none() {
            let cache =
                successor_cache().ok_or_else(|| invariant("invalid successor cache capacity"))?;
            self.successors = Some(cache);
        }
        proof_decl! { let ghost entries = successor_map(*self); }
        checkpoint(timer, world)?;
        successor_put(&mut self.successors, key, successor);
        proof! {
            assert(successor_entries(self.successors).contains_key(class_key(key)));
            assert(successor_entries(self.successors)[class_key(key)] == successor);
            assert forall|other: ClassKey| successor_entries(self.successors).contains_key(other) implies
                other == class_key(key) || entries.contains_key(other) by {}
            assert forall|other: ClassKey| successor_map(*self).contains_key(other) implies {
                let i = other.transition@ as int;
                other.transition@ < self.store.graph().transitions.len() && 0 <= i < self.atoms@.len() && self.atoms@[i] is Some
                    && successor_map(*self)[other]@ < self.store.graph().regexes.len()
                    && forall|sym: model::Symbols, theta: Seq<crate::verify::value_specs::Data>, current: crate::verify::value_specs::Data, word: Seq<crate::verify::value_specs::Data>|
                        model::symbols_wf(sym) && symbolic::verify::truth_words_realize(self.store.graph(), self.atoms@[i].unwrap()@, other.words, sym, theta, current)
                            ==> model::regex_lang(self.store.graph(), sym, theta, successor_map(*self)[other]@, word)
                                == super::normalize::verify::transition_lang(self.store.graph(), sym, theta, other.transition, current, word)
            } by {
                if other == class_key(key) { assert(other.transition == transition); }
                else { assert(entries.contains_key(other)); }
            }
        }
        proof! {
            lemma_pair_cursor_frame(classified, *self);
            assert(model::graph_wf(self.store.graph()));
            assert(self.store.valid_store());
            assert(model::symbols_wf(self.symbols@));
            assert(self.root@ < self.store.graph().regexes.len());
            assert(atom_cache_wf(self.store.graph(), self.atoms@));
            assert(symbolic::verify::derivative_cache_wf(self.store.graph(), self.derivatives@));
            let head = choose|head: crate::verify::history_specs::Head| super::source::verify::pattern_represents(entry.pattern, entry.symbols@, head);
            assert(super::source::verify::pattern_represents(self.pattern, self.symbols@, head));
            assert(exists|head: crate::verify::history_specs::Head| super::source::verify::pattern_represents(self.pattern, self.symbols@, head));
            assert(pair_wf(*self));
        }
        checkpoint(timer, world)?;
        Ok(successor)
    }
}

#[cfg(feature = "cache")]
#[verus_verify]
#[verus_spec(result =>
    ensures result matches Ok(answer) ==> answer == (super::source::verify::values_data(left@) == super::source::verify::values_data(right@)),
)]
fn equal_bindings(
    left: &[Value],
    right: &[Value],
    timer: &mut ExecutionTimer,
    world: &mut ObservationWorld,
) -> KernelResult<bool> {
    if left.len() != right.len() {
        return Ok(false);
    }
    let mut bindings_equal = true;
    let mut failure = None;
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= left.len(), left.len() == right.len(),
            bindings_equal ==> forall|i: int| 0 <= i < index ==> crate::verify::value_specs::value_view(left@[i]) == crate::verify::value_specs::value_view(right@[i]),
            !bindings_equal ==> super::source::verify::values_data(left@) != super::source::verify::values_data(right@),
        ensures failure is Some || !bindings_equal || index == left.len(),
        decreases left@.len() - index,
    ))]
    while index < left.len() {
        loop_try!(checkpoint(timer, world), failure);
        let equal = left[index] == right[index];
        loop_try!(checkpoint(timer, world), failure);
        if !equal {
            proof! {
                assert(super::source::verify::values_data(left@)[index as int] != super::source::verify::values_data(right@)[index as int]);
            }
            bindings_equal = false;
            break;
        }
        index = index.saturating_add(1);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    proof! {
        if bindings_equal {
            assert(super::source::verify::values_data(left@) =~= super::source::verify::values_data(right@));
        }
    }
    Ok(bindings_equal)
}

#[verus_verify]
enum Walk {
    Transition(TransitionId),
    TransitionChildren(TransitionId, usize),
    Test(TestId),
    TestChildren(TestId, usize),
}
/// Collect every unsigned base primitive read anywhere in the transition DAG.
/// Branches are deliberately not pruned using an event or request substitution.
#[verus_verify]
#[verus_spec(result =>
    requires old(store).valid_store(), model::graph_wf(old(store).graph()), root@ < old(store).graph().transitions.len(),
    ensures final(store).valid_store(), model::graph_wf(final(store).graph()),
        model::graph_extends(old(store).graph(), final(store).graph()),
        final(store).restoration() == old(store).restoration(),
        result matches Ok(atoms) ==> atoms_wf(final(store).graph(), root@, atoms@),
)]
pub(crate) fn transition_atoms<G: KernelStore>(
    store: &mut G,
    root: TransitionId,
) -> KernelResult<AtomSet> {
    proof_decl! { let ghost base = store.graph(); }
    proof! { lemma_atom_ids_obey_cmp(); }
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
            lemma_atom_ids_obey_cmp();
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
                    _ => return Err(invariant("invalid transition traversal")),
                };
                if let Some(child) = child {
                    proof! {
                        assert(model::transition_node_child(base.transitions[id@ as int], index as nat) == Some(child@));
                        assert(child@ < base.transitions.len());
                    }
                    let next = index
                        .checked_add(1)
                        .ok_or_else(|| invariant("transition child index overflow"))?;
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
                    _ => return Err(invariant("invalid test traversal")),
                };
                if let Some(child) = child {
                    proof! {
                        assert(model::test_node_child(base.tests[id@ as int], index as nat) == Some(child@));
                        assert(child@ < base.tests.len());
                    }
                    let next = index
                        .checked_add(1)
                        .ok_or_else(|| invariant("test child index overflow"))?;
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
        test_lemma_multiset_membership(collected, sorted);
        lemma_found_membership(store.graph(), collected, sorted);
    }
    primitives.dedup();
    proof! {
        test_lemma_dedup_properties(sorted);
        lemma_found_membership(store.graph(), sorted, primitives@);
        assert forall|p: model::Primitive| transition_reaches_primitive(store.graph(), root@, p)
            implies has_positive(store.graph(), primitives@, p) by {
            assert(found(store.graph(), sorted).contains(p));
            assert(found(store.graph(), primitives@).contains(p));
        }
    }
    store.checkpoint()?;
    super::kernel::atom_set(store, primitives)
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

        pub proof fn lemma_atom_ids_obey_cmp()
            ensures vstd::laws_cmp::obeys_cmp::<TestId>(), vstd::laws_cmp::obeys_cmp::<TransitionId>(),
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

        // Termination measure for `transition_atoms`: the tree-unfolded size of the walk
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

    use crate::verify::history_algebra as algebra;
    use crate::verify::{history_specs as language, value_specs::{Data, history_view}};
    use super::super::source::verify as source_model;
    use super::super::normalize::verify as norm;

    pub(super) struct ClassKey { pub transition: TransitionId, pub words: Seq<u64> }
    pub(super) open spec fn class_key(key: EventClass) -> ClassKey {
        ClassKey { transition: key.transition, words: key.words.view() }
    }
    pub(super) uninterp spec fn successor_cache_view(cache: LruCache<EventClass, RegexId>) -> Map<ClassKey, RegexId>;
    pub(super) open spec fn successor_entries(cache: Option<LruCache<EventClass, RegexId>>) -> Map<ClassKey, RegexId> {
        match cache { Some(cache) => successor_cache_view(cache), None => Map::empty() }
    }
    pub(super) open spec fn atom_cache_wf(g: model::Graph, atoms: Seq<Option<AtomSet>>) -> bool {
        forall|i: int| 0 <= i < atoms.len() && atoms[i] is Some ==> i < g.transitions.len()
            && atoms_wf(g, i as nat, atoms[i].unwrap()@)
    }

    pub(super) open spec fn successor_entries_wf(
        g: model::Graph, atoms: Seq<Option<AtomSet>>, entries: Map<ClassKey, RegexId>,
    ) -> bool {
        forall|key: ClassKey| entries.contains_key(key) ==> {
            let index = key.transition@ as int;
            key.transition@ < g.transitions.len() && 0 <= index < atoms.len() && atoms[index] is Some
            && entries[key]@ < g.regexes.len()
            && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
                model::symbols_wf(sym) && symbolic::verify::truth_words_realize(g, atoms[index].unwrap()@, key.words, sym, theta, event)
                    ==> model::regex_lang(g, sym, theta, entries[key]@, word)
                        == norm::transition_lang(g, sym, theta, key.transition, event, word)
        }
    }

    pub(super) open spec fn cursor_cache_wf(pair: CompiledPair) -> bool {
        #[cfg(feature = "cache")]
        {
        pair.cursors@.len() <= CURSOR_CAPACITY && match pair.snapshot {
            None => pair.cursors@.len() == 0,
            Some(snapshot) => forall|i: int| 0 <= i < pair.cursors@.len() ==> {
                let cursor = #[trigger] pair.cursors@[i];
                let bindings = source_model::values_data(cursor.bindings@);
                bindings.len() == pair.symbols@.variables.len()
                && (forall|j: int| 0 <= j < bindings.len() ==> bindings[j] != Data::Undefined)
                && cursor.consumed_len <= history_view(snapshot).len()
                && cursor.residual@ < pair.store.graph().regexes.len()
                && forall|word: Seq<Data>| model::regex_lang(pair.store.graph(), pair.symbols@, bindings, cursor.residual@, word)
                    == model::regex_lang(pair.store.graph(), pair.symbols@, bindings, pair.root@,
                        history_view(snapshot).take(cursor.consumed_len as int) + word)
            },
        }
        }
        #[cfg(not(feature = "cache"))]
        { true }
    }


    pub open(super) spec fn pair_wf(pair: CompiledPair) -> bool {
        model::graph_wf(pair.store.graph()) && pair.store.valid_store() && model::symbols_wf(pair.symbols@)
        && pair.root@ < pair.store.graph().regexes.len()
        && (exists|head: language::Head| source_model::pattern_represents(pair.pattern, pair.symbols@, head))
        && symbolic::verify::derivative_cache_wf(pair.store.graph(), pair.derivatives@)
        && atom_cache_wf(pair.store.graph(), pair.atoms@)
        && (match pair.successors { Some(cache) => successor_entries_wf(pair.store.graph(), pair.atoms@, successor_cache_view(cache)), None => true })
        && cursor_cache_wf(pair)
    }

    pub open(super) spec fn pair_represents(
        pair: CompiledPair, head: language::Head, tail: language::Regex<language::SrcTest>,
    ) -> bool {
        pair_wf(pair) && source_model::pattern_represents(pair.pattern, pair.symbols@, head)
            && source_model::tail_represents(pair.store.graph(), pair.symbols@, pair.root, tail)
    }

    pub open(super) spec fn pair_graph(pair: CompiledPair) -> model::Graph { pair.store.graph() }
    pub open(super) spec fn pair_symbols(pair: CompiledPair) -> model::Symbols { pair.symbols@ }
    pub open(super) spec fn pair_root(pair: CompiledPair) -> RegexId { pair.root }

    pub open(super) spec fn pair_frame(before: CompiledPair, after: CompiledPair) -> bool {
        model::graph_extends(before.store.graph(), after.store.graph()) && after.symbols@ == before.symbols@
            && after.pattern == before.pattern && after.root == before.root
    }

    pub open(super) spec fn progress_metadata_unchanged(before: CompiledPair, after: CompiledPair) -> bool {
        #[cfg(feature = "cache")]
        { after.snapshot == before.snapshot && after.cursors@ == before.cursors@ }
        #[cfg(not(feature = "cache"))]
        { true }
    }

    pub open(super) spec fn has_atoms(pair: CompiledPair, transition: TransitionId) -> bool {
        transition@ < pair.atoms@.len() && pair.atoms@[transition@ as int] is Some
    }

    pub open(super) spec fn instantiation_result(
        pair: CompiledPair, transition: TransitionId, bindings: Seq<Value>, event: Value, result: RegexId,
    ) -> bool {
        result@ < pair.store.graph().regexes.len()
            && forall|word: Seq<Data>| model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), result@, word)
                == norm::transition_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), transition, crate::verify::value_specs::value_view(event), word)
    }

    pub open(super) spec fn residual_after_prefix(
        pair: CompiledPair, history: Seq<Data>, bindings: Seq<Value>, count: nat, residual: RegexId,
    ) -> bool {
        count <= history.len() && residual@ < pair.store.graph().regexes.len()
            && forall|word: Seq<Data>| model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), residual@, word)
                == model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), pair.root@,
                    history.take(count as int) + word)
    }

    /// The runtime residual after `count` events is, modulo language, q_count.
    pub(super) proof fn lemma_residual_is_symbolic_run(pair: CompiledPair, history: Seq<Data>, bindings: Seq<Value>, count: nat, residual: RegexId, word: Seq<Data>)
        requires residual_after_prefix(pair, history, bindings, count, residual),
        ensures model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), residual@, word)
            == language::lang(model::gsem(pair.symbols@, source_model::values_data(bindings)),
                algebra::symbolic_run(model::gsem(pair.symbols@, source_model::values_data(bindings)), history.take(count as int), model::lift_regex(pair.store.graph(), pair.root@)), word),
    {
        let sem = model::gsem(pair.symbols@, source_model::values_data(bindings));
        let root = model::lift_regex(pair.store.graph(), pair.root@);
        algebra::lemma_symbolic_run_is_derive_word(sem, history.take(count as int), root);
        language::lemma_derive_word_correct(sem, history.take(count as int), root, word);
    }

    pub proof fn lemma_pair_represents_frame(before: CompiledPair, after: CompiledPair, head: language::Head, tail: language::Regex<language::SrcTest>)
        requires pair_represents(before, head, tail), pair_wf(after), pair_frame(before, after),
        ensures pair_represents(after, head, tail),
    {
        source_model::lemma_tail_represents_frame(before.store.graph(), after.store.graph(), before.symbols@, after.symbols@, before.root, tail);
    }

    pub proof fn lemma_pair_represents_wf(pair: CompiledPair, head: language::Head, tail: language::Regex<language::SrcTest>)
        requires pair_represents(pair, head, tail),
        ensures pair_wf(pair),
    {}

    pub(super) open spec fn successor_map(pair: CompiledPair) -> Map<ClassKey, RegexId> {
        successor_entries(pair.successors)
    }

    pub(super) proof fn lemma_pair_cursor_frame(before: CompiledPair, after: CompiledPair)
        requires pair_wf(before), model::graph_wf(after.store.graph()), pair_frame(before, after),
            progress_metadata_unchanged(before, after),
        ensures cursor_cache_wf(after),
    {
        #[cfg(feature = "cache")]
        { lemma_cached_cursor_frame(before, after); }
    }

    // Verus rejects fuel headers for functions pruned from the Base cursor proof.
    #[cfg(feature = "cache")]
    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    pub(super) proof fn lemma_cached_cursor_frame(before: CompiledPair, after: CompiledPair)
        requires pair_wf(before), model::graph_wf(after.store.graph()), pair_frame(before, after),
            progress_metadata_unchanged(before, after),
        ensures cursor_cache_wf(after),
    {
        hide(source_model::values_data);
        hide(history_view);
        hide(language::lang);
        hide(language::interp_transition);
        hide(model::test_holds);
        hide(model::lift_regex);
        hide(model::lift_transition);
        model::lemma_graph_wf_elim(before.store.graph());
        model::lemma_lift_regex_stable(before.store.graph(), after.store.graph(), before.root@);
        #[cfg(feature = "cache")]
        {
            if before.snapshot is Some {
                let snapshot = before.snapshot.unwrap();
                assert forall|i: int| 0 <= i < after.cursors@.len() implies {
                    let cursor = #[trigger] after.cursors@[i];
                    let bindings = source_model::values_data(cursor.bindings@);
                    bindings.len() == after.symbols@.variables.len()
                    && (forall|j: int| 0 <= j < bindings.len() ==> bindings[j] != Data::Undefined)
                    && cursor.consumed_len <= history_view(snapshot).len()
                    && cursor.residual@ < after.store.graph().regexes.len()
                    && forall|word: Seq<Data>| model::regex_lang(after.store.graph(), after.symbols@, bindings, cursor.residual@, word)
                        == model::regex_lang(after.store.graph(), after.symbols@, bindings, after.root@,
                            history_view(snapshot).take(cursor.consumed_len as int) + word)
                } by {
                    assert(after.cursors@[i] == before.cursors@[i]);
                    let cursor = before.cursors@[i];
                    model::lemma_lift_regex_stable(before.store.graph(), after.store.graph(), cursor.residual@);
                    assert forall|word: Seq<Data>| model::regex_lang(after.store.graph(), after.symbols@, source_model::values_data(cursor.bindings@), cursor.residual@, word)
                        == model::regex_lang(after.store.graph(), after.symbols@, source_model::values_data(cursor.bindings@), after.root@, history_view(snapshot).take(cursor.consumed_len as int) + word) by {
                        assert(model::regex_lang(before.store.graph(), before.symbols@, source_model::values_data(cursor.bindings@), cursor.residual@, word)
                            == model::regex_lang(before.store.graph(), before.symbols@, source_model::values_data(cursor.bindings@), before.root@, history_view(snapshot).take(cursor.consumed_len as int) + word));
                    }
                }
            }
        }
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
            && forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
                model::symbols_wf(sym) && symbolic::verify::truth_words_realize(b, atoms[index].unwrap()@, key.words, sym, theta, event)
                    ==> model::regex_lang(b, sym, theta, entries[key]@, word)
                        == norm::transition_lang(b, sym, theta, key.transition, event, word)
        } by {
            let index = key.transition@ as int;
            symbolic::verify::truth_words_realize_extends(a, b, atoms[index].unwrap()@, key.words);
            model::lemma_lift_regex_stable(a, b, entries[key]@);
            model::lemma_lift_transition_stable(a, b, key.transition@);
            assert forall|sym: model::Symbols, theta: Seq<Data>, event: Data, word: Seq<Data>|
                model::symbols_wf(sym) && symbolic::verify::truth_words_realize(b, atoms[index].unwrap()@, key.words, sym, theta, event)
                implies model::regex_lang(b, sym, theta, entries[key]@, word)
                    == norm::transition_lang(b, sym, theta, key.transition, event, word) by {
                assert(symbolic::verify::truth_words_realize(a, atoms[index].unwrap()@, key.words, sym, theta, event));
                assert(model::regex_lang(a, sym, theta, entries[key]@, word) == norm::transition_lang(a, sym, theta, key.transition, event, word));
            }
        }
    }

    pub(super) proof fn lemma_pair_symbolic_frame(before: CompiledPair, after: CompiledPair)
        requires pair_wf(before), after.store.valid_store(), model::graph_wf(after.store.graph()),
            pair_frame(before, after), progress_metadata_unchanged(before, after),
            after.atoms@ == before.atoms@, successor_map(after) == successor_map(before),
            symbolic::verify::derivative_cache_wf(after.store.graph(), after.derivatives@),
        ensures pair_wf(after),
    {
        symbolic::verify::derivative_extends(before.store.graph(), after.store.graph());
        lemma_pair_cursor_frame(before, after);
        assert forall|i: int| 0 <= i < after.atoms@.len() && after.atoms@[i] is Some implies i < after.store.graph().transitions.len()
            && atoms_wf(after.store.graph(), i as nat, after.atoms@[i].unwrap()@) by {
            lemma_atoms_wf_extends(before.store.graph(), after.store.graph(), i as nat, before.atoms@[i].unwrap()@);
        }
        lemma_successor_entries_frame(before.store.graph(), after.store.graph(), before.atoms@, successor_map(before));
    }

    pub(super) proof fn lemma_replay_frame(before: CompiledPair, after: CompiledPair, history: Seq<Data>, bindings: Seq<Value>, count: nat, residual: RegexId)
        requires pair_wf(before), pair_frame(before, after), residual_after_prefix(before, history, bindings, count, residual),
        ensures residual_after_prefix(after, history, bindings, count, residual),
    {
        hide(language::lang); hide(model::lift_regex); hide(model::lift_transition); hide(model::test_holds);
        model::lemma_graph_wf_elim(before.store.graph());
        model::lemma_lift_regex_stable(before.store.graph(), after.store.graph(), residual@);
        model::lemma_lift_regex_stable(before.store.graph(), after.store.graph(), before.root@);
        assert forall|word: Seq<Data>| model::regex_lang(after.store.graph(), after.symbols@, source_model::values_data(bindings), residual@, word)
            == model::regex_lang(after.store.graph(), after.symbols@, source_model::values_data(bindings), after.root@, history.take(count as int) + word) by {
            assert(model::regex_lang(before.store.graph(), before.symbols@, source_model::values_data(bindings), residual@, word)
                == model::regex_lang(before.store.graph(), before.symbols@, source_model::values_data(bindings), before.root@, history.take(count as int) + word));
        }
    }

    pub(super) proof fn lemma_previous_frame(before: CompiledPair, after: CompiledPair, transition: TransitionId, bindings: Seq<Value>, event: Value, residual: RegexId)
        requires pair_wf(before), pair_frame(before, after), instantiation_result(before, transition, bindings, event, residual),
            transition@ < before.store.graph().transitions.len(),
        ensures instantiation_result(after, transition, bindings, event, residual), transition@ < after.store.graph().transitions.len(),
    {
        hide(language::lang); hide(model::lift_regex); hide(model::lift_transition); hide(model::test_holds);
        model::lemma_graph_wf_elim(before.store.graph());
        model::lemma_lift_regex_stable(before.store.graph(), after.store.graph(), residual@);
        model::lemma_lift_transition_stable(before.store.graph(), after.store.graph(), transition@);
        assert forall|word: Seq<Data>| model::regex_lang(after.store.graph(), after.symbols@, source_model::values_data(bindings), residual@, word)
            == norm::transition_lang(after.store.graph(), after.symbols@, source_model::values_data(bindings), transition, crate::verify::value_specs::value_view(event), word) by {
            assert(model::regex_lang(before.store.graph(), before.symbols@, source_model::values_data(bindings), residual@, word)
                == norm::transition_lang(before.store.graph(), before.symbols@, source_model::values_data(bindings), transition, crate::verify::value_specs::value_view(event), word));
        }
    }

    pub(super) proof fn lemma_replay_step(pair: CompiledPair, history: Seq<Data>, bindings: Seq<Value>, count: nat, residual: RegexId, transition: TransitionId, event: Value, successor: RegexId)
        requires pair_wf(pair), residual_after_prefix(pair, history, bindings, count, residual), count < history.len(),
            crate::verify::value_specs::value_view(event) == history[count as int],
            symbolic::verify::derivative_correct(pair.store.graph(), residual@, transition),
            instantiation_result(pair, transition, bindings, event, successor),
        ensures residual_after_prefix(pair, history, bindings, count + 1, successor),
    {
        assert forall|word: Seq<Data>| model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), successor@, word)
            == model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), pair.root@, history.take(count as int + 1) + word) by {
            assert(history.take(count as int + 1) =~= history.take(count as int).push(history[count as int]));
            assert(history.take(count as int) + (seq![history[count as int]] + word) =~= history.take(count as int + 1) + word);
        }
    }

    pub(super) proof fn lemma_absorbing_language(pair: CompiledPair, bindings: Seq<Value>, residual: RegexId)
        requires model::graph_wf(pair.store.graph()), residual@ == pair.store.graph().constants.all || residual@ == pair.store.graph().constants.empty,
        ensures forall|word: Seq<Data>| model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), residual@, word)
            == (residual@ == pair.store.graph().constants.all),
    {
        model::lemma_graph_wf_elim(pair.store.graph());
        assert forall|word: Seq<Data>| model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), residual@, word)
            == (residual@ == pair.store.graph().constants.all) by {
            if residual@ == pair.store.graph().constants.all {
                assert(model::lift_regex(pair.store.graph(), residual@) == language::Regex::All);
            } else {
                assert(model::lift_regex(pair.store.graph(), residual@) == language::Regex::Empty);
            }
        }
    }

    pub(super) proof fn lemma_replay_absorbing(pair: CompiledPair, history: Seq<Data>, bindings: Seq<Value>, count: nat, residual: RegexId)
        requires pair_wf(pair), residual_after_prefix(pair, history, bindings, count, residual),
            residual@ == pair.store.graph().constants.all || residual@ == pair.store.graph().constants.empty,
        ensures residual_after_prefix(pair, history, bindings, history.len(), residual),
    {
        hide(language::lang); hide(model::lift_regex); hide(model::test_holds); hide(model::lift_transition);
        lemma_absorbing_language(pair, bindings, residual);
        assert forall|word: Seq<Data>| model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), residual@, word)
            == model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), pair.root@, history.take(history.len() as int) + word) by {
            let rest = history.subrange(count as int, history.len() as int) + word;
            assert(history.take(history.len() as int) =~= history);
            assert(model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), residual@, rest)
                == model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), residual@, word));
            assert(history.take(count as int) + rest =~= history + word);
            assert(model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), residual@, rest)
                == model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), pair.root@, history.take(count as int) + rest));
        }
    }

    #[cfg(feature = "cache")]
    pub(super) proof fn lemma_publication_frame(before: CompiledPair, after: CompiledPair)
        requires pair_wf(before), after.store.graph() == before.store.graph(), after.store.valid_store(),
            after.symbols@ == before.symbols@, after.pattern == before.pattern, after.root == before.root,
            after.derivatives@ == before.derivatives@, after.atoms@ == before.atoms@,
            successor_map(after) == successor_map(before), cursor_cache_wf(after),
        ensures pair_wf(after), pair_frame(before, after),
    {
        hide(language::lang); hide(model::lift_regex); hide(model::lift_transition); hide(model::test_holds);
        let head = choose|head: language::Head| source_model::pattern_represents(before.pattern, before.symbols@, head);
        assert(source_model::pattern_represents(after.pattern, after.symbols@, head));
        assert(exists|head: language::Head| source_model::pattern_represents(after.pattern, after.symbols@, head));
    }

    pub(super) proof fn lemma_full_residual_answer(pair: CompiledPair, history: Seq<Data>, bindings: Seq<Value>, residual: RegexId, answer: bool)
        requires residual_after_prefix(pair, history, bindings, history.len(), residual),
            answer == language::nullable(model::lift_regex(pair.store.graph(), residual@)),
        ensures answer == model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), pair.root@, history),
    {
        language::lemma_nullable_iff_nil(model::gsem(pair.symbols@, source_model::values_data(bindings)), model::lift_regex(pair.store.graph(), residual@));
        assert(history.take(history.len() as int) + Seq::<Data>::empty() =~= history);
        assert(model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), residual@, Seq::empty())
            == model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), pair.root@, history.take(history.len() as int) + Seq::empty()));
    }

    pub(super) proof fn lemma_pair_all_frames(before: CompiledPair)
        ensures forall|after: CompiledPair, head: language::Head, tail: language::Regex<language::SrcTest>|
            pair_represents(before, head, tail) && pair_wf(after) && pair_frame(before, after)
                ==> pair_represents(after, head, tail),
    {
        assert forall|after: CompiledPair, head: language::Head, tail: language::Regex<language::SrcTest>|
            pair_represents(before, head, tail) && pair_wf(after) && pair_frame(before, after)
                implies pair_represents(after, head, tail) by { lemma_pair_represents_frame(before, after, head, tail); }
    }

    /// lemma_bind_compile_substitutions: binding the compiled tail with the unique
    /// complete head substitution decides exactly the independent pair language.
    pub(super) proof fn lemma_bind_compile_substitutions(pair: CompiledPair, head: language::Head, tail: language::Regex<language::SrcTest>, request: Data, history: Seq<Data>, bindings: Seq<Value>, answer: bool)
        requires pair_represents(pair, head, tail), bindings.len() == pair.symbols@.variables.len(),
            language::head_match(head, request, source_model::theta_of(bindings, pair.symbols@)),
            source_model::theta_of(bindings, pair.symbols@).dom() == language::head_vars(head),
            answer == model::regex_lang(pair.store.graph(), pair.symbols@, source_model::values_data(bindings), pair.root@, history),
        ensures answer == language::pair_lang(head, tail, request, history),
    {
        source_model::lemma_theta_of(bindings, pair.symbols@);
        assert(source_model::bindings_agree(pair.symbols@, source_model::values_data(bindings), source_model::theta_of(bindings, pair.symbols@)));
        language::lemma_pair_lang_substitutions(head, tail, request, history, source_model::theta_of(bindings, pair.symbols@));
    }

    #[cfg(feature = "cache")]
    pub(super) open spec fn cursor_ready(pair: CompiledPair, cursor: Cursor, history: Seq<Data>) -> bool {
        cursor.bindings@.len() == pair.symbols@.variables.len()
            && (forall|i: int| 0 <= i < cursor.bindings@.len() ==> crate::verify::value_specs::value_view(cursor.bindings@[i]) != Data::Undefined)
            && residual_after_prefix(pair, history, cursor.bindings@, cursor.consumed_len as nat, cursor.residual)
    }

    #[cfg(feature = "cache")]
    pub(super) proof fn lemma_cursor_continuity(pair: CompiledPair, history: Seq<Data>)
        requires pair_wf(pair), pair.snapshot is Some, history_view(pair.snapshot.unwrap()).is_prefix_of(history),
        ensures forall|i: int| 0 <= i < pair.cursors@.len() ==> cursor_ready(pair, pair.cursors@[i], history),
    {
        let snapshot = history_view(pair.snapshot.unwrap());
        assert forall|i: int| 0 <= i < pair.cursors@.len() implies cursor_ready(pair, pair.cursors@[i], history) by {
            let cursor = pair.cursors@[i];
            assert(residual_after_prefix(pair, snapshot, cursor.bindings@, cursor.consumed_len as nat, cursor.residual));
            assert(cursor.bindings@.len() == pair.symbols@.variables.len());
            assert forall|j: int| 0 <= j < cursor.bindings@.len() implies crate::verify::value_specs::value_view(cursor.bindings@[j]) != Data::Undefined by {
                assert(source_model::values_data(cursor.bindings@)[j] == crate::verify::value_specs::value_view(cursor.bindings@[j]));
            }
            assert(snapshot.take(cursor.consumed_len as int) =~= history.take(cursor.consumed_len as int));
        }
    }

        }
}

#[allow(clippy::unreachable)]
#[cfg(test)]
mod cache_tests {
    use super::super::{graph::Storage as _, source::compile_pair};
    use super::*;
    use alloc::string::ToString as _;
    use serde_json::json;

    fn value(source: serde_json::Value) -> Value {
        Value::from_json_str(&source.to_string()).expect("valid event-class fixture")
    }

    fn history(source: serde_json::Value) -> crate::Rc<Array> {
        match value(source) {
            Value::Array(events) => events,
            _ => unreachable!("array fixture"),
        }
    }

    fn compile(regex: serde_json::Value) -> CompiledPair {
        let policy = value(json!({"request":{"var":"v"},"history":regex}));
        let mut world = ObservationWorld;
        compile_pair(&policy, &mut ExecutionTimer::new(None), &mut world).unwrap()
    }

    fn replay(pair: &mut CompiledPair, events: serde_json::Value, binding: i64) -> bool {
        let mut world = ObservationWorld;
        pair.replay(
            &history(events),
            &[Value::from(binding)],
            &mut ExecutionTimer::new(None),
            &mut world,
        )
        .unwrap()
    }

    #[test]
    fn unequal_metadata_and_different_bindings_share_exact_event_classes() {
        let mut pair = compile(json!({"star":{"test":{"eq":{"path":["x"],"term":{"var":"v"}}}}}));
        assert!(replay(
            &mut pair,
            json!([{"x":1,"trace":"a"},{"x":1,"trace":"b"}]),
            1
        ));
        assert_eq!(pair.work.events, 2);
        assert_eq!(pair.work.event_classes, 2);
        assert_eq!(pair.work.successor_misses, 1);
        assert_eq!(pair.work.successor_hits, 1);
        assert_eq!(pair.work.equal_event_hits, 0);
        assert_eq!(pair.work.self_loops, 2);
        assert_eq!(pair.successors.as_ref().map(LruCache::len), Some(1));

        // Equal words under another substitution are authoritative; raw Values
        // and binding identity are deliberately absent from the cache key.
        assert!(replay(&mut pair, json!([{"x":2,"trace":"c"}]), 2));
        assert_eq!(pair.work.successor_hits, 2);
        assert_eq!(pair.work.successor_misses, 1);
        // Reusing that same event with a different binding changes its words.
        assert!(!replay(&mut pair, json!([{"x":2,"trace":"c"}]), 1));
        assert_eq!(pair.work.successor_misses, 2);
        assert_eq!(pair.successors.as_ref().map(LruCache::len), Some(2));
        pair.release();
    }

    #[test]
    fn equal_event_shortcut_is_local_to_a_fixed_binding_replay() {
        let mut pair = compile(json!({"star":{"test":{"eq":{"path":["x"],"term":{"var":"v"}}}}}));
        let events = json!([{"x":1},{"x":1}]);
        assert!(replay(&mut pair, events.clone(), 1));
        assert_eq!(pair.work.events, 2);
        assert_eq!(pair.work.event_classes, 1);
        assert_eq!(pair.work.equal_event_hits, 1);
        assert!(!replay(&mut pair, events, 2));
        assert_eq!(pair.work.events, 3); // Empty is absorbing after the first event.
        assert_eq!(pair.work.event_classes, 2);
        assert_eq!(pair.work.equal_event_hits, 1);
        pair.release();
    }

    #[test]
    fn negative_tests_cache_only_positive_primitive_ids() {
        let mut pair = compile(json!({"test":{"neq":{"path":["x"],"term":{"value":1}}}}));
        assert!(replay(&mut pair, json!([{"x":2}]), 0));
        let atoms = pair
            .atoms
            .iter()
            .flatten()
            .next()
            .expect("cached primitive list");
        assert_eq!(atoms.ids().len(), 2);
        for id in atoms.ids() {
            assert!(matches!(
                pair.store.storage.test(*id).unwrap(),
                TestView::Atom { positive: true, .. }
            ));
        }
        assert!(atoms.ids().windows(2).all(|ids| ids.first() < ids.get(1)));
        assert!(!replay(&mut pair, json!([{}]), 0));
        assert!(!replay(&mut pair, json!([{"x":1}]), 0));
        assert_eq!(pair.successors.as_ref().map(LruCache::len), Some(3));
        for key in pair
            .successors
            .as_ref()
            .expect("event cache")
            .iter()
            .map(|(key, _)| key)
        {
            assert_eq!(key.words.len(), 1);
            assert_eq!(key.words.first().copied().unwrap().checked_shr(2), Some(0));
        }
        pair.release();
    }

    #[test]
    fn constants_and_absorbing_states_do_not_allocate_event_caches() {
        for (regex, events, expected, visits) in [
            (json!({"test":true}), json!([null]), true, 1),
            (json!({"all":true}), json!([null, null]), true, 0),
            (json!({"empty":true}), json!([null, null]), false, 0),
        ] {
            let mut pair = compile(regex);
            assert_eq!(replay(&mut pair, events, 0), expected);
            assert_eq!(pair.work.events, visits);
            assert!(pair.successors.is_none());
            assert!(pair.atoms.is_empty());
            pair.release();
        }
    }

    #[test]
    fn derivative_cycle_stabilizes_without_merging_distinct_residuals() {
        let mut pair = compile(json!({"star":{"concat":[
            {"test":{"eq":{"path":["x"],"term":{"value":1}}}},
            {"test":{"eq":{"path":["x"],"term":{"value":2}}}}
        ]}}));
        assert!(replay(&mut pair, json!([{"x":1},{"x":2}]), 0));
        let bytes = pair.store.bytes;
        let derivatives = pair.derivatives.len();
        let atom_rows = pair.atoms.len();
        for trace in 0..64 {
            assert!(replay(
                &mut pair,
                json!([{"x":1,"trace":trace},{"x":2,"trace":trace}]),
                0
            ));
        }
        assert_eq!(pair.store.bytes, bytes);
        assert_eq!(pair.derivatives.len(), derivatives);
        assert_eq!(pair.atoms.len(), atom_rows);
        assert_eq!(pair.successors.as_ref().map(LruCache::len), Some(2));
        assert!(!replay(&mut pair, json!([{"x":1}]), 0));
        assert!(!replay(&mut pair, json!([{"x":1},{"x":1}]), 0));
        assert!(replay(
            &mut pair,
            json!([{"x":1},{"x":2},{"x":1},{"x":2}]),
            0
        ));
        pair.release();
    }

    #[test]
    fn event_class_lru_has_a_256_entry_ceiling() {
        let tests: Vec<_> = (0..9)
            .map(|bit| json!({"eq":{"path":[bit.to_string()],"term":{"value":1}}}))
            .collect();
        let mut pair = compile(json!({"test":{"and":tests}}));
        for bits in 0_u16..=256 {
            let mut event = serde_json::Map::new();
            for bit in 0..9 {
                event.insert(
                    bit.to_string(),
                    json!(u16::from(bits & (1_u16 << bit) != 0)),
                );
            }
            assert!(!replay(&mut pair, json!([event]), 0));
        }
        assert_eq!(pair.work.successor_misses, 257);
        assert_eq!(pair.successors.as_ref().map(LruCache::len), Some(256));
        // The earliest class was evicted and must be interpreted again.
        let event: serde_json::Map<_, _> = (0..9).map(|bit| (bit.to_string(), json!(0))).collect();
        assert!(!replay(&mut pair, json!([event]), 0));
        assert_eq!(pair.work.successor_misses, 258);
        assert_eq!(pair.successors.as_ref().map(LruCache::len), Some(256));
        pair.release();
    }
}

#[allow(clippy::unreachable)]
#[cfg(all(test, feature = "cache"))]
mod progress_tests {
    use super::super::source::compile_pair;
    use super::*;
    use alloc::vec;
    use serde_json::{json, Value as Json};

    fn value(source: Json) -> Value {
        Value::from(source)
    }

    fn history(source: Json) -> Rc<Array> {
        match value(source) {
            Value::Array(events) => events,
            _ => unreachable!("array fixture"),
        }
    }

    fn compile(regex: Json) -> CompiledPair {
        let mut world = ObservationWorld;
        compile_pair(
            &value(json!({"request":{"var":"v"},"history":regex})),
            &mut ExecutionTimer::new(None),
            &mut world,
        )
        .unwrap()
    }

    fn equality() -> Json {
        json!({"test":{"eq":{"path":["x"],"term":{"var":"v"}}}})
    }

    fn star() -> CompiledPair {
        compile(json!({"star":equality()}))
    }

    fn evaluate(pair: &mut CompiledPair, events: &Rc<Array>, request: &Value) -> bool {
        let mut world = ObservationWorld;
        pair.evaluate(events, request, &mut ExecutionTimer::new(None), &mut world)
            .unwrap()
    }

    // Independent membership oracle for star(test(x == request)); this does not
    // inspect normalized nodes, derivatives, event classes or retained cursors.
    fn assert_star(pair: &mut CompiledPair, events: &Rc<Array>, request: &Value) -> bool {
        let key = Value::from("x");
        let expected = events.iter().all(|event| {
            event
                .as_object()
                .ok()
                .and_then(|object| object.get(&key))
                .is_some_and(|selected| selected == request)
        });
        let actual = evaluate(pair, events, request);
        assert_eq!(actual, expected);
        actual
    }

    fn reset_work(pair: &mut CompiledPair) {
        pair.work = WorkCounters::default();
    }

    #[test]
    fn identical_arrays_are_constant_history_work_and_extensions_fold_only_suffix() {
        let mut pair = star();
        let request = Value::from(1);
        let initial = history(json!([{"x":1,"trace":"a"},{"x":1,"trace":"b"}]));
        assert!(assert_star(&mut pair, &initial, &request));
        let residual = pair.cursors.first().unwrap().residual;
        reset_work(&mut pair);
        assert!(assert_star(&mut pair, &initial, &request));
        assert_eq!(pair.work.events, 0);
        assert_eq!(pair.work.prefix_comparisons, 0);

        let reconstructed = history(json!([{"x":1,"trace":"a"},{"x":1,"trace":"b"}]));
        assert!(!Rc::ptr_eq(&initial, &reconstructed));
        assert!(assert_star(&mut pair, &reconstructed, &request));
        assert_eq!(pair.work.events, 0);
        assert_eq!(pair.work.prefix_comparisons, 2);
        assert!(Rc::ptr_eq(pair.snapshot.as_ref().unwrap(), &reconstructed));

        let mut extended = Rc::clone(&reconstructed);
        Rc::make_mut(&mut extended).push(value(json!({"x":1,"trace":"self-loop"})));
        reset_work(&mut pair);
        assert!(assert_star(&mut pair, &extended, &request));
        assert_eq!(pair.work.events, 1);
        assert_eq!(pair.work.prefix_comparisons, 2);
        assert_eq!(pair.work.self_loops, 1);
        assert_eq!(pair.cursors.first().unwrap().residual, residual);
        assert_eq!(pair.cursors.first().unwrap().consumed_len, 3);

        let mut relevant = Rc::clone(&extended);
        Rc::make_mut(&mut relevant).push(value(json!({"x":2})));
        reset_work(&mut pair);
        assert!(!assert_star(&mut pair, &relevant, &request));
        assert_eq!(pair.work.events, 1);
        assert_eq!(pair.work.prefix_comparisons, 3);
        let mut after_empty = Rc::clone(&relevant);
        Rc::make_mut(&mut after_empty).push(value(json!({"x":1})));
        reset_work(&mut pair);
        assert!(!assert_star(&mut pair, &after_empty, &request));
        assert_eq!(pair.work.events, 0);
        assert_eq!(pair.work.prefix_comparisons, 4);
        assert_eq!(pair.cursors.first().unwrap().consumed_len, 5);
        pair.release();
    }

    #[test]
    fn replacements_truncations_and_divergent_appends_replay_from_root() {
        let mut pair = star();
        let initial = history(json!([{"x":1},{"x":1}]));
        assert!(assert_star(&mut pair, &initial, &Value::from(1)));
        assert!(!assert_star(&mut pair, &initial, &Value::from(2)));
        assert_eq!(pair.cursors.len(), 2);
        for (events, binding, expected) in [
            (json!([{"x":1},{"x":2}]), 1, false),
            (json!([{"x":1}]), 1, true),
            (json!([{"x":1},{"x":2}]), 1, false),
            (json!([{"x":2},{"x":2}]), 2, true),
            (json!([]), 2, true),
            (json!([{"x":1}]), 2, false),
        ] {
            let events = history(events);
            assert_eq!(
                assert_star(&mut pair, &events, &Value::from(binding)),
                expected
            );
            assert_eq!(pair.cursors.len(), 1);
            assert_eq!(pair.cursors.first().unwrap().consumed_len, events.len());
            assert!(Rc::ptr_eq(pair.snapshot.as_ref().unwrap(), &events));
        }
        pair.release();
    }

    #[test]
    fn one_shared_snapshot_keeps_other_binding_cursors_at_their_valid_prefixes() {
        let mut pair = compile(json!({"concat":[{"all":true},equality(),{"all":true}]}));
        let initial = history(json!([{"x":1}]));
        assert!(evaluate(&mut pair, &initial, &Value::from(1)));
        assert!(!evaluate(&mut pair, &initial, &Value::from(2)));
        assert_eq!(Rc::strong_count(&initial), 2); // Caller plus one pair snapshot.
        let extended = history(json!([{"x":1},{"x":2}]));
        reset_work(&mut pair);
        assert!(evaluate(&mut pair, &extended, &Value::from(1)));
        assert_eq!(pair.work.events, 0); // Binding 1 was already at absorbing all.
        assert_eq!(pair.work.prefix_comparisons, 1);
        assert_eq!(Rc::strong_count(&initial), 1);
        assert_eq!(Rc::strong_count(&extended), 2);
        let older = pair
            .cursors
            .iter()
            .find(|cursor| cursor.bindings == vec![Value::from(2)])
            .unwrap();
        assert_eq!(older.consumed_len, 1);
        reset_work(&mut pair);
        assert!(evaluate(&mut pair, &extended, &Value::from(2)));
        assert_eq!(pair.work.events, 1);
        assert_eq!(pair.work.prefix_comparisons, 0);
        assert_eq!(pair.cursors.first().unwrap().consumed_len, 2);
        assert_eq!(Rc::strong_count(&extended), 2);
        pair.release();
    }

    #[test]
    fn cursor_move_to_front_eviction_is_bounded_and_uses_exact_values() {
        let mut pair = star();
        let events = history(json!([{"x":1}]));
        for binding in 0..CURSOR_CAPACITY {
            assert_star(&mut pair, &events, &Value::from(binding));
        }
        assert_eq!(pair.cursors.len(), CURSOR_CAPACITY);
        assert_eq!(Rc::strong_count(&events), 2);
        reset_work(&mut pair);
        assert!(!assert_star(&mut pair, &events, &Value::from(0)));
        assert_eq!(pair.work.events, 0);
        assert!(!assert_star(
            &mut pair,
            &events,
            &Value::from(CURSOR_CAPACITY)
        ));
        assert_eq!(pair.cursors.len(), CURSOR_CAPACITY);
        assert!(!pair
            .cursors
            .iter()
            .any(|cursor| cursor.bindings == vec![Value::from(1)]));
        reset_work(&mut pair);
        assert!(assert_star(&mut pair, &events, &Value::from(1)));
        assert_eq!(pair.work.events, 1); // Binding 1 was evicted, so replay is required.
        assert!(!assert_star(&mut pair, &events, &Value::from("1")));
        assert!(pair
            .cursors
            .iter()
            .any(|cursor| cursor.bindings == vec![Value::from(1)]));
        assert!(pair
            .cursors
            .iter()
            .any(|cursor| cursor.bindings == vec![Value::from("1")]));
        assert_eq!(Rc::strong_count(&events), 2);
        pair.release();
    }

    #[test]
    fn request_mismatch_does_not_validate_or_replace_progress() {
        let policy =
            value(json!({"request":{"object":{"key":{"var":"v"}}},"history":{"star":equality()}}));
        let mut world = ObservationWorld;
        let mut pair = compile_pair(&policy, &mut ExecutionTimer::new(None), &mut world).unwrap();
        let events = history(json!([{"x":1}]));
        assert!(evaluate(&mut pair, &events, &value(json!({"key":1}))));
        let residual = pair.cursors.first().unwrap().residual;
        let divergent = history(json!([{"x":2}]));
        reset_work(&mut pair);
        assert!(!evaluate(&mut pair, &divergent, &value(json!({}))));
        assert_eq!(pair.work.events, 0);
        assert_eq!(pair.work.prefix_comparisons, 0);
        assert!(Rc::ptr_eq(pair.snapshot.as_ref().unwrap(), &events));
        assert_eq!(pair.cursors.len(), 1);
        assert_eq!(pair.cursors.first().unwrap().consumed_len, 1);
        assert_eq!(pair.cursors.first().unwrap().residual, residual);
        assert!(evaluate(&mut pair, &events, &value(json!({"key":1}))));
        assert_eq!(pair.work.events, 0);
        pair.release();
    }

    #[test]
    fn nested_cow_mutation_cannot_change_a_retained_history() {
        let mut pair = star();
        let events = history(json!([{"x":{"nested":[1]}}]));
        let request = value(json!({"nested":[1]}));
        assert!(assert_star(&mut pair, &events, &request));
        let mut caller = Value::Array(Rc::clone(&events));
        let event = caller
            .as_array_mut()
            .unwrap()
            .get_mut(0)
            .unwrap()
            .as_object_mut()
            .unwrap();
        let selected = event
            .get_mut(&Value::from("x"))
            .unwrap()
            .as_object_mut()
            .unwrap();
        let nested = selected
            .get_mut(&Value::from("nested"))
            .unwrap()
            .as_array_mut()
            .unwrap();
        *nested.get_mut(0).unwrap() = Value::from(2);
        let Value::Array(changed) = caller else {
            unreachable!("array fixture");
        };
        assert!(!Rc::ptr_eq(&events, &changed));
        assert_eq!(
            events.first(),
            history(json!([{"x":{"nested":[1]}}])).first()
        );
        reset_work(&mut pair);
        assert!(!assert_star(&mut pair, &changed, &request));
        assert_eq!(pair.work.prefix_comparisons, 1);
        assert_eq!(pair.work.events, 1);
        assert!(assert_star(
            &mut pair,
            &changed,
            &value(json!({"nested":[2]}))
        ));
        assert!(assert_star(&mut pair, &events, &request));
        pair.release();
    }

    #[test]
    fn equal_false_answers_never_keep_the_wrong_future_language() {
        let factors: Vec<_> = (1..=3)
            .map(|literal| json!({"test":{"eq":{"path":["x"],"term":{"value":literal}}}}))
            .collect();
        let mut pair = compile(json!({"concat":factors}));
        let request = Value::Null;
        assert!(!evaluate(&mut pair, &history(json!([{"x":1}])), &request));
        let first = pair.cursors.first().unwrap().residual;
        assert!(!evaluate(
            &mut pair,
            &history(json!([{"x":1},{"x":2}])),
            &request
        ));
        let second = pair.cursors.first().unwrap().residual;
        assert_ne!(first, second);
        assert!(evaluate(
            &mut pair,
            &history(json!([{"x":1},{"x":2},{"x":3}])),
            &request
        ));
        assert!(!evaluate(&mut pair, &history(json!([{"x":1}])), &request));
        assert!(!evaluate(
            &mut pair,
            &history(json!([{"x":1},{"x":3}])),
            &request
        ));
        assert!(evaluate(
            &mut pair,
            &history(json!([{"x":1},{"x":2},{"x":3}])),
            &request
        ));
        pair.release();
    }

    #[test]
    fn timeout_mid_suffix_preserves_old_snapshot_and_cursor_then_replays_the_suffix() {
        use crate::tests::interpreter::timer_test_support::{
            configure_time_source, reset_time_source,
        };
        use crate::utils::limits::{acquire_limits_test_lock, ExecutionTimerConfig, LimitError};
        use core::{num::NonZeroU32, time::Duration};

        let _guard = acquire_limits_test_lock();
        let mut world = ObservationWorld;
        configure_time_source(None);
        let mut pair = star();
        let request = Value::from(1);
        let initial = history(json!([{"x":1,"trace":0}]));
        assert!(assert_star(&mut pair, &initial, &request));
        assert!(!assert_star(&mut pair, &initial, &Value::from(2)));
        let before: Vec<_> = pair
            .cursors
            .iter()
            .map(|cursor| {
                (
                    cursor.bindings.clone(),
                    cursor.consumed_len,
                    cursor.residual,
                )
            })
            .collect();
        let extended = history(json!((0..65)
            .map(|trace| json!({"x":1,"trace":trace}))
            .collect::<Vec<_>>()));
        let divergent = history(json!(vec![json!({"x":1,"trace":"branch"}); 65]));
        for candidate in [&extended, &divergent] {
            reset_work(&mut pair);
            reset_time_source();
            let mut timer = ExecutionTimer::new(Some(ExecutionTimerConfig {
                limit: Duration::from_millis(1),
                check_interval: NonZeroU32::new(64).unwrap(),
            }));
            timer.start(world.now().expect("configured test clock"));
            assert!(matches!(
                pair.evaluate(candidate, &request, &mut timer, &mut world),
                Err(super::super::HistoryError::Limit(
                    LimitError::TimeLimitExceeded { .. }
                ))
            ));
            assert!(pair.work.events > 0 && pair.work.events < 64);
            assert!(Rc::ptr_eq(pair.snapshot.as_ref().unwrap(), &initial));
            let after: Vec<_> = pair
                .cursors
                .iter()
                .map(|cursor| {
                    (
                        cursor.bindings.clone(),
                        cursor.consumed_len,
                        cursor.residual,
                    )
                })
                .collect();
            assert_eq!(before, after);
        }
        reset_work(&mut pair);
        assert!(assert_star(&mut pair, &extended, &request));
        assert_eq!(pair.work.events, 64);
        assert_eq!(pair.work.prefix_comparisons, 1);
        assert_eq!(pair.cursors.first().unwrap().consumed_len, 65);
        assert!(Rc::ptr_eq(pair.snapshot.as_ref().unwrap(), &extended));
        assert_eq!(pair.cursors.get(1).unwrap().consumed_len, 1);
        reset_time_source();
        pair.release();
    }

    #[test]
    fn different_policy_values_keep_disjoint_progress_and_snapshots() {
        let mut state = super::super::HistoryMatchState::default();
        let mut world = ObservationWorld;
        let policies: Vec<_> = [1, 2]
            .into_iter()
            .map(|literal| {
                value(json!({
                    "request":{"any":true},
                    "history":{"star":{"test":{"eq":{"path":["x"],"term":{"value":literal}}}}}
                }))
            })
            .collect();
        let initial = history(json!([{"x":1}]));
        let first = policies.first().unwrap();
        let second = policies.get(1).unwrap();
        assert!(state
            .evaluate(
                first,
                &initial,
                &Value::Null,
                &mut ExecutionTimer::new(None),
                &mut world,
            )
            .unwrap());
        assert!(!state
            .evaluate(
                second,
                &initial,
                &Value::Null,
                &mut ExecutionTimer::new(None),
                &mut world,
            )
            .unwrap());
        assert_eq!(state.pairs.len(), 2);
        assert_eq!(Rc::strong_count(&initial), 3); // One snapshot in each distinct pair.
        let branch = history(json!([{"x":2}]));
        assert!(state
            .evaluate(
                second,
                &branch,
                &Value::Null,
                &mut ExecutionTimer::new(None),
                &mut world,
            )
            .unwrap());
        assert_eq!(Rc::strong_count(&initial), 2);
        assert_eq!(Rc::strong_count(&branch), 2);
        let retained = &mut state
            .pairs
            .iter_mut()
            .find(|entry| &entry.policy == first)
            .unwrap()
            .pair;
        reset_work(retained);
        assert!(state
            .evaluate(
                first,
                &initial,
                &Value::Null,
                &mut ExecutionTimer::new(None),
                &mut world,
            )
            .unwrap());
        let retained = &state
            .pairs
            .iter()
            .find(|entry| &entry.policy == first)
            .unwrap()
            .pair;
        assert_eq!(retained.work.events, 0);
        assert_eq!(retained.work.prefix_comparisons, 0);
        assert!(Rc::ptr_eq(retained.snapshot.as_ref().unwrap(), &initial));
    }
}
