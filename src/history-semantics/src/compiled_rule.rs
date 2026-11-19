//! Store-bound owned DSL compilation and retained numeric decisions.

use crate::runtime::RuleRuntime;
use alloc::sync::Arc;
use history_store::history::History;
#[cfg(verus_keep_ghost)]
use history_store::history::StoredHistory;
use history_store::typed::Store;
use history_syntax::Event;
use history_syntax::syntax::{Rule, RuleMode};
use junco_core::errors::{CompileError, HistoryError};
use junco_core::flat::FlatPair;
use junco_core::flatten::flatten_rule;
use junco_core::limits::{Limits, Unmetered};
use junco_core::observation::ObservationWorld;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::verify::typed_decision as decision;
#[cfg(verus_keep_ghost)]
use history_store::history::verify as raw;
#[cfg(verus_keep_ghost)]
use history_store::typed::verify as books;
#[cfg(verus_keep_ghost)]
use junco_core::spec::semantics as dsl;
#[cfg(verus_keep_ghost)]
use junco_core::verify::{
    encoding, flatten as source,
    history_specs::{no_invariant_compile_failure, no_invariant_failure},
};
#[cfg(verus_keep_ghost)]
use verify::*;

#[cfg(verus_keep_ghost)]
verus! {
broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas,
    junco_core::kernel::verify::group_kernel_views};
/// The result retains a structural witness, not an assumed language equivalence.
pub(crate) open spec fn compiled_source<E: Event>(
    rule: Rule<E>, mode: RuleMode, numeric: FlatPair<u64>,
    maps: encoding::Codebook<E::Component>, eq: encoding::Equality<E::Component>,
    domain: encoding::Domain<E::Component>,
) -> bool {
    mode == rule.mode && exists|flat: junco_core::flat::FlatRule<E::Component>|
        source::flattened::<E>(rule, flat)
            && encoding::lowering(flat.source, numeric, maps, eq)
            && encoding::constants_in_domain(flat.source, domain)
}
}

#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas,
        junco_core::kernel::verify::group_kernel_views};

    pub tracked struct ObservedHistory {
        pub(crate) snapshot: raw::Snapshot,
        pub(crate) registration: books::HistoryRegistration,
    }

    pub open(crate) spec fn source_rule<E: Event>(compiled: CompiledRule<E>) -> Rule<E> {
        compiled.source@
    }

    /// Native store owner retained by this compiled rule.
    pub open(crate) spec fn compiled_store<E: Event>(compiled: CompiledRule<E>) -> Arc<Store<E>> {
        compiled.store
    }

    /// Encoding witnesses are retained without exposing their representation.
    pub closed spec fn compiled_maps_frame<E: Event>(before: CompiledRule<E>, after: CompiledRule<E>) -> bool {
        after.maps@ == before.maps@
    }

    /// A failed decision retains the committed numeric cursor cache.
    pub closed spec fn compiled_cursor_frame<E: Event>(before: CompiledRule<E>, after: CompiledRule<E>) -> bool {
        after.runtime.cursors@ == before.runtime.cursors@
    }

    pub open(crate) spec fn observation_matches(registry: vstd::resource::Loc, key: (usize, u64),
        events: Seq<junco_core::verify::history_specs::EventView>, observation: ObservedHistory) -> bool {
        observation.registration.id() == registry && observation.registration.key() == key.0
            && observation.registration.value() == observation.snapshot.id()
            && observation.snapshot.value().revision == key.1 as nat
            && observation.snapshot.value().events == events
    }

    pub open(crate) spec fn observations_wf(registry: vstd::resource::Loc,
        snapshots: crate::runtime::verify::HistorySnapshots,
        observations: Map<(usize, u64), ObservedHistory>) -> bool {
        snapshots.dom() == observations.dom()
            && forall|key: (usize, u64)| observations.contains_key(key) ==>
                observation_matches(registry, key, snapshots[key], observations[key])
    }

    /// Publishing an exact lifecycle observation also introduces closed snapshot compatibility.
    pub(crate) proof fn lemma_observations_insert(registry: vstd::resource::Loc,
        snapshots: crate::runtime::verify::HistorySnapshots, observations: Map<(usize, u64), ObservedHistory>,
        key: (usize, u64), events: Seq<junco_core::verify::history_specs::EventView>, observation: ObservedHistory)
        requires observations_wf(registry, snapshots, observations),
            observation_matches(registry, key, events, observation),
        ensures observations_wf(registry, snapshots.insert(key, events), observations.insert(key, observation)),
            crate::runtime::verify::snapshot_compatible(snapshots.insert(key, events), key.0, key.1, events),
    {
        assert forall|k: (usize, u64)| observations.insert(key, observation).contains_key(k) implies
            observation_matches(registry, k, snapshots.insert(key, events)[k], observations.insert(key, observation)[k]) by {
            if k != key {
                assert(observations.contains_key(k));
                assert(observation_matches(registry, k, snapshots[k], observations[k]));
            }
        }
        crate::runtime::verify::lemma_snapshot_compatible_intro(snapshots.insert(key, events), key.0, key.1, events);
    }

    pub open(crate) spec fn compiled_wf<E: Event>(compiled: CompiledRule<E>) -> bool {
        books::store_wf(*compiled.store)
            && junco_core::flat::verify::structural_wf(compiled.template)
            && decision::runtime_represents(compiled.template, compiled.runtime)
            && observations_wf(books::registry_id(&compiled.store),
                compiled.runtime.snapshots@, compiled.observations@)
            && (junco_core::spec::hypotheses::event_obligations::<E>() ==> books::maps_wf::<E>(compiled.maps@)
                && books::snapshot_published::<E>(books::registry_id(&compiled.store), compiled.maps@)
                && compiled_source::<E>(compiled.source@, compiled.mode, compiled.template,
                    compiled.maps@, source::component_equality::<E>(), books::domain::<E>()))
    }

    pub open(crate) spec fn constructed<E: Event>(compiled: CompiledRule<E>, rule: Rule<E>, store: Arc<Store<E>>) -> bool {
        compiled_wf(compiled) && compiled.source@ == rule && compiled.store == store
            && compiled.runtime.cursors@ == Seq::<history_store::cache::HistoryCursor>::empty()
            && compiled.runtime.snapshots@ == Map::<(usize, u64), Seq<junco_core::verify::history_specs::EventView>>::empty()
    }

    /// Introduces decision readiness from actual rule and history constructors.
    pub proof fn lemma_constructed_decision<E: Event>(compiled: CompiledRule<E>, rule: Rule<E>,
        store: Arc<Store<E>>, history: History<E>)
        requires constructed(compiled, rule, store), raw::history_wf(history),
        ensures decision_requires(compiled, history), compiled_wf(compiled),
            source_rule(compiled) == rule, compiled_store(compiled) == store,
            books::store_wf(*store),
    {}

    pub open(crate) spec fn decision_requires<E: Event>(compiled: CompiledRule<E>, history: History<E>) -> bool {
        compiled_wf(compiled) && raw::history_wf(history)
    }

    /// Readiness is preserved when a well-formed history is paired with a retained rule.
    pub proof fn lemma_decision_requires<E: Event>(compiled: CompiledRule<E>, history: History<E>)
        requires compiled_wf(compiled), raw::history_wf(history),
        ensures decision_requires(compiled, history),
    {}

    /// Persistent observations agree with the history's body-maintained transition ledger.
    pub(crate) proof fn lemma_history_compatible(registry: vstd::resource::Loc,
        history: usize, stored: StoredHistory, snapshots: crate::runtime::verify::HistorySnapshots,
        tracked observations: &Map<(usize, u64), ObservedHistory>,
        tracked registration: &books::HistoryRegistration, tracked lifecycle: &raw::Lifecycle)
        requires observations_wf(registry, snapshots, *observations), lifecycle.wf(),
            registration.id() == registry, registration.key() == history,
            registration.value() == lifecycle.id(), lifecycle.state() == stored@,
        ensures crate::runtime::verify::snapshot_compatible(snapshots,
            history, stored.revision(), history_store::store::verify::events_view(raw::stored_events(&stored))),
    {
        history_store::history::lemma_stored_history_view(stored);
        let key = (history, stored.revision());
        if snapshots.contains_key(key) {
            assert(observations.contains_key(key));
            assert(observation_matches(registry, key, snapshots[key], observations[key]));
            let tracked observation = observations.tracked_borrow(key);
            books::registrations_agree(&observation.registration, registration);
            assert(observation.snapshot.id() == lifecycle.id());
            lifecycle.validate(&observation.snapshot);
            assert(observation.snapshot.value().revision == stored.revision() as nat);
            assert(observation.snapshot.value().events.is_prefix_of(
                history_store::store::verify::events_view(raw::stored_events(&stored))));
        }
        crate::runtime::verify::lemma_snapshot_compatible_intro(snapshots, history, stored.revision(),
            history_store::store::verify::events_view(raw::stored_events(&stored)));
    }

    pub open spec fn dsl_result<E: Event>(rule: Rule<E>, history: History<E>, candidate: E,
        result: Result<Option<bool>, HistoryError>) -> bool {
        result matches Ok(answer) ==> answer == dsl::rule_evaluation(
            rule@, candidate, raw::raw_events(history))
    }

    /// Outcome of the ordered scan: the first violated source (`least_violation` in the semantics) or none
    /// (`policy_permits`), under the event laws.
    pub open spec fn ordered_result<E: Event>(sources: Seq<Rule<E>>, history: History<E>, candidate: E,
        result: Result<Option<usize>, HistoryError>) -> bool {
        junco_core::spec::hypotheses::event_obligations::<E>() ==> match result {
            Ok(Some(index)) => dsl::least_violation(dsl::rule_views(sources), candidate, raw::raw_events(history), index as int),
            Ok(None) => dsl::policy_permits(dsl::rule_views(sources), candidate, raw::raw_events(history)),
            Err(_) => true,
        }
    }

    /// A scan that violated no source permits the candidate (`policy_permits` over the views).
    pub proof fn lemma_no_violation_permits<E: Event>(sources: Seq<Rule<E>>, candidate: E, history: Seq<E>)
        requires forall|j: int| 0 <= j < sources.len() ==> !dsl::rule_violated(sources[j]@, candidate, history),
        ensures dsl::policy_permits(dsl::rule_views(sources), candidate, history),
    {
        assert forall|i: int| 0 <= i < dsl::rule_views(sources).len() implies
            !dsl::rule_violated(dsl::rule_views(sources)[i], candidate, history) by {
            assert(dsl::rule_views(sources)[i] == sources[i]@);
        }
    }

    pub open spec fn compiled_sources<E: Event>(rules: Seq<CompiledRule<E>>) -> Seq<Rule<E>> {
        rules.map(|i: int, rule: CompiledRule<E>| source_rule(rule))
    }

    pub open(crate) spec fn compiled_table_wf<E: Event>(rules: Seq<CompiledRule<E>>, store: Arc<Store<E>>) -> bool {
        books::store_wf(*store) && forall|i: int| 0 <= i < rules.len() ==>
            compiled_wf(rules[i]) && rules[i].store == store
    }

    pub open(crate) spec fn compiled_structure_frame<E: Event>(before: CompiledRule<E>, after: CompiledRule<E>) -> bool {
        compiled_wf(after) && source_rule(after) == source_rule(before)
            && after.store == before.store && after.mode == before.mode
            && after.template == before.template
    }

    pub open(crate) spec fn compiled_table_frame<E: Event>(before: Seq<CompiledRule<E>>, after: Seq<CompiledRule<E>>) -> bool {
        before.len() == after.len() && forall|i: int| 0 <= i < before.len() ==>
            compiled_structure_frame(before[i], after[i])
    }

    pub(crate) proof fn lemma_compiled_sources_frame<E: Event>(before: Seq<CompiledRule<E>>, after: Seq<CompiledRule<E>>)
        requires compiled_table_frame(before, after),
        ensures compiled_sources(before) == compiled_sources(after),
    {
        assert(compiled_sources(before) =~= compiled_sources(after));
    }

    pub(crate) proof fn lemma_compiled_mode_frame<E: Event>(before: Seq<CompiledRule<E>>, after: Seq<CompiledRule<E>>, index: int)
        requires compiled_table_frame(before, after), 0 <= index < before.len(),
        ensures after[index].mode_spec() == before[index].mode_spec(),
    { reveal(CompiledRule::mode_spec); }

    pub proof fn lemma_compiled_source_mode<E: Event>(compiled: CompiledRule<E>, mode: RuleMode)
        requires compiled_wf(compiled), junco_core::spec::hypotheses::event_obligations::<E>(), mode == compiled.mode_spec(),
        ensures mode == source_rule(compiled).mode,
    { reveal(CompiledRule::mode_spec); }

    pub proof fn lemma_dsl_violation<E: Event>(compiled: CompiledRule<E>, history: History<E>, candidate: E,
        result: Result<Option<bool>, HistoryError>, mode: RuleMode)
        requires compiled_wf(compiled), junco_core::spec::hypotheses::event_obligations::<E>(),
            dsl_result(source_rule(compiled), history, candidate, result), mode == compiled.mode_spec(),
        ensures result matches Ok(answer) ==> dsl::rule_violated(source_rule(compiled)@, candidate, raw::raw_events(history))
            == match answer { None => false, Some(accepted) => match mode {
                RuleMode::Require => !accepted, RuleMode::Forbid => accepted,
            } },
    {
        reveal(CompiledRule::mode_spec);
    }

    pub open(crate) spec fn decision_result<E: Event>(before: CompiledRule<E>, after: CompiledRule<E>,
        history: History<E>, candidate: E, result: Result<Option<bool>, HistoryError>) -> bool {
        compiled_structure_frame(before, after) && after.maps@ == before.maps@
            && no_invariant_failure(result)
            && (result is Err ==> after.runtime.cursors@ == before.runtime.cursors@)
            && (junco_core::spec::hypotheses::event_obligations::<E>() ==> dsl_result(before.source@, history, candidate, result))
            && ((result == Err(HistoryError::WrongHistoryOwner))
                == !books::same_store_owner(before.store, raw::store_of(history)))
    }

    /// Eliminates a checked decision without revealing graphs, maps, or cursors.
    pub proof fn lemma_decision_result_facts<E: Event>(
        before: CompiledRule<E>, after: CompiledRule<E>, history: History<E>,
        candidate: E, result: Result<Option<bool>, HistoryError>)
        requires decision_result(before, after, history, candidate, result),
        ensures compiled_wf(after), compiled_structure_frame(before, after),
            source_rule(after) == source_rule(before), compiled_store(after) == compiled_store(before),
            compiled_maps_frame(before, after),
            no_invariant_failure(result),
            result is Err ==> compiled_cursor_frame(before, after),
            raw::history_wf(history) ==> decision_requires(after, history),
            (result == Err(HistoryError::WrongHistoryOwner))
                == !books::same_store_owner(compiled_store(before), raw::store_of(history)),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> dsl_result(source_rule(before), history, candidate, result),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> match result {
                Ok(answer) => answer == dsl::rule_evaluation(
                    source_rule(before)@, candidate, raw::raw_events(history)),
                Err(_) => true,
            },
    {}

    pub open(crate) spec fn numeric_result(template: FlatPair<u64>, request: history_store::store::Event,
        stored: StoredHistory, result: Result<Option<bool>, HistoryError>) -> bool {
        result matches Ok(answer) ==> match answer {
            None => crate::compile::verify::head_rejects(template, request),
            Some(accepted) => exists|bindings: junco_core::kernel::Bindings|
                crate::compile::verify::bindings_match(template, request, bindings)
                    && junco_core::verify::history_specs::event_wf(bindings@, bindings@.len())
                    && accepted == crate::compile::verify::source_regex(template, template.root as nat,
                        bindings@, history_store::store::verify::events_view(raw::stored_events(&stored))),
        }
    }

    pub(crate) proof fn lemma_typed_result<E: Event>(compiled: CompiledRule<E>, history: History<E>, candidate: E,
        request: history_store::store::Event, maps: books::ComponentMaps<E>, result: Result<Option<bool>, HistoryError>)
        requires compiled_wf(compiled), raw::history_wf(history), junco_core::spec::hypotheses::event_obligations::<E>(),
            books::maps_wf::<E>(maps), books::maps_extend::<E>(compiled.maps@, maps),
            books::maps_extend::<E>(raw::history_maps(history), maps), books::event_encoded::<E>(maps, candidate, request),
            numeric_result(compiled.template, request, *history.numeric(), result),
        ensures dsl_result(compiled.source@, history, candidate, result),
    {
        raw::lemma_history_wf(history);
        assert(raw::raw_word(history) =~= raw::raw_events(history).map(
            |i: int, event: E| history_syntax::spec::events::event_view(event)));
        let flat = choose|flat: junco_core::flat::FlatRule<E::Component>|
            source::flattened::<E>(compiled.source@, flat)
                && encoding::lowering(flat.source, compiled.template, compiled.maps@, source::component_equality::<E>())
                && encoding::constants_in_domain(flat.source, books::domain::<E>());
        assert(compiled.source@.head@.len() == history_syntax::spec::events::arity::<E>());
        assert(compiled.template.head@.len() == compiled.source@.head@.len());
        assert(history_syntax::spec::events::event_view(candidate).len() == compiled.source@.head@.len());
        let numeric_word = raw::stored_events(history.numeric()).map(|i: int, event: history_store::store::Event| books::numeric_values(event));
        assert forall|i: int| 0 <= i < raw::raw_events(history).len() implies
            books::event_encoded::<E>(maps, raw::raw_events(history)[i], raw::stored_events(history.numeric())[i]) by {
            books::lemma_event_extension::<E>(raw::history_maps(history), maps, raw::raw_events(history)[i], raw::stored_events(history.numeric())[i]);
        }
        assert forall|i: int| 0 <= i < numeric_word.len() implies
            numeric_word[i].len() == books::numeric_values(request).len() by {
            assert(books::event_encoded::<E>(maps, raw::raw_events(history)[i],
                raw::stored_events(history.numeric())[i]));
        }
        assert(encoding::word_encoded(maps, source::component_equality::<E>(), books::domain::<E>(),
            raw::raw_word(history), numeric_word));
        assert(junco_core::verify::encoding::word_representation(numeric_word,
            history_store::store::verify::events_view(raw::stored_events(history.numeric()))));
        encoding::lemma_dsl_later_maps_preservation::<E>(compiled.source@, flat, compiled.template,
            compiled.maps@, maps, books::domain::<E>(), history_syntax::spec::events::event_view(candidate), raw::raw_word(history),
            books::numeric_values(request), numeric_word);
        crate::compile::verify::lemma_flat_head(compiled.template, books::numeric_values(request), request@);
        if let Ok(answer) = result {
            match answer {
                None => crate::compile::verify::lemma_head_rejects(compiled.template, request),
                Some(accepted) => {
                    let bindings = choose|bindings: junco_core::kernel::Bindings|
                        crate::compile::verify::bindings_match(compiled.template, request, bindings)
                            && junco_core::verify::history_specs::event_wf(bindings@, bindings@.len())
                            && accepted == crate::compile::verify::source_regex(compiled.template,
                                compiled.template.root as nat, bindings@,
                                history_store::store::verify::events_view(raw::stored_events(history.numeric())));
                    crate::compile::verify::lemma_bindings_match(compiled.template, request, bindings);
                    crate::compile::verify::lemma_flat_regex(compiled.template, compiled.template.root as nat,
                        books::numeric_values(request), request@, numeric_word,
                        history_store::store::verify::events_view(raw::stored_events(history.numeric())), bindings@);
                },
            }
        }
    }
    }
}

verus! {
pub(crate) type LoweredRule<E> = (RuleMode, FlatPair<u64>, Ghost<history_store::typed::ComponentMaps<E>>);

impl<E: Event> CompiledRule<E> {
    /// Flatten before locking; publish one finite snapshot after encoding constants.
    fn lower<L: Limits>(
        store: &Store<E>, rule: &Rule<E>, limits: &mut L, world: &mut ObservationWorld,
    ) -> (result: Result<LoweredRule<E>, CompileError>)
        requires books::store_wf(*store),
        ensures result matches Ok((mode, numeric, maps)) ==> mode == rule.mode
            && junco_core::flat::verify::structural_wf(numeric)
            && books::snapshot_published::<E>(books::registry_id(store), maps@)
            && (junco_core::spec::hypotheses::event_obligations::<E>() ==> books::maps_wf::<E>(maps@)
                && compiled_source::<E>(*rule, mode, numeric, maps@,
                    source::component_equality::<E>(), books::domain::<E>())),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_compile_failure(result),
            junco_core::spec::hypotheses::event_obligations::<E>() && dsl::head_scoped(rule.head@)
                && dsl::regex_scoped(rule.tail@, rule.head@)
                ==> !(result matches Err(CompileError::VariableComponentConflict { .. }))
                    && !(result matches Err(CompileError::UnboundVariable { .. }))
                    && !(result matches Err(CompileError::Runtime(HistoryError::InvalidPolicy { .. }))),
            junco_core::spec::hypotheses::event_obligations::<E>() && dsl::rule_wf(rule@)
                && rule@.head.len() == history_syntax::spec::events::arity::<E>()
                && dsl::rule_constants_tagged::<E>(rule@)
                ==> (result is Ok || (result matches Err(CompileError::Runtime(error)) && dsl::resource_error(error))),
    {
        let flat = flatten_rule(rule, limits, world)?;
        proof_decl! { let ghost flattened = flat; }
        proof! {
            books::lemma_empty_snapshot::<E>(store);
            if junco_core::spec::hypotheses::event_obligations::<E>() {
                books::lemma_native_obligations_projection::<E>();
                books::lemma_empty_maps_wf::<E>();
                assert(encoding::constants_in_domain(flat.source, books::domain::<E>()));
            }
        }
        let (result, maps) = store.lower_with_snapshot(&flat.source, limits, world,
            verus_exec_expr! { Ghost(books::empty_maps::<E>()) });
        let numeric = result?;
        proof! {
            if junco_core::spec::hypotheses::event_obligations::<E>() {
                assert(source::flattened::<E>(*rule, flattened));
                assert(compiled_source::<E>(*rule, flat.mode, numeric, maps@,
                    source::component_equality::<E>(), books::domain::<E>()));
            }
        }
        Ok((flat.mode, numeric, maps))
    }
}
}

/// A rule owns one graph generation; all histories and constants share its store.
#[verus_verify]
pub struct CompiledRule<E: Event> {
    pub(crate) template: FlatPair<u64>,
    pub(crate) mode: RuleMode,
    pub(crate) store: Arc<Store<E>>,
    pub(crate) runtime: RuleRuntime,
    #[cfg(verus_keep_ghost)]
    pub(crate) source: Ghost<Rule<E>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) maps: Ghost<books::ComponentMaps<E>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) observations: Tracked<Map<(usize, u64), ObservedHistory>>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<E: Event> CompiledRule<E> {
    pub closed spec fn mode_spec(&self) -> RuleMode { self.mode }
}
}

#[verus_verify]
impl<E: Event> CompiledRule<E> {
    // Pointer comparison relates native identity to contents, never registry equality to identity.
    #[doc(hidden)]
    #[verus_verify]
    #[verus_verify(external_body)]
    #[verus_spec(result => ensures
        result == (junco_core::verify::history_assumptions::arc_identity(*left)
            == junco_core::verify::history_assumptions::arc_identity(*right)),
        result == books::same_store_owner(*left, *right),
        result ==> *left == *right && **left == **right)]
    pub fn same_owner(left: &Arc<Store<E>>, right: &Arc<Store<E>>) -> bool {
        Arc::ptr_eq(left, right)
    }

    /// Consume the source on every outcome using its iterative disposal path.
    /// Native event laws exclude internal failures; scoped sources also exclude scope/validation diagnostics.
    #[verus_spec(result => requires books::store_wf(*store),
        ensures result matches Ok(compiled) ==> constructed(compiled, rule, store),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_compile_failure(result),
            junco_core::spec::hypotheses::event_obligations::<E>() && dsl::head_scoped(rule.head@)
                && dsl::regex_scoped(rule.tail@, rule.head@)
                ==> !(result matches Err(CompileError::VariableComponentConflict { .. }))
                    && !(result matches Err(CompileError::UnboundVariable { .. }))
                    && !(result matches Err(CompileError::Runtime(HistoryError::InvalidPolicy { .. }))),
            junco_core::spec::hypotheses::event_obligations::<E>() && dsl::rule_wf(rule@)
                && rule@.head.len() == history_syntax::spec::events::arity::<E>()
                && dsl::rule_constants_tagged::<E>(rule@)
                ==> (result is Ok || (result matches Err(CompileError::Runtime(error)) && dsl::resource_error(error))))]
    pub fn new(store: Arc<Store<E>>, rule: Rule<E>) -> Result<Self, CompileError> {
        Self::new_with_limits(store, rule, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result => requires books::store_wf(*store),
        ensures result matches Ok(compiled) ==> constructed(compiled, rule, store),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_compile_failure(result),
            junco_core::spec::hypotheses::event_obligations::<E>() && dsl::head_scoped(rule.head@)
                && dsl::regex_scoped(rule.tail@, rule.head@)
                ==> !(result matches Err(CompileError::VariableComponentConflict { .. }))
                    && !(result matches Err(CompileError::UnboundVariable { .. }))
                    && !(result matches Err(CompileError::Runtime(HistoryError::InvalidPolicy { .. }))),
            junco_core::spec::hypotheses::event_obligations::<E>() && dsl::rule_wf(rule@)
                && rule@.head.len() == history_syntax::spec::events::arity::<E>()
                && dsl::rule_constants_tagged::<E>(rule@)
                ==> (result is Ok || (result matches Err(CompileError::Runtime(error)) && dsl::resource_error(error))))]
    pub(crate) fn new_with_limits<L: Limits>(
        store: Arc<Store<E>>,
        rule: Rule<E>,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Self, CompileError> {
        Self::construct(store, rule, cfg!(feature = "cache"), limits, world)
    }

    #[verus_spec(result => requires books::store_wf(*store),
        ensures result matches Ok(compiled) ==> constructed(compiled, rule, store),
            junco_core::spec::hypotheses::event_obligations::<E>() ==> no_invariant_compile_failure(result),
            junco_core::spec::hypotheses::event_obligations::<E>() && dsl::head_scoped(rule.head@)
                && dsl::regex_scoped(rule.tail@, rule.head@)
                ==> !(result matches Err(CompileError::VariableComponentConflict { .. }))
                    && !(result matches Err(CompileError::UnboundVariable { .. }))
                    && !(result matches Err(CompileError::Runtime(HistoryError::InvalidPolicy { .. }))),
            junco_core::spec::hypotheses::event_obligations::<E>() && dsl::rule_wf(rule@)
                && rule@.head.len() == history_syntax::spec::events::arity::<E>()
                && dsl::rule_constants_tagged::<E>(rule@)
                ==> (result is Ok || (result matches Err(CompileError::Runtime(error)) && dsl::resource_error(error))))]
    fn construct<L: Limits>(
        store: Arc<Store<E>>,
        rule: Rule<E>,
        precompile: bool,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Self, CompileError> {
        proof_decl! { let ghost source = rule; }
        // No `?` may bypass disposal of the caller's recursive owned source.
        let owner = history_store::typed::borrow_store(&store);
        let lowered = Self::lower(owner, &rule, limits, world);
        rule.dispose();
        let (mode, template, _maps) = lowered?;
        let runtime =
            RuleRuntime::new(store.numeric_store(), &template, precompile, limits, world)?;
        proof_decl! { let tracked observations = Map::<(usize, u64), ObservedHistory>::tracked_empty(); }
        Ok(Self {
            template,
            mode,
            store,
            runtime,
            #[cfg(verus_keep_ghost)]
            source: verus_exec_expr! { Ghost(source) },
            #[cfg(verus_keep_ghost)]
            maps: _maps,
            #[cfg(verus_keep_ghost)]
            observations: verus_exec_expr! { Tracked(observations) },
        })
    }

    #[verus_spec(result => ensures result == self.mode_spec())]
    pub const fn mode(&self) -> RuleMode {
        proof! { reveal(CompiledRule::mode_spec); }
        self.mode
    }

    /// `None` is only a head mismatch; operational errors never become verdicts.
    /// Foreign native store owners yield `WrongHistoryOwner`; matching owners never do.
    /// Readiness excludes internal invariant failures on both matching and foreign-owner paths.
    #[verus_spec(result => requires decision_requires(*old(self), *history),
        ensures decision_result(*old(self), *final(self), *history, *candidate, result),
            no_invariant_failure(result),
            junco_core::spec::hypotheses::event_obligations::<E>()
                && compiled_store(*old(self)) == raw::store_of(*history)
                ==> (result matches Err(error) ==> dsl::resource_error(error)))]
    pub fn accepts_history(
        &mut self,
        history: &History<E>,
        candidate: &E,
    ) -> Result<Option<bool>, HistoryError> {
        self.accepts_history_with_limits(history, candidate, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result => requires decision_requires(*old(self), *history),
        ensures decision_result(*old(self), *final(self), *history, *candidate, result),
            no_invariant_failure(result),
            junco_core::spec::hypotheses::event_obligations::<E>()
                && compiled_store(*old(self)) == raw::store_of(*history)
                ==> (result matches Err(error) ==> dsl::resource_error(error)))]
    pub(crate) fn accepts_history_with_limits<L: Limits>(
        &mut self,
        history: &History<E>,
        candidate: &E,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<bool>, HistoryError> {
        proof_decl! { let ghost entry = *self; }
        // Check before projections, codebook publication, or any residual lookup.
        if !Self::same_owner(&self.store, history.store()) {
            return Err(HistoryError::WrongHistoryOwner);
        }
        proof! {
            raw::lemma_history_wf(*history);
            assert(history.id() == history.numeric().id());
            history_store::history::lemma_stored_history_view(*history.numeric());
            let ghost registry = books::registry_id(&self.store);
            lemma_history_compatible(registry, history.id(), *history.numeric(),
                self.runtime.snapshots@, self.observations.borrow(), history.registration_ref(), history.lifecycle_ref());
            let key = (history.id(), history.numeric().revision());
            let events = history_store::store::verify::events_view(raw::stored_events(history.numeric()));
            crate::runtime::verify::lemma_cursor_cache_observe(self.runtime.pair,
                self.runtime.cursors@, self.runtime.snapshots@, history.id(), history.numeric().revision(), events);
            let tracked observation = ObservedHistory {
                snapshot: history.lifecycle_ref().observe(),
                registration: history.registration_ref().duplicate(),
            };
            lemma_observations_insert(registry, self.runtime.snapshots@, self.observations@, key, events, observation);
            self.observations.borrow_mut().tracked_insert(key, observation);
            *self.runtime.snapshots = self.runtime.snapshots@.insert(key, events);
            assert(compiled_wf(*self));
        }
        let owner = history_store::typed::borrow_store(&self.store);
        let (encoded, _maps) = owner.encode_event_with_snapshot(
            candidate,
            verus_exec_expr! { Ghost(self.maps@) },
            verus_exec_expr! { Ghost(raw::history_maps(*history)) },
        );
        let request = encoded?;
        proof_decl! { let ghost observed = self.runtime.snapshots@; }
        let first =
            self.runtime
                .accepts(&self.template, &request, history.numeric(), limits, world);
        proof! {
            let key = (history.id(), history.numeric().revision());
            let events = history_store::store::verify::events_view(raw::stored_events(history.numeric()));
            assert(observed.insert(key, events) =~= observed);
            assert(self.runtime.snapshots@ == observed);
            assert(compiled_wf(*self));
        }
        let result = match first {
            Err(HistoryError::GraphBudget { .. } | HistoryError::GraphIndex) => {
                // A failed replacement must not discard the old committed cursor cache.
                let mut replacement = RuleRuntime::new(
                    self.store.numeric_store(),
                    &self.template,
                    cfg!(feature = "cache"),
                    limits,
                    world,
                )?;
                proof_decl! { let tracked mut replacement_observations = Map::<(usize, u64), ObservedHistory>::tracked_empty(); }
                proof! {
                    history_store::history::lemma_stored_history_view(*history.numeric());
                    let tracked observation = ObservedHistory {
                        snapshot: history.lifecycle_ref().observe(),
                        registration: history.registration_ref().duplicate(),
                    };
                    let key = (history.id(), history.numeric().revision());
                    let events = history_store::store::verify::events_view(raw::stored_events(history.numeric()));
                    lemma_observations_insert(books::registry_id(&self.store), replacement.snapshots@,
                        replacement_observations, key, events, observation);
                    replacement_observations.tracked_insert(key, observation);
                    *replacement.snapshots = replacement.snapshots@.insert(key, events);
                    assert(decision::runtime_represents(self.template, replacement));
                }
                proof_decl! { let ghost new_snapshots = replacement.snapshots@; }
                let answer = replacement.accepts(
                    &self.template,
                    &request,
                    history.numeric(),
                    limits,
                    world,
                )?;
                proof! {
                    let key = (history.id(), history.numeric().revision());
                    let events = history_store::store::verify::events_view(raw::stored_events(history.numeric()));
                    assert(new_snapshots.insert(key, events) =~= new_snapshots);
                    assert(replacement.snapshots@ == new_snapshots);
                    assert(observations_wf(books::registry_id(&self.store),
                        replacement.snapshots@, replacement_observations));
                }
                self.runtime = replacement;
                proof! {
                    *self.observations = replacement_observations;
                    assert(compiled_wf(*self));
                }
                Ok(answer)
            }
            other => other,
        };
        proof! {
            if junco_core::spec::hypotheses::event_obligations::<E>() {
                lemma_typed_result(entry, *history, *candidate, request, _maps@, result);
            }
        }
        result
    }
}

#[cfg(any(test, feature = "test-util"))]
impl<E: Event> CompiledRule<E> {
    /// Construct the same runtime without optional precompilation for work probes.
    pub fn new_lazy(store: Arc<Store<E>>, rule: Rule<E>) -> Result<Self, CompileError> {
        Self::construct(store, rule, false, &mut Unmetered, &mut ObservationWorld)
    }

    pub fn work_counters(&self) -> &crate::runtime::WorkCounters {
        self.runtime.work_counters()
    }

    pub fn work_events(&self) -> usize {
        self.runtime.work_events()
    }

    pub fn reset_work_events(&mut self) {
        self.runtime.reset_work_events();
    }

    pub fn cursor_positions(
        &self,
    ) -> alloc::vec::Vec<(usize, junco_core::kernel::Bindings, u64, usize)> {
        self.runtime.cursor_positions()
    }

    pub fn replace_graph_byte_pressure(&mut self, bytes: usize) -> usize {
        self.runtime.replace_graph_byte_pressure(bytes)
    }

    pub fn set_answer_checkpoint_failure(&mut self, fail: bool) {
        self.runtime.set_answer_checkpoint_failure(fail);
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;
    use history_syntax::syntax::{
        AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, TestExpr,
    };
    use history_syntax::{Component3, N3};
    use junco_core::limits::LimitError;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Probe(u8, u8, u8);

    impl Event for Probe {
        type Component = Component3<u8, u8, u8>;
        type Arity = N3;
        fn component(self, index: usize) -> Self::Component {
            match index {
                0 => Component3::C0(self.0),
                1 => Component3::C1(self.1),
                _ => Component3::C2(self.2),
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

    fn head() -> Head<Probe> {
        Head::new([
            ComponentPattern::variable("actor"),
            ComponentPattern::constant(Component3::C1(2)),
            ComponentPattern::variable("resource"),
        ])
    }

    fn reads() -> Rule<Probe> {
        Rule::new(
            RuleMode::Require,
            head(),
            RegexExpr::star(RegexExpr::test(TestExpr::atom(
                Comparison::Eq,
                AtomPattern::new(Component(1), ComponentPattern::constant(Component3::C1(1))),
            ))),
        )
    }

    #[test]
    fn consuming_constructor_disposes_deep_success_and_unbound_failure() {
        let store = Arc::new(Store::new().unwrap());
        let mut valid = RegexExpr::epsilon();
        let mut invalid = RegexExpr::test(TestExpr::atom(
            Comparison::Eq,
            AtomPattern::new(Component(0), ComponentPattern::variable("missing")),
        ));
        for _ in 0..4096 {
            valid = RegexExpr::star(valid);
            invalid = RegexExpr::star(invalid);
        }
        let mut compiled = CompiledRule::new(
            Arc::clone(&store),
            Rule::new(RuleMode::Require, head(), valid),
        )
        .unwrap();
        let history = History::new(Arc::clone(&store)).unwrap();
        assert_eq!(
            compiled.accepts_history(&history, &Probe(1, 2, 1)),
            Ok(Some(true))
        );
        assert!(matches!(CompiledRule::new(store,
            Rule::new(RuleMode::Require, head(), invalid)),
            Err(CompileError::UnboundVariable { name }) if name == "missing"));
    }

    struct FailPublication;
    impl Limits for FailPublication {
        fn checkpoint(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
            Err(LimitError::MemoryLimitExceeded { usage: 2, limit: 1 })
        }
        fn enforce_memory(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
    }

    #[test]
    fn answer_and_publication_errors_preserve_committed_cursors_and_history() {
        let store = Arc::new(Store::new().unwrap());
        let mut history = History::from_events(Arc::clone(&store), [Probe(1, 1, 1)]).unwrap();
        let mut compiled = CompiledRule::new_lazy(store, reads()).unwrap();
        let candidate = Probe(1, 2, 1);
        assert_eq!(
            compiled.accepts_history(&history, &candidate),
            Ok(Some(true))
        );
        let prior = compiled.cursor_positions();
        history.push(Probe(1, 1, 1)).unwrap();
        let revision = history.numeric().revision();
        let raw = history.as_slice().to_vec();
        let numeric = history.numeric().as_slice().to_vec();

        compiled.set_answer_checkpoint_failure(true);
        assert!(matches!(
            compiled.accepts_history(&history, &candidate),
            Err(HistoryError::Limit(_))
        ));
        compiled.set_answer_checkpoint_failure(false);
        assert_eq!(compiled.cursor_positions(), prior);
        assert!(matches!(
            compiled.accepts_history_with_limits(
                &history,
                &candidate,
                &mut FailPublication,
                &mut ObservationWorld
            ),
            Err(HistoryError::Limit(_))
        ));
        assert_eq!(compiled.cursor_positions(), prior);
        assert_eq!(history.as_slice(), raw);
        assert_eq!(history.numeric().as_slice(), numeric);
        assert_eq!(history.numeric().revision(), revision);
        assert_eq!(
            compiled.accepts_history(&history, &candidate),
            Ok(Some(true))
        );
    }

    #[test]
    fn failed_graph_replacement_keeps_old_generation_cache() {
        let store = Arc::new(Store::new().unwrap());
        let mut history = History::from_events(Arc::clone(&store), [Probe(1, 1, 1)]).unwrap();
        let read = || {
            RegexExpr::test(TestExpr::atom(
                Comparison::Eq,
                AtomPattern::new(Component(1), ComponentPattern::constant(Component3::C1(1))),
            ))
        };
        let rule = Rule::new(
            RuleMode::Require,
            head(),
            RegexExpr::concat([read(), RegexExpr::star(read())]),
        );
        let mut compiled = CompiledRule::new_lazy(store, rule).unwrap();
        let candidate = Probe(1, 2, 1);
        assert_eq!(
            compiled.accepts_history(&history, &candidate),
            Ok(Some(true))
        );
        let prior = compiled.cursor_positions();
        history.push(Probe(1, 1, 1)).unwrap();
        let pressure =
            compiled.replace_graph_byte_pressure(junco_core::limits::MAX_GRAPH_BYTES + 1);
        let request = compiled
            .store
            .encode_event_with_snapshot(&candidate, Ghost::assume_new(), Ghost::assume_new())
            .0
            .unwrap();
        assert!(matches!(
            compiled.runtime.accepts(
                &compiled.template,
                &request,
                history.numeric(),
                &mut Unmetered,
                &mut ObservationWorld
            ),
            Err(HistoryError::GraphBudget { .. })
        ));
        assert!(matches!(
            compiled.accepts_history_with_limits(
                &history,
                &candidate,
                &mut FailPublication,
                &mut ObservationWorld
            ),
            Err(HistoryError::Limit(_))
        ));
        assert_eq!(compiled.cursor_positions(), prior);
        assert_eq!(
            compiled.replace_graph_byte_pressure(pressure),
            junco_core::limits::MAX_GRAPH_BYTES + 1
        );
        compiled.replace_graph_byte_pressure(junco_core::limits::MAX_GRAPH_BYTES + 1);
        assert_eq!(
            compiled.accepts_history(&history, &candidate),
            Ok(Some(true))
        );
        assert_eq!(compiled.work_events(), 2);
        compiled.reset_work_events();
        assert_eq!(
            compiled.accepts_history(&history, &candidate),
            Ok(Some(true))
        );
        assert_eq!(compiled.work_events(), 0);
    }

    #[test]
    fn candidate_allocation_failure_keeps_prior_cursors_and_history() {
        let store = Arc::new(Store::new().unwrap());
        let history = History::from_events(Arc::clone(&store), [Probe(1, 1, 1)]).unwrap();
        let mut compiled = CompiledRule::new(store, reads()).unwrap();
        assert_eq!(
            compiled.accepts_history(&history, &Probe(1, 2, 1)),
            Ok(Some(true))
        );
        let prior = compiled.cursor_positions();
        let failure = junco_core::observation::fail_reservations_after(0);
        assert_eq!(
            compiled.accepts_history(&history, &Probe(2, 2, 1)),
            Err(HistoryError::AllocationFailed)
        );
        drop(failure);
        assert_eq!(compiled.cursor_positions(), prior);
        assert_eq!(history.as_slice(), [Probe(1, 1, 1)]);
        assert_eq!(history.numeric().len(), 1);
        assert_eq!(history.numeric().revision(), 0);
        assert_eq!(
            compiled.accepts_history(&history, &Probe(2, 2, 1)),
            Ok(Some(true))
        );
    }

    #[test]
    fn foreign_owner_is_rejected_before_even_head_mismatch_projections() {
        use core::sync::atomic::{AtomicUsize, Ordering};
        static PROJECTIONS: AtomicUsize = AtomicUsize::new(0);
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        struct Counted(Probe);
        impl Event for Counted {
            type Component = <Probe as Event>::Component;
            type Arity = N3;
            fn component(self, index: usize) -> Self::Component {
                PROJECTIONS.fetch_add(1, Ordering::SeqCst);
                self.0.component(index)
            }
            fn coordinate(component: Self::Component) -> usize {
                Probe::coordinate(component)
            }
        }
        let store = Arc::new(Store::new().unwrap());
        let foreign = Arc::new(Store::new().unwrap());
        let rule = Rule::<Counted>::new(
            RuleMode::Require,
            Head::new([
                ComponentPattern::variable("actor"),
                ComponentPattern::constant(Component3::C1(2)),
                ComponentPattern::variable("resource"),
            ]),
            RegexExpr::epsilon(),
        );
        let mut compiled = CompiledRule::new(store, rule).unwrap();
        let history = History::new(foreign).unwrap();
        assert_eq!(
            compiled.accepts_history(&history, &Counted(Probe(1, 3, 1))),
            Err(HistoryError::WrongHistoryOwner)
        );
        assert_eq!(PROJECTIONS.load(Ordering::SeqCst), 0);
        assert!(compiled.cursor_positions().is_empty());
    }

    #[test]
    fn four_coordinate_decisions_bind_and_retain_the_whole_candidate() {
        use history_syntax::Component4;
        type Four = (u8, u8, u8, u8);

        let variable = |index, name| {
            TestExpr::<Four>::atom(
                Comparison::Eq,
                AtomPattern::new(Component(index), ComponentPattern::variable(name)),
            )
        };
        let rule = Rule::<Four>::new(
            RuleMode::Require,
            Head::new([
                ComponentPattern::variable("principal"),
                ComponentPattern::variable("handle"),
                ComponentPattern::constant(Component4::C2(3)),
                ComponentPattern::variable("label"),
            ]),
            RegexExpr::star(RegexExpr::test(TestExpr::and([
                variable(0, "principal"),
                variable(1, "handle"),
                TestExpr::atom(
                    Comparison::Eq,
                    AtomPattern::new(Component(2), ComponentPattern::constant(Component4::C2(1))),
                ),
                variable(3, "label"),
            ]))),
        );
        let store = Arc::new(Store::<Four>::new().unwrap());
        let mut history = History::from_events(Arc::clone(&store), [(7, 11, 1, 9); 2]).unwrap();
        let mut compiled = CompiledRule::new(store, rule).unwrap();
        let matching = (7, 11, 3, 9);
        assert_eq!(
            compiled.accepts_history(&history, &matching),
            Ok(Some(true))
        );
        for different in [(8, 11, 3, 9), (7, 12, 3, 9), (7, 11, 3, 8)] {
            assert_eq!(
                compiled.accepts_history(&history, &different),
                Ok(Some(false))
            );
        }
        assert_eq!(compiled.accepts_history(&history, &(7, 11, 4, 9)), Ok(None));
        history.push((7, 11, 1, 8)).unwrap();
        assert_eq!(
            compiled.accepts_history(&history, &matching),
            Ok(Some(false))
        );
        history.truncate(2).unwrap();
        assert_eq!(
            compiled.accepts_history(&history, &matching),
            Ok(Some(true))
        );
    }
}
