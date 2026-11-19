//! Ordered authorization and append-on-grant request handling.
//!
//! Checked ordered selection composes the rule evaluator with atomic history transactions.
//! Numeric residual caches retain their existing native boundary.

use alloc::{borrow::ToOwned, string::String, sync::Arc, vec::Vec};

use crate::compiled_rule::CompiledRule;
#[cfg(verus_keep_ghost)]
use crate::spec::monitor::{ValidatorView, check_frame, check_step, permits_result, rollback_step};
#[cfg(verus_keep_ghost)]
use history_store::history::verify as raw;
use history_store::history::{Checkpoint, History};
use history_store::typed::Store;
use history_syntax::Event;
#[cfg(verus_keep_ghost)]
use history_syntax::event::specs::EventSpec;
#[cfg(verus_keep_ghost)]
use history_syntax::spec::events::RuleView;
use history_syntax::syntax::{Rule, RuleMode};
use junco_core::errors::{CompileError, HistoryError};
use junco_core::event::{Grant, Request};
use junco_core::limits::{Limits, Unmetered};
use junco_core::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use junco_core::spec::hypotheses::event_obligations;
#[cfg(verus_keep_ghost)]
use junco_core::spec::semantics as sem;
#[cfg(verus_keep_ghost)]
use junco_core::verify::history_specs::{no_invariant_compile_failure, no_invariant_failure};
use vstd::prelude::*;

/// Diagnostic returned when the first matching rule is violated.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Denial<E: Event> {
    /// Zero-based source-order index of the first violated rule.
    pub index: usize,
    /// Whether the violated rule required or forbade its tail language.
    pub mode: RuleMode,
    /// Candidate event that was denied and was not appended to history.
    pub event: E,
    /// Human-readable explanation of the failed history relation.
    pub message: String,
}

/// Result of checking one capability request.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision<E: Event, M> {
    /// Request was accepted and appended to committed history.
    Grant(Grant<E, M>),
    /// Request was rejected atomically; committed history is unchanged.
    Denied(Denial<E>),
}

#[verus_verify]
impl<E: Event, M> Decision<E, M> {
    /// Returns `true` exactly for [`Decision::Grant`].
    #[verus_spec(result => ensures result == (self is Grant))]
    pub fn is_grant(&self) -> bool {
        matches!(self, Self::Grant(_))
    }
}

/// Compiles an ordered rule set sharing one typed store.
#[verus_verify]
pub struct ValidatorBuilder<E: Event> {
    pub(crate) store: Arc<Store<E>>,
    pub(crate) rules: Vec<CompiledRule<E>>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<E: Event> ValidatorBuilder<E> {
    /// Opaque well-formedness: every compiled rule lives in the builder's store.
    pub closed spec fn wf(&self) -> bool { verify::builder_wf(*self) }
    /// Views of the rules passed to `add_rule`, in order.
    pub closed spec fn rules(&self) -> Seq<RuleView<E::Component>> {
        sem::rule_views(verify::builder_sources(*self))
    }
}

impl<E: Event> View for Validator<E> {
    type V = ValidatorView<E>;
    /// Monitor-specification view: the rules passed to `add_rule`, in order, and the committed history.
    closed spec fn view(&self) -> ValidatorView<E> {
        ValidatorView {
            rules: sem::rule_views(verify::validator_sources(*self)),
            history: raw::raw_events(self.history),
        }
    }
}

impl<E: Event> Validator<E> {
    /// Opaque well-formedness: committed history and compiled table share one store.
    pub closed spec fn wf(&self) -> bool { verify::validator_wf(*self) }
}
}

#[verus_verify]
impl<E: Event> ValidatorBuilder<E> {
    /// Creates an empty builder in `store`.
    #[verus_spec(result => requires history_store::typed::verify::store_wf(*store),
        ensures result.wf(), result.rules() == Seq::<RuleView<E::Component>>::empty())]
    pub fn new(store: Arc<Store<E>>) -> Self {
        let builder = Self {
            store,
            rules: Vec::new(),
        };
        proof! { assert(builder.rules() =~= Seq::<RuleView<E::Component>>::empty()); }
        builder
    }

    /// Compiles and appends one complete source rule.
    /// Under the event laws, a well-formed, correctly tagged rule of the event arity has only resource-error exits.
    #[verus_spec(result => requires old(self).wf(),
        ensures event_obligations::<E>() ==> no_invariant_compile_failure(result),
            event_obligations::<E>() && sem::rule_wf(source@)
                && source@.head.len() == history_syntax::spec::events::arity::<E>()
                && sem::rule_constants_tagged::<E>(source@)
                ==> (result is Ok || (result matches Err(CompileError::Runtime(error)) && sem::resource_error(error))),
            match result {
            Err(_) => final(self).wf() && final(self).rules() == old(self).rules(),
            Ok(borrow) => mut_ref_current(borrow).wf()
                && mut_ref_current(borrow).rules() == old(self).rules().push(source@)
                && (event_obligations::<E>() ==> junco_core::spec::semantics::rule_wf(source@)
                    && source@.head.len() == history_syntax::spec::events::arity::<E>()
                    && junco_core::verify::flatten::head_coordinates_wf::<E>(source@.head))
                && mut_ref_future(borrow) == *final(self),
        })]
    pub fn add_rule(&mut self, source: Rule<E>) -> Result<&mut Self, CompileError> {
        proof_decl! { let ghost before = *self; let ghost supplied = source; }
        if ObservationWorld
            .try_reserve_vec(&mut self.rules, 1)
            .is_err()
        {
            source.dispose();
            return Err(HistoryError::AllocationFailed.into());
        }
        let runtime = CompiledRule::new(self.store.clone(), source)?;
        proof! {
            if event_obligations::<E>() {
                let flat = choose|flat: junco_core::flat::FlatRule<E::Component>|
                    junco_core::verify::flatten::flattened::<E>(supplied, flat)
                        && junco_core::verify::encoding::lowering(flat.source, runtime.template,
                            runtime.maps@, junco_core::verify::flatten::component_equality::<E>())
                        && junco_core::verify::encoding::constants_in_domain(flat.source,
                            history_store::typed::verify::domain::<E>());
                assert forall|i: int| 0 <= i < supplied@.head.len() implies
                    match #[trigger] supplied@.head[i] {
                        history_syntax::spec::events::PatternView::Constant(value) => E::coordinate_spec(value) == i,
                        _ => true,
                    } by {
                    assert(junco_core::verify::flatten::head_slot_represents(flat.source.head@[i], supplied@.head[i]));
                    assert(junco_core::verify::encoding::head_in_domain(flat.source.head@[i],
                        junco_core::verify::encoding::field_at(i), history_store::typed::verify::domain::<E>()));
                }
            }
        }
        self.rules.push(runtime);
        proof! {
            assert(verify::builder_sources(*self) =~= verify::builder_sources(before).push(supplied));
            assert(self.rules() =~= before.rules().push(supplied@));
            assert forall|i: int| 0 <= i < self.rules@.len() implies
                crate::compiled_rule::verify::compiled_wf(self.rules@[i]) && self.rules@[i].store == self.store by {
                if i < before.rules@.len() { assert(self.rules@[i] == before.rules@[i]); }
            }
        }
        Ok(self)
    }

    /// Creates the validator with the empty committed history in the rules' store.
    #[verus_spec(result => requires self.wf(),
        ensures event_obligations::<E>() ==> no_invariant_failure(result),
            result matches Ok(validator) ==> validator.wf()
            && validator@.rules == self.rules() && validator@.history == Seq::<E>::empty())]
    pub fn finish(self) -> Result<Validator<E>, HistoryError> {
        let history = History::new(self.store)?;
        proof! { raw::lemma_empty_history(history, self.store); }
        Ok(Validator {
            rules: self.rules,
            history,
        })
    }
}

/// Stateful validator for a fixed ordered rule set.
#[verus_verify]
pub struct Validator<E: Event> {
    pub(crate) rules: Vec<CompiledRule<E>>,
    pub(crate) history: History<E>,
}

#[verus_verify]
impl<E: Event> Validator<E> {
    /// Starts compiling a validator in `store`.
    #[verus_spec(result => requires history_store::typed::verify::store_wf(*store),
        ensures result.wf(), result.rules() == Seq::<RuleView<E::Component>>::empty())]
    pub fn builder(store: Arc<Store<E>>) -> ValidatorBuilder<E> {
        ValidatorBuilder::new(store)
    }

    /// Authorizes a request, appending its exact event only after successful evaluation
    /// (`check_frame`); under the event laws the decision means `check_step`.
    #[verus_spec(result => requires old(self).wf(),
        ensures final(self).wf(),
            check_frame(old(self)@, final(self)@, request, result),
            event_obligations::<E>() ==> check_step(old(self)@, request, result),
            event_obligations::<E>() ==> (result matches Err(error) ==> sem::resource_error(error)),
            result matches Ok(Decision::Denied(denial)) ==> verify::denial_message(denial),
            raw::owner_frame(verify::validator_history(*old(self)), verify::validator_history(*final(self))))]
    pub fn check<M>(&mut self, request: Request<E, M>) -> Result<Decision<E, M>, HistoryError> {
        self.check_with(request, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result => requires old(self).wf(),
        ensures final(self).wf(),
            check_frame(old(self)@, final(self)@, request, result),
            event_obligations::<E>() ==> check_step(old(self)@, request, result),
            event_obligations::<E>() ==> (result matches Err(error) ==> sem::resource_error(error)),
            result matches Ok(Decision::Denied(denial)) ==> verify::denial_message(denial),
            raw::owner_frame(verify::validator_history(*old(self)), verify::validator_history(*final(self))))]
    fn check_with<M, L: Limits>(
        &mut self,
        request: Request<E, M>,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Decision<E, M>, HistoryError> {
        proof_decl! { let ghost entry = *self; }
        let first = self.first_violation_with(&request.event, limits, world);
        proof! {
            crate::compiled_rule::verify::lemma_compiled_sources_frame(entry.rules@, self.rules@);
            assert(self@.rules == entry@.rules);
        }
        if let Some(index) = first? {
            let mode = self.rules[index].mode();
            let message = match mode {
                RuleMode::Require => {
                    "committed history does not satisfy required past-regex rule".to_owned()
                }
                RuleMode::Forbid => {
                    "committed history satisfies forbidden past-regex rule".to_owned()
                }
            };
            proof! {
                crate::compiled_rule::verify::lemma_compiled_mode_frame(entry.rules@, self.rules@, index as int);
                assert(crate::compiled_rule::verify::compiled_structure_frame(entry.rules@[index as int], self.rules@[index as int]));
                if event_obligations::<E>() {
                    crate::compiled_rule::verify::lemma_compiled_source_mode(self.rules@[index as int], mode);
                    assert(mode == entry@.rules[index as int].mode);
                    assert(sem::least_violation(entry@.rules, request.event, entry@.history, index as int));
                }
            }
            let denial = Denial {
                index,
                mode,
                event: request.event,
                message,
            };
            return Ok(Decision::Denied(denial));
        }
        let appended = self.history.push_with(request.event, limits, world);
        proof! {
            raw::lemma_push_result(entry.history, self.history, request.event, appended);
            raw::lemma_history_frame_facts(entry.history, self.history);
            assert(verify::validator_wf(*self));
            assert(self@.rules == entry@.rules);
        }
        appended?;
        Ok(Decision::Grant(Grant {
            event: request.event,
            metadata: request.metadata,
        }))
    }

    /// Evaluates without committing: the state is unchanged and, under the event laws, the
    /// answer is `permits_result`; errors are operational resource failures.
    #[verus_spec(result => requires old(self).wf(),
        ensures final(self).wf(), final(self)@ == old(self)@, no_invariant_failure(result),
            event_obligations::<E>() ==> permits_result(old(self)@, *candidate, result),
            event_obligations::<E>() ==> (result matches Err(error) ==> sem::resource_error(error)),
            raw::owner_frame(verify::validator_history(*old(self)), verify::validator_history(*final(self))))]
    pub fn permits(&mut self, candidate: &E) -> Result<bool, HistoryError> {
        proof_decl! { let ghost entry = *self; }
        let first = self.first_violation(candidate);
        proof! {
            crate::compiled_rule::verify::lemma_compiled_sources_frame(entry.rules@, self.rules@);
            assert(self@ == entry@);
            if event_obligations::<E>() {
                if let Ok(Some(index)) = first {
                    assert(sem::rule_violated(entry@.rules[index as int], *candidate, entry@.history));
                    assert(sem::policy_denies(entry@.rules, *candidate, entry@.history));
                }
            }
        }
        Ok(first?.is_none())
    }

    #[verus_spec(result => requires verify::validator_wf(*old(self)),
        ensures no_invariant_failure(result),
            event_obligations::<E>() ==> (result matches Err(error) ==> sem::resource_error(error)),
            verify::validator_frame(*old(self), *final(self)), final(self).history == old(self).history,
            result matches Ok(Some(index)) ==> index < final(self).rules@.len(),
            crate::compiled_rule::verify::ordered_result(verify::validator_sources(*old(self)), old(self).history, *candidate, result))]
    fn first_violation(&mut self, candidate: &E) -> Result<Option<usize>, HistoryError> {
        self.first_violation_with(candidate, &mut Unmetered, &mut ObservationWorld)
    }

    #[verus_spec(result => requires verify::validator_wf(*old(self)),
        ensures no_invariant_failure(result),
            event_obligations::<E>() ==> (result matches Err(error) ==> sem::resource_error(error)),
            verify::validator_frame(*old(self), *final(self)), final(self).history == old(self).history,
            result matches Ok(Some(index)) ==> index < final(self).rules@.len(),
            crate::compiled_rule::verify::ordered_result(verify::validator_sources(*old(self)), old(self).history, *candidate, result))]
    fn first_violation_with<L: Limits>(
        &mut self,
        candidate: &E,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<usize>, HistoryError> {
        proof_decl! { let ghost entry = *self; }
        proof! { history_store::history::verify::lemma_history_frame_facts(entry.history, entry.history); }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(invariant
            index <= self.rules@.len(), verify::validator_wf(*self), verify::validator_frame(entry, *self),
            entry == *old(self), self.history == entry.history,
            junco_core::spec::hypotheses::event_obligations::<E>() ==>
                forall|j: int| 0 <= j < index ==> !sem::rule_violated(
                    verify::validator_sources(entry)[j]@, *candidate, history_store::history::verify::raw_events(entry.history)),
            decreases self.rules@.len() - index))]
        while index < self.rules.len() {
            proof_decl! { let ghost before = *self; }
            let rule = &mut self.rules[index];
            let answer = rule.accepts_history_with_limits(&self.history, candidate, limits, world);
            let mode = rule.mode();
            proof! {
                if junco_core::spec::hypotheses::event_obligations::<E>() {
                    crate::compiled_rule::verify::lemma_dsl_violation(*rule, self.history, *candidate, answer, mode);
                }
                assert forall|j: int| 0 <= j < entry.rules@.len() implies
                    crate::compiled_rule::verify::compiled_structure_frame(entry.rules@[j], self.rules@[j]) by {
                    if j != index as int { assert(self.rules@[j] == before.rules@[j]); }
                }
                crate::compiled_rule::verify::lemma_compiled_sources_frame(entry.rules@, self.rules@);
                assert(verify::validator_wf(*self));
                assert(verify::validator_frame(entry, *self));
            }
            let violated = match answer? {
                None => false,
                Some(inside) => match mode {
                    RuleMode::Require => !inside,
                    RuleMode::Forbid => inside,
                },
            };
            if violated {
                return Ok(Some(index));
            }
            index += 1;
        }
        proof! {
            if event_obligations::<E>() {
                crate::compiled_rule::verify::lemma_no_violation_permits(
                    verify::validator_sources(entry), *candidate, raw::raw_events(entry.history));
            }
        }
        Ok(None)
    }

    /// Returns committed grants' events in exact acceptance order.
    #[verus_spec(result => ensures result@ == self@.history)]
    pub fn history(&self) -> &[E] {
        self.history.as_slice()
    }

    /// Captures the current committed-history position.
    #[verus_spec(result => ensures raw::checkpoint_matches(verify::validator_history(*self), result))]
    pub fn checkpoint(&self) -> Checkpoint {
        self.history.checkpoint()
    }

    /// Rolls back a checkpoint of this validator's history: `rollback_step`, plus the
    /// underlying history's checkpoint-ownership outcome.
    #[verus_spec(result => requires old(self).wf(),
        ensures final(self).wf(), rollback_step(old(self)@, final(self)@, result),
            raw::owner_frame(verify::validator_history(*old(self)), verify::validator_history(*final(self))),
            raw::rollback_result(verify::validator_history(*old(self)), verify::validator_history(*final(self)), checkpoint, result))]
    pub fn rollback(&mut self, checkpoint: Checkpoint) -> Result<(), HistoryError> {
        proof_decl! { let ghost entry = *self; }
        let result = self.history.rollback(checkpoint);
        proof! {
            raw::lemma_rollback_result(entry.history, self.history, checkpoint, result);
            raw::lemma_history_frame_facts(entry.history, self.history);
            crate::compiled_rule::verify::lemma_compiled_sources_frame(entry.rules@, self.rules@);
            assert(verify::validator_wf(*self));
            let before = raw::raw_events(entry.history);
            let after = raw::raw_events(self.history);
            if raw::state_frame(entry.history, self.history) {
                assert(after =~= before.subrange(0, after.len() as int));
            }
        }
        result
    }
}

impl<E: Event> Validator<E> {
    /// Resets the existing per-rule numeric event-work counters.
    #[cfg(feature = "test-util")]
    pub fn reset_work_events(&mut self) {
        for rule in &mut self.rules {
            rule.reset_work_events();
        }
    }

    /// Returns the saturating sum of existing per-rule numeric event-work counters.
    #[cfg(feature = "test-util")]
    pub fn work_events(&self) -> usize {
        self.rules.iter().fold(0usize, |total, rule| {
            total.saturating_add(rule.work_events())
        })
    }
}

/// Crate-internal frame predicates over the compiled entries, and the trace-safety lemmas of the monitor specification.
#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;
    use crate::compiled_rule::verify as compiled;
    use crate::spec::monitor::trace_safe;
    use history_store::history::verify as raw;
    verus! {
    pub open(crate) spec fn builder_store<E: Event>(builder: ValidatorBuilder<E>) -> Arc<Store<E>> { builder.store }
    pub open(crate) spec fn builder_rules<E: Event>(builder: ValidatorBuilder<E>) -> Seq<CompiledRule<E>> { builder.rules@ }
    pub open(crate) spec fn builder_sources<E: Event>(builder: ValidatorBuilder<E>) -> Seq<Rule<E>> {
        compiled::compiled_sources(builder.rules@)
    }
    pub open(crate) spec fn builder_wf<E: Event>(builder: ValidatorBuilder<E>) -> bool {
        compiled::compiled_table_wf(builder.rules@, builder.store)
    }
    pub open(crate) spec fn validator_history<E: Event>(validator: Validator<E>) -> History<E> { validator.history }
    pub open(crate) spec fn validator_sources<E: Event>(validator: Validator<E>) -> Seq<Rule<E>> {
        compiled::compiled_sources(validator.rules@)
    }
    pub open(crate) spec fn validator_wf<E: Event>(validator: Validator<E>) -> bool {
        raw::history_wf(validator.history)
            && compiled::compiled_table_wf(validator.rules@, raw::store_of(validator.history))
    }

    pub open(crate) spec fn validator_frame<E: Event>(before: Validator<E>, after: Validator<E>) -> bool {
        validator_wf(after) && compiled::compiled_table_frame(before.rules@, after.rules@)
            && validator_sources(after) == validator_sources(before)
            && raw::owner_frame(before.history, after.history)
    }

    /// The denial's explanation names the violated rule's mode.
    pub open spec fn denial_message<E: Event>(denial: Denial<E>) -> bool {
        denial.message@ == match denial.mode {
            RuleMode::Require => "committed history does not satisfy required past-regex rule"@,
            RuleMode::Forbid => "committed history satisfies forbidden past-regex rule"@,
        }
    }

    /// A `check` keeps the trace safe: a grant appends an event the policy permitted
    /// (`check_step`), every other outcome leaves the history as it was (`check_frame`).
    pub proof fn lemma_check_preserves_trace_safe<E: Event, M>(
        before: ValidatorView<E>, after: ValidatorView<E>, request: Request<E, M>,
        result: Result<Decision<E, M>, HistoryError>)
        requires trace_safe(before), check_frame(before, after, request, result),
            check_step(before, request, result),
        ensures trace_safe(after),
    {
        assert forall|j: int| 0 <= j < after.history.len() implies
            sem::policy_permits(after.rules, #[trigger] after.history[j], after.history.take(j)) by {
            if j < before.history.len() {
                assert(sem::policy_permits(before.rules, before.history[j], before.history.take(j)));
                assert(after.history.take(j) =~= before.history.take(j));
            } else {
                assert(after.history.take(j) =~= before.history);
            }
        }
    }

    /// A `rollback` keeps the trace safe: a prefix of a safe trace is safe.
    pub proof fn lemma_rollback_preserves_trace_safe<E: Event>(
        before: ValidatorView<E>, after: ValidatorView<E>, result: Result<(), HistoryError>)
        requires trace_safe(before), rollback_step(before, after, result),
        ensures trace_safe(after),
    {
        assert forall|j: int| 0 <= j < after.history.len() implies
            sem::policy_permits(after.rules, #[trigger] after.history[j], after.history.take(j)) by {
            assert(sem::policy_permits(before.rules, before.history[j], before.history.take(j)));
            assert(after.history.take(j) =~= before.history.take(j));
        }
    }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use history_syntax::{
        AtomPattern, Comparison, Component, Component3, ComponentPattern as P, Head, N3,
        RegexExpr as R, TestExpr as T,
    };
    use junco_core::limits::LimitError;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct Document {
        principal: u8,
        action: u8,
        resource: u8,
        payload: u16,
    }
    impl Event for Document {
        type Component = Component3<u8, u8, u8>;
        type Arity = N3;

        fn component(self, index: usize) -> Self::Component {
            match index {
                0 => Component3::C0(self.principal),
                1 => Component3::C1(self.action),
                _ => Component3::C2(self.resource),
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
    fn edit() -> Document {
        Document {
            principal: 7,
            action: 1,
            resource: 9,
            payload: 42,
        }
    }
    fn release() -> Document {
        Document {
            action: 2,
            payload: 21,
            ..edit()
        }
    }
    fn store() -> Arc<Store<Document>> {
        Arc::new(Store::new().unwrap())
    }
    fn any_head() -> Head<Document> {
        Head::new([
            P::variable("principal"),
            P::variable("action"),
            P::variable("resource"),
        ])
    }
    fn prior_edit() -> Rule<Document> {
        Rule::new(
            RuleMode::Require,
            Head::new([
                P::variable("actor"),
                P::constant(Component3::C1(2)),
                P::variable("resource"),
            ]),
            R::concat([
                R::all(),
                R::test(T::and([
                    T::atom(
                        Comparison::Eq,
                        AtomPattern::new(Component(0), P::variable("actor")),
                    ),
                    T::atom(
                        Comparison::Eq,
                        AtomPattern::new(Component(1), P::constant(Component3::C1(1))),
                    ),
                    T::atom(
                        Comparison::Eq,
                        AtomPattern::new(Component(2), P::variable("resource")),
                    ),
                ])),
                R::all(),
            ]),
        )
    }

    #[test]
    fn grants_preserve_event_metadata_and_append_exactly_once() {
        let mut builder = Validator::builder(store());
        builder.add_rule(prior_edit()).unwrap();
        let mut validator = builder.finish().unwrap();
        assert!(
            validator
                .check(Request::new(edit(), ()))
                .unwrap()
                .is_grant()
        );
        assert_eq!(validator.history(), &[edit()]);
        let checkpoint = validator.checkpoint();
        let metadata = alloc::vec![3u8, 1, 4];
        let Decision::Grant(grant) = validator
            .check(Request::new(release(), metadata.clone()))
            .unwrap()
        else {
            panic!("matching prior edit must grant")
        };
        assert_eq!(grant.event, release());
        assert_eq!(grant.metadata, metadata);
        assert_eq!(validator.history(), &[edit(), release()]);
        let other = Document {
            principal: 8,
            ..release()
        };
        assert!(
            matches!(validator.check(Request::new(other, ())).unwrap(), Decision::Denied(Denial { mode: RuleMode::Require, event, .. }) if event == other)
        );
        assert_eq!(validator.history(), &[edit(), release()]);
        assert!(validator.permits(&release()).unwrap());
        assert_eq!(validator.history(), &[edit(), release()]);
        validator.rollback(checkpoint).unwrap();
        assert_eq!(validator.history(), &[edit()]);
    }

    #[test]
    fn first_violation_order_and_empty_tables_are_preserved() {
        for first in [RuleMode::Require, RuleMode::Forbid] {
            let mut builder = Validator::builder(store());
            for mode in [
                first,
                if first == RuleMode::Require {
                    RuleMode::Forbid
                } else {
                    RuleMode::Require
                },
            ] {
                builder
                    .add_rule(Rule::new(
                        mode,
                        any_head(),
                        if mode == RuleMode::Require {
                            R::empty()
                        } else {
                            R::all()
                        },
                    ))
                    .unwrap();
            }
            let mut validator = builder.finish().unwrap();
            assert!(
                matches!(validator.check(Request::new(release(), ())).unwrap(), Decision::Denied(Denial { index: 0, mode, .. }) if mode == first)
            );
            assert!(validator.history().is_empty());
        }
        // The index must distinguish violations with the same mode, after a nonviolating rule.
        let mut builder = Validator::builder(store());
        builder
            .add_rule(Rule::new(RuleMode::Require, any_head(), R::all()))
            .unwrap();
        builder
            .add_rule(Rule::new(RuleMode::Forbid, any_head(), R::all()))
            .unwrap();
        builder
            .add_rule(Rule::new(RuleMode::Forbid, any_head(), R::all()))
            .unwrap();
        let mut validator = builder.finish().unwrap();
        assert!(matches!(
            validator.check(Request::new(release(), ())).unwrap(),
            Decision::Denied(Denial {
                index: 1,
                mode: RuleMode::Forbid,
                ..
            })
        ));
        assert!(validator.history().is_empty());
        let mut empty = Validator::<Document>::builder(store()).finish().unwrap();
        assert!(empty.permits(&release()).unwrap());
        assert!(empty.check(Request::new(release(), ())).unwrap().is_grant());
        assert_eq!(empty.history(), &[release()]);
    }

    #[test]
    fn append_allocation_error_is_not_a_denial_or_a_grant() {
        let mut validator = Validator::<Document>::builder(store()).finish().unwrap();
        let _failure = junco_core::observation::fail_reservations_after(0);
        assert!(matches!(
            validator.check(Request::new(edit(), ())),
            Err(HistoryError::AllocationFailed)
        ));
        assert!(validator.history().is_empty());
    }

    struct PublicationFailure;
    impl Limits for PublicationFailure {
        fn checkpoint(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn enforce_memory(&mut self) -> Result<(), LimitError> {
            Ok(())
        }
        fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
            Err(LimitError::RegexSizeLimitExceeded { limit: 0 })
        }
    }

    #[test]
    fn evaluation_error_does_not_append_or_become_a_denial() {
        let mut builder = Validator::builder(store());
        builder
            .add_rule(Rule::new(RuleMode::Require, any_head(), R::epsilon()))
            .unwrap();
        let mut validator = builder.finish().unwrap();
        assert!(matches!(
            validator.check_with(
                Request::new(release(), ()),
                &mut PublicationFailure,
                &mut ObservationWorld
            ),
            Err(HistoryError::Limit(_))
        ));
        assert!(validator.history().is_empty());
    }

    #[test]
    fn failed_builder_reservation_drains_a_deep_owned_rule() {
        let mut tail = R::<Document>::epsilon();
        for _ in 0..4096 {
            tail = R::star(tail);
        }
        let source = Rule::new(RuleMode::Require, any_head(), tail);
        let mut builder = Validator::builder(store());
        {
            let _failure = junco_core::observation::fail_reservations_after(0);
            assert!(matches!(
                builder.add_rule(source),
                Err(CompileError::Runtime(HistoryError::AllocationFailed))
            ));
        }
        assert!(builder.finish().unwrap().permits(&release()).unwrap());
    }
}
