//! Ordered authorization and append-on-grant request handling.
//!
//! This native facade delegates language evaluation and history transactions to the verified
//! [`CompiledRule`] and [`History`] bodies. Formatting and opaque request metadata remain native.

use alloc::{format, string::String, sync::Arc, vec::Vec};

use crate::compiled_rule::CompiledRule;
use history_store::history::{Checkpoint, History};
use history_store::typed::Store;
use history_syntax::Event;
use history_syntax::syntax::{Rule, RuleMode};
use junco_core::error::{CompileError, HistoryError};
use junco_core::event::{Grant, Request};
use junco_core::limits::{Limits, Unmetered};
use junco_core::observation::ObservationWorld;

/// Diagnostic returned when the first matching rule is violated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Denial<E: Event> {
    /// Whether the violated rule required or forbade its tail language.
    pub mode: RuleMode,
    /// Candidate event that was denied and was not appended to history.
    pub event: E,
    /// Human-readable explanation of the failed history relation.
    pub message: String,
}

/// Result of checking one capability request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision<E: Event, M> {
    /// Request was accepted and appended to committed history.
    Grant(Grant<E, M>),
    /// Request was rejected atomically; committed history is unchanged.
    Denied(Denial<E>),
}

impl<E: Event, M> Decision<E, M> {
    /// Returns `true` exactly for [`Decision::Grant`].
    pub fn is_grant(&self) -> bool {
        matches!(self, Self::Grant(_))
    }
}

/// Compiles an ordered rule set sharing one typed store.
pub struct ValidatorBuilder<E: Event> {
    store: Arc<Store<E>>,
    rules: Vec<CompiledRule<E>>,
}

impl<E: Event> ValidatorBuilder<E> {
    /// Creates an empty builder in `store`.
    pub fn new(store: Arc<Store<E>>) -> Self {
        Self {
            store,
            rules: Vec::new(),
        }
    }

    /// Compiles and appends one complete source rule.
    pub fn add_rule(&mut self, source: Rule<E>) -> Result<&mut Self, CompileError> {
        if ObservationWorld
            .try_reserve_vec(&mut self.rules, 1)
            .is_err()
        {
            source.dispose();
            return Err(HistoryError::AllocationFailed.into());
        }
        let runtime = CompiledRule::new(self.store.clone(), source)?;
        self.rules.push(runtime);
        Ok(self)
    }

    /// Creates the empty committed history in the rules' store.
    pub fn finish(self) -> Result<Validator<E>, HistoryError> {
        Ok(Validator {
            rules: self.rules,
            history: History::new(self.store)?,
        })
    }
}

/// Stateful validator for a fixed ordered rule set.
pub struct Validator<E: Event> {
    rules: Vec<CompiledRule<E>>,
    history: History<E>,
}

impl<E: Event> Validator<E> {
    /// Starts compiling a validator in `store`.
    pub fn builder(store: Arc<Store<E>>) -> ValidatorBuilder<E> {
        ValidatorBuilder::new(store)
    }

    /// Authorizes a request, appending its exact event only after successful evaluation.
    pub fn check<M>(&mut self, request: Request<E, M>) -> Result<Decision<E, M>, HistoryError> {
        self.check_with(request, &mut Unmetered, &mut ObservationWorld)
    }

    fn check_with<M, L: Limits>(
        &mut self,
        request: Request<E, M>,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Decision<E, M>, HistoryError> {
        if let Some(mode) = self.first_violation_with(&request.event, limits, world)? {
            let relation = match mode {
                RuleMode::Require => "does not satisfy required",
                RuleMode::Forbid => "satisfies forbidden",
            };
            return Ok(Decision::Denied(Denial {
                mode,
                event: request.event,
                message: format!("committed history {relation} past-regex rule"),
            }));
        }
        self.history.push_with(request.event, limits, world)?;
        Ok(Decision::Grant(Grant {
            event: request.event,
            metadata: request.metadata,
        }))
    }

    /// Evaluates without appending; retained residuals fold only newly committed events.
    pub fn permits(&mut self, candidate: &E) -> Result<bool, HistoryError> {
        Ok(self.first_violation(candidate)?.is_none())
    }

    fn first_violation(&mut self, candidate: &E) -> Result<Option<RuleMode>, HistoryError> {
        self.first_violation_with(candidate, &mut Unmetered, &mut ObservationWorld)
    }

    fn first_violation_with<L: Limits>(
        &mut self,
        candidate: &E,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<Option<RuleMode>, HistoryError> {
        for rule in &mut self.rules {
            let Some(inside) =
                rule.accepts_history_with_limits(&self.history, candidate, limits, world)?
            else {
                continue;
            };
            let violated = match rule.mode() {
                RuleMode::Require => !inside,
                RuleMode::Forbid => inside,
            };
            if violated {
                return Ok(Some(rule.mode()));
            }
        }
        Ok(None)
    }

    /// Returns committed grants' events in exact acceptance order.
    pub fn history(&self) -> &[E] {
        self.history.as_slice()
    }

    /// Captures the current committed-history position.
    pub fn checkpoint(&self) -> Checkpoint {
        self.history.checkpoint()
    }

    /// Rolls back a checkpoint belonging to this validator's history.
    pub fn rollback(&mut self, checkpoint: Checkpoint) -> Result<(), HistoryError> {
        self.history.rollback(checkpoint)
    }

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

#[cfg(test)]
mod tests {
    use super::*;
    use history_syntax::{
        AtomPattern, Comparison, ComponentPattern as P, Head, RegexExpr as R, TestExpr as T,
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
        type Principal = u8;
        type Action = u8;
        type Resource = u8;
        fn principal(self) -> u8 {
            self.principal
        }
        fn action(self) -> u8 {
            self.action
        }
        fn resource(self) -> u8 {
            self.resource
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
        Head::new(
            P::variable("principal"),
            P::variable("action"),
            P::variable("resource"),
        )
    }
    fn prior_edit() -> Rule<Document> {
        Rule::new(
            RuleMode::Require,
            Head::new(
                P::variable("actor"),
                P::constant(2),
                P::variable("resource"),
            ),
            R::concat([
                R::all(),
                R::test(T::and([
                    T::atom(Comparison::Eq, AtomPattern::Principal(P::variable("actor"))),
                    T::atom(Comparison::Eq, AtomPattern::Action(P::constant(1))),
                    T::atom(
                        Comparison::Eq,
                        AtomPattern::Resource(P::variable("resource")),
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
                matches!(validator.check(Request::new(release(), ())).unwrap(), Decision::Denied(Denial { mode, .. }) if mode == first)
            );
            assert!(validator.history().is_empty());
        }
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
