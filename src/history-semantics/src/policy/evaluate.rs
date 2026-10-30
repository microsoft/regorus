//! Compilation and evaluation for declarative trace-policy tables.

use alloc::{sync::Arc, vec::Vec};

use super::decision::PolicyDecision;
use super::rule::{Diagnostic, PolicyRule};
use crate::CompiledRule;
use history_store::{History, Store};
use history_syntax::{Event, RuleMode};
use junco_core::limits::{Limits, Unmetered};
use junco_core::observation::ObservationWorld;
use junco_core::{CompileError, HistoryError};

/// One compiled runtime rule paired with the diagnostic rendered when it is violated.
struct CompiledPolicyRule<E: Event, C> {
    runtime: CompiledRule<E>,
    diagnostic: Diagnostic<C>,
}

/// A policy table whose compiled rules and caches survive successive decisions.
///
/// Diagnostics are native callbacks; policy packaging does not extend the backend's proof to
/// arbitrary callback implementations.
pub struct CompiledPolicy<E: Event, C> {
    store: Arc<Store<E>>,
    rules: Vec<CompiledPolicyRule<E, C>>,
}

impl<E: Event, C> CompiledPolicy<E, C> {
    /// Compiles every source rule in order and preserves its paired diagnostic.
    pub fn new(store: Arc<Store<E>>, rules: Vec<PolicyRule<E, C>>) -> Result<Self, CompileError> {
        Self::from_rules(store, rules)
    }

    pub(super) fn from_rules(
        store: Arc<Store<E>>,
        rules: impl IntoIterator<Item = PolicyRule<E, C>>,
    ) -> Result<Self, CompileError> {
        let mut compiled = Vec::new();
        let mut remaining = rules.into_iter();
        let mut world = ObservationWorld;
        while let Some(PolicyRule { rule, diagnostic }) = remaining.next() {
            if world.try_reserve_vec(&mut compiled, 1).is_err() {
                rule.dispose();
                for pending in remaining {
                    pending.rule.dispose();
                }
                return Err(HistoryError::AllocationFailed.into());
            }
            let runtime = match CompiledRule::new(Arc::clone(&store), rule) {
                Ok(runtime) => runtime,
                Err(error) => {
                    for pending in remaining {
                        pending.rule.dispose();
                    }
                    return Err(error);
                }
            };
            compiled.push(CompiledPolicyRule {
                runtime,
                diagnostic,
            });
        }
        Ok(Self {
            store,
            rules: compiled,
        })
    }

    /// Returns the first violation without appending to the caller's history.
    ///
    /// `context` and the selected diagnostic run once on denial only. Foreign histories are
    /// rejected even by an empty table, before callbacks or candidate encoding.
    pub fn decide(
        &mut self,
        history: &History<E>,
        probe: &E,
        context: impl FnOnce() -> C,
    ) -> Result<PolicyDecision, HistoryError> {
        self.decide_with_limits(
            history,
            probe,
            context,
            &mut Unmetered,
            &mut ObservationWorld,
        )
    }

    pub(super) fn decide_with_limits<L: Limits>(
        &mut self,
        history: &History<E>,
        probe: &E,
        context: impl FnOnce() -> C,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<PolicyDecision, HistoryError> {
        if !Arc::ptr_eq(&self.store, history.store()) {
            return Err(HistoryError::WrongHistoryOwner);
        }
        for rule in &mut self.rules {
            let Some(inside) = rule
                .runtime
                .accepts_history_with_limits(history, probe, limits, world)?
            else {
                continue;
            };
            let violated = match rule.runtime.mode() {
                RuleMode::Forbid => inside,
                RuleMode::Require => !inside,
            };
            if violated {
                let (failed_precondition, allowed_fixes) = (rule.diagnostic)(&context());
                return Ok(PolicyDecision::Deny {
                    failed_precondition,
                    allowed_fixes,
                });
            }
        }
        Ok(PolicyDecision::Grant)
    }
}
