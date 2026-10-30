//! A caller-assembled trace policy whose history stays with the caller.

use alloc::{boxed::Box, string::String, sync::Arc, vec::Vec};
use core::fmt;

use super::decision::PolicyDecision;
use super::evaluate::CompiledPolicy;
use super::rule::PolicyRule;
use history_store::{History, Store};
use history_syntax::{Event, Rule};
use junco_core::{CompileError, HistoryError};

/// Renders a violated rule's `(failed_precondition, allowed_fixes)` from the candidate event.
pub type TraceDiagnostic<E> = Arc<dyn Fn(&E) -> (String, Vec<String>) + Send + Sync>;

/// One caller-supplied rule paired with the diagnostic its violation surfaces.
pub struct TraceRule<E: Event> {
    /// The past-regex rule.
    pub rule: Rule<E>,
    /// Renders the denial when `rule` is violated.
    pub diagnostic: TraceDiagnostic<E>,
}

impl<E: Event> TraceRule<E> {
    /// Pairs `rule` with `diagnostic`.
    pub fn new(
        rule: Rule<E>,
        diagnostic: impl Fn(&E) -> (String, Vec<String>) + Send + Sync + 'static,
    ) -> Self {
        Self {
            rule,
            diagnostic: Arc::new(diagnostic),
        }
    }
}

impl<E: Event> Clone for TraceRule<E> {
    fn clone(&self) -> Self {
        Self {
            rule: self.rule.clone(),
            diagnostic: Arc::clone(&self.diagnostic),
        }
    }
}

impl<E: Event> fmt::Debug for TraceRule<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("TraceRule")
            .field("rule", &self.rule)
            .finish_non_exhaustive()
    }
}

/// A caller-assembled rule table compiled once and decided against external histories.
pub struct TracePolicy<E: Event> {
    compiled: CompiledPolicy<E, E>,
}

impl<E: Event + 'static> TracePolicy<E> {
    /// Compiles every rule in order, preserving the first-violation diagnostic.
    pub fn new(
        store: Arc<Store<E>>,
        rules: impl IntoIterator<Item = TraceRule<E>>,
    ) -> Result<Self, CompileError> {
        let rules = rules
            .into_iter()
            .map(|TraceRule { rule, diagnostic }| PolicyRule {
                rule,
                diagnostic: Box::new(move |event: &E| diagnostic(event)),
            });
        Ok(Self {
            compiled: CompiledPolicy::from_rules(store, rules)?,
        })
    }

    /// Decides without appending; retained progress is reused for later decisions.
    pub fn decide(
        &mut self,
        history: &History<E>,
        candidate: &E,
    ) -> Result<PolicyDecision, HistoryError> {
        self.compiled.decide(history, candidate, || *candidate)
    }
}
