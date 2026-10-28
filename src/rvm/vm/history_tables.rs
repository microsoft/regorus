// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Bounded typed history steps. A decision pins one revision/prefix and each active
//! rule pins its graph generation; no synchronization guard survives a dispatch.

// Verus contracts require crate visibility and reference-pattern matches.
#[allow(clippy::redundant_pub_crate, clippy::pattern_type_mismatch)]
pub(crate) mod error;
#[allow(clippy::redundant_pub_crate, clippy::pattern_type_mismatch)]
pub(crate) mod graph;
#[allow(clippy::redundant_pub_crate, clippy::pattern_type_mismatch)]
pub(crate) mod kernel;
#[allow(clippy::redundant_pub_crate, clippy::pattern_type_mismatch)]
pub(crate) mod normalize;
#[allow(clippy::redundant_pub_crate, clippy::pattern_type_mismatch)]
pub(crate) mod progress;
#[allow(clippy::redundant_pub_crate, clippy::pattern_type_mismatch)]
pub(crate) mod source;
#[allow(clippy::redundant_pub_crate, clippy::pattern_type_mismatch)]
pub(crate) mod symbolic;

#[allow(
    clippy::redundant_pub_crate,
    reason = "Shared history work queues stay crate-visible."
)]
pub(crate) type WorkVec<T> = smallvec::SmallVec<[T; 4]>;

#[allow(
    clippy::redundant_pub_crate,
    reason = "The public language API re-exports this error."
)]
pub(crate) use error::HistoryError;
#[allow(
    clippy::redundant_pub_crate,
    reason = "Native observation capability stays crate-visible."
)]
pub(crate) use graph::ObservationWorld;

use self::graph::allocation;
#[cfg(verus_keep_ghost)]
use self::kernel::verify as model;
use self::kernel::{Bindings, KernelResult, RegexId};
use self::progress::CompiledPair;
use super::dispatch::InstructionOutcome;
use super::errors::{Result, VmError};
use super::execution_model::ExecutionState;
use super::machine::RegoVM;
#[cfg(test)]
use crate::languages::history_table::store::HistoryCursor;
use crate::languages::history_table::store::{HistoryTableRuntime, RuleRuntime, StoredHistory};
use crate::languages::history_table::{Event, HistoryHandle, HistoryStore};
use crate::rvm::program::{HistoryRuleMode, Program};
use crate::utils::limits::{ExecutionTimer, LimitError};
use crate::value::Value;
#[cfg(verus_keep_ghost)]
use crate::verify::{history_algebra, history_specs as language};
use alloc::sync::Arc;
use alloc::vec::Vec;
#[cfg(feature = "std")]
use parking_lot::{Mutex, RwLock};
#[cfg(not(feature = "std"))]
use spin::{Mutex, RwLock};
use vstd::prelude::*;

#[derive(Debug)]
pub(super) struct HistoryAttachment {
    store: Arc<HistoryStore>,
    tables: Vec<Arc<HistoryTableRuntime>>,
}

#[derive(Debug)]
pub(super) struct HistoryDecision {
    history: usize,
    record: Arc<RwLock<StoredHistory>>,
    revision: u64,
    target_len: usize,
    request: Event,
}

#[derive(Debug)]
pub(super) struct ActiveHistoryRule {
    pc: usize,
    bindings: Bindings,
    instance: Arc<Mutex<RuleRuntime>>,
    cursor: BatchCursor,
    retried: bool,
}

#[expect(
    clippy::redundant_pub_crate,
    reason = "Verus contracts require crate-visible transaction state."
)]
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct BatchCursor {
    pub(crate) consumed: usize,
    pub(crate) residual: RegexId,
}

impl BatchCursor {
    /// The same executable transaction is used under the runtime/history locks.
    /// No cursor changes until fold, final answer, and publication checks all succeed.
    #[expect(
        clippy::too_many_arguments,
        reason = "Keep explicit transaction inputs aligned with its verified contract."
    )]
    #[verus_verify]
    #[verus_spec(result =>
        requires
            crate::rvm::vm::history_tables::progress::verify::pair_wf(*old(pair)),
            crate::rvm::vm::history_tables::progress::verify::residual_after_prefix(
                *old(pair), crate::rvm::vm::history_tables::kernel::verify::events_view(events@), bindings@,
                old(self).consumed as nat, old(self).residual),
        ensures
            crate::rvm::vm::history_tables::progress::verify::pair_wf(*final(pair)),
            crate::rvm::vm::history_tables::progress::verify::pair_frame(*old(pair), *final(pair)),
            result is Err ==> final(self).consumed == old(self).consumed
                && final(self).residual == old(self).residual,
            result is Ok ==> old(self).consumed <= final(self).consumed
                && final(self).consumed <= target_len
                && final(self).consumed == crate::verify::history_specs::selected_end(old(self).consumed as nat, target_len as nat, batch_size as nat),
            result matches Ok(Some(_)) ==> final(self).consumed == target_len,
            result matches Ok(None) ==> final(self).consumed < target_len,
            result is Ok ==> crate::rvm::vm::history_tables::progress::verify::residual_folds(
                *final(pair), bindings@, old(self).residual,
                crate::rvm::vm::history_tables::kernel::verify::events_view(events@).subrange(old(self).consumed as int, final(self).consumed as int),
                final(self).residual),
            result matches Ok(Some(answer)) ==> answer == crate::rvm::vm::history_tables::kernel::verify::regex_lang(
                (*final(pair)).store.graph(), bindings@,
                old(self).residual@, crate::rvm::vm::history_tables::kernel::verify::events_view(events@).subrange(old(self).consumed as int, target_len as int)),
            result is Ok ==> crate::rvm::vm::history_tables::progress::verify::residual_after_prefix(
                *final(pair), crate::rvm::vm::history_tables::kernel::verify::events_view(events@), bindings@,
                final(self).consumed as nat, final(self).residual),
            result matches Ok(Some(answer)) ==> answer == crate::rvm::vm::history_tables::kernel::verify::regex_lang(
                (*old(pair)).store.graph(), bindings@,
                old(pair).root@, crate::rvm::vm::history_tables::kernel::verify::events_view(events@).take(target_len as int)),
    )]
    pub(crate) fn advance(
        &mut self,
        pair: &mut CompiledPair,
        events: &[Event],
        bindings: &Bindings,
        target_len: usize,
        batch_size: usize,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<Option<bool>> {
        proof_decl! { let ghost entry = *pair; let ghost entry_cursor = *self; }
        if batch_size == 0 || self.consumed > target_len || target_len > events.len() {
            return Err(HistoryError::invariant("invalid history batch bounds"));
        }
        let remaining = target_len
            .checked_sub(self.consumed)
            .ok_or(HistoryError::invariant("invalid history remaining length"))?;
        let count = if batch_size < remaining {
            batch_size
        } else {
            remaining
        };
        let end = self
            .consumed
            .checked_add(count)
            .ok_or(HistoryError::invariant("invalid history batch end"))?;
        proof! {
            language::lemma_selected_end(self.consumed as nat, target_len as nat, batch_size as nat);
            assert(end == language::selected_end(self.consumed as nat, target_len as nat, batch_size as nat));
        }
        let suffix = events
            .get(self.consumed..end)
            .ok_or(HistoryError::invariant("invalid history batch slice"))?;
        proof! {
            assert(model::events_view(suffix@) =~= model::events_view(events@).subrange(self.consumed as int, end as int));
        }
        let residual = pair.fold(self.residual, suffix, bindings, timer, world)?;
        let answer = if end == target_len {
            let answer = pair.answer(residual, timer, world)?;
            proof! {
                language::lemma_nullable_iff_nil(model::gsem(bindings@), model::lift_regex((*pair).store.graph(), residual@));
                assert(model::events_view(suffix@) + Seq::<language::EventView>::empty() =~= model::events_view(suffix@));
                assert(model::regex_lang((*pair).store.graph(), bindings@, residual@, Seq::empty())
                    == model::regex_lang((*pair).store.graph(), bindings@, entry_cursor.residual@, model::events_view(suffix@)));
            }
            Some(answer)
        } else {
            None
        };
        world.publication_checkpoint(timer)?;
        proof! {
            model::lemma_graph_wf_elim(entry.store.graph());
            model::lemma_lift_regex_stable(entry.store.graph(), (*pair).store.graph(), entry.root@);
            history_algebra::theorem_batch_extends_pinned_prefix(
                entry.store.graph(), (*pair).store.graph(), bindings@,
                entry.root@, entry_cursor.residual@, residual@, model::events_view(events@),
                entry_cursor.consumed as nat, end as nat,
            );
        }
        // Commit the cursor last so every fallible operation leaves it unchanged.
        self.consumed = end;
        self.residual = residual;
        Ok(answer)
    }
}

impl HistoryAttachment {
    fn new(store: Arc<HistoryStore>, program: &Arc<Program>) -> KernelResult<Self> {
        let mut tables = Vec::new();
        allocation(tables.try_reserve_exact(program.history_tables.len()))?;
        for table in 0..program.history_tables.len() {
            tables.push(store.table_runtime(program, table)?);
        }
        Ok(Self { store, tables })
    }
}

impl HistoryDecision {
    fn check(
        &self,
        stored: &StoredHistory,
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> KernelResult<()> {
        world.publication_checkpoint(timer)?;
        if stored.revision != self.revision || stored.events.len() < self.target_len {
            return Err(HistoryError::HistoryChanged {
                expected: self.revision,
                actual: stored.revision,
            });
        }
        Ok(())
    }
}

impl VmError {
    pub(super) fn from_history(error: HistoryError, pc: usize) -> Self {
        match error {
            HistoryError::Limit(LimitError::TimeLimitExceeded { elapsed, limit }) => {
                VmError::TimeLimitExceeded { elapsed, limit, pc }
            }
            HistoryError::Limit(LimitError::MemoryLimitExceeded { usage, limit }) => {
                VmError::MemoryLimitExceeded { usage, limit, pc }
            }
            HistoryError::Limit(LimitError::RegexSizeLimitExceeded { limit }) => {
                VmError::RegexSizeLimitExceeded { limit, pc }
            }
            source => VmError::History { source, pc },
        }
    }
}
impl RegoVM {
    /// Attach the application-owned history service after loading the program.
    /// Numeric templates and initial graphs are prepared outside decision timing.
    pub fn attach_history(&mut self, store: Arc<HistoryStore>) -> Result<()> {
        self.ensure_history_idle()?;
        let attachment = HistoryAttachment::new(store, &self.program)
            .map_err(|error| VmError::from_history(error, self.pc))?;
        self.history_attachment = Some(attachment);
        self.history_input = None;
        self.clear_history_execution();
        Ok(())
    }

    /// Stage a typed request without appending it to the supplied history.
    pub fn set_history_input(&mut self, history: HistoryHandle, request: Event) -> Result<()> {
        self.ensure_history_idle()?;
        let attachment = self
            .history_attachment
            .as_ref()
            .ok_or(VmError::HistoryContextMissing { pc: self.pc })?;
        attachment
            .store
            .history_record(&history)
            .map_err(|error| VmError::from_history(error, self.pc))?;
        attachment
            .store
            .validate_event(&request)
            .map_err(|error| VmError::from_history(error, self.pc))?;
        self.history_input = Some((history, request));
        self.clear_history_execution();
        Ok(())
    }

    const fn ensure_history_idle(&self) -> Result<()> {
        if matches!(
            self.execution_state,
            ExecutionState::Running | ExecutionState::Suspended { .. }
        ) || self.history_decision.is_some()
        {
            return Err(VmError::HistoryExecutionActive { pc: self.pc });
        }
        Ok(())
    }

    pub(super) fn clear_history_execution(&mut self) {
        self.history_decision = None;
        self.history_active_rule = None;
    }

    /// Common execution preflight also covers empty tables with no HistoryStep.
    pub(super) fn begin_history_execution(&mut self) -> Result<()> {
        if self.program.metadata.language == "history_table" {
            self.capture_history_decision()?;
        }
        Ok(())
    }

    fn capture_history_decision(&mut self) -> Result<()> {
        if self.history_decision.is_some() {
            return Ok(());
        }
        let attachment = self
            .history_attachment
            .as_ref()
            .ok_or(VmError::HistoryContextMissing { pc: self.pc })?;
        let staged = self
            .history_input
            .as_ref()
            .ok_or(VmError::HistoryContextMissing { pc: self.pc })?;
        let record = attachment
            .store
            .history_record(&staged.0)
            .map_err(|error| VmError::from_history(error, self.pc))?;
        let stored = record.read();
        ObservationWorld
            .publication_checkpoint(&mut self.execution_timer)
            .map_err(|error| VmError::from_history(error, self.pc))?;
        let revision = stored.revision;
        let target_len = stored.events.len();
        drop(stored);
        self.history_decision = Some(HistoryDecision {
            history: staged.0.index,
            record,
            revision,
            target_len,
            request: staged.1,
        });
        Ok(())
    }

    pub(super) fn finish_history_execution(&mut self) -> Result<()> {
        let result = if let Some(decision) = self.history_decision.as_ref() {
            let stored = decision.record.read();
            // Revalidate even terminal decisions: truncation may invalidate a pinned prefix.
            decision
                .check(&stored, &mut self.execution_timer, &mut ObservationWorld)
                .map_err(|error| VmError::from_history(error, self.pc))
        } else {
            Ok(())
        };
        self.clear_history_execution();
        result
    }

    pub(super) fn execute_history_step(&mut self, params_index: u16) -> Result<InstructionOutcome> {
        let pc = self.pc;
        let params = self
            .program
            .instruction_data
            .history_step_params
            .get(usize::from(params_index))
            .ok_or(VmError::InvalidHistoryStepParams {
                index: params_index,
                pc,
            })?
            .clone();
        let table = self
            .program
            .history_tables
            .get(usize::from(params.table))
            .ok_or(VmError::InvalidHistoryTableIndex {
                index: params.table,
                pc,
            })?;
        table
            .rules
            .get(usize::from(params.rule))
            .ok_or(VmError::InvalidHistoryRuleIndex {
                table: params.table,
                rule: params.rule,
                pc,
            })?;
        if params.batch_size == 0 {
            return Err(VmError::InvalidHistoryBatchSize {
                batch_size: params.batch_size,
                pc,
            });
        }
        let batch_size = usize::try_from(params.batch_size).map_err(|_| {
            VmError::from_history(
                HistoryError::invariant("history batch_size does not fit usize"),
                pc,
            )
        })?;
        self.capture_history_decision()?;
        let attachment = self
            .history_attachment
            .as_ref()
            .ok_or(VmError::HistoryContextMissing { pc })?;
        let runtime = attachment
            .tables
            .get(usize::from(params.table))
            .cloned()
            .ok_or(VmError::InvalidHistoryTableIndex {
                index: params.table,
                pc,
            })?;
        let slot = runtime.rules.get(usize::from(params.rule)).ok_or(
            VmError::InvalidHistoryRuleIndex {
                table: params.table,
                rule: params.rule,
                pc,
            },
        )?;
        let decision = self
            .history_decision
            .as_ref()
            .ok_or(VmError::HistoryContextMissing { pc })?;
        // A loaded program fixes parameters at each PC; loading another clears active execution.
        if self
            .history_active_rule
            .as_ref()
            .is_some_and(|active| active.pc != pc)
        {
            return Err(VmError::from_history(
                HistoryError::invariant("history continuation belongs to another instruction"),
                pc,
            ));
        }
        let mut world = ObservationWorld;
        if self.history_active_rule.is_none() {
            let instance = Arc::clone(&slot.current.lock());
            // Lock graph before history consistently; retain both guards through validation.
            let mut graph = instance.lock();
            let stored = decision.record.read();
            decision
                .check(&stored, &mut self.execution_timer, &mut world)
                .map_err(|error| VmError::from_history(error, pc))?;
            let Some(bindings) = slot.template.bindings(&decision.request) else {
                return Ok(InstructionOutcome::Continue);
            };
            // Native provenance: this locked record belongs to decision.history;
            // same-revision observations extend its previously recorded word.
            let cursor =
                graph.resume_cursor(decision.history, &bindings, &stored, decision.target_len);
            drop(stored);
            drop(graph);
            self.history_active_rule = Some(ActiveHistoryRule {
                pc,
                bindings,
                instance,
                cursor,
                retried: false,
            });
        }
        let active = self
            .history_active_rule
            .as_mut()
            .ok_or(VmError::HistoryContextMissing { pc })?;
        // Keep graph-before-history order through the fold and successful publication.
        let mut graph = active.instance.lock();
        let stored = decision.record.read();
        decision
            .check(&stored, &mut self.execution_timer, &mut world)
            .map_err(|error| VmError::from_history(error, pc))?;
        let outcome = graph.advance_cursor(
            &mut active.cursor,
            decision.history,
            &active.bindings,
            &stored,
            decision.target_len,
            batch_size,
            &mut self.execution_timer,
            &mut world,
        );
        match outcome {
            Ok(answer) => {
                drop(stored);
                drop(graph);
                match answer {
                    None => Ok(InstructionOutcome::Repeat),
                    Some(answer) => {
                        self.history_active_rule = None;
                        let violated = match slot.mode {
                            HistoryRuleMode::Require => !answer,
                            HistoryRuleMode::Forbid => answer,
                        };
                        if violated {
                            Ok(InstructionOutcome::Return(Value::from(usize::from(
                                params.rule,
                            ))))
                        } else {
                            Ok(InstructionOutcome::Continue)
                        }
                    }
                }
            }
            Err(HistoryError::GraphLimit { .. }) if !active.retried => {
                let exhausted = Arc::clone(&active.instance);
                drop(stored);
                drop(graph);
                let replacement =
                    RuleRuntime::new(&slot.template, false, &mut self.execution_timer, &mut world)
                        .map_err(|error| VmError::from_history(error, pc))?;
                let replacement = slot.replace(&exhausted, Arc::new(Mutex::new(replacement)));
                let root = replacement.lock().pair.root;
                active.instance = replacement;
                active.cursor = BatchCursor {
                    consumed: 0,
                    residual: root,
                };
                active.retried = true;
                Ok(InstructionOutcome::Repeat)
            }
            Err(error) => Err(VmError::from_history(error, pc)),
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::unwrap_used,
        clippy::indexing_slicing,
        clippy::arithmetic_side_effects
    )]

    use super::graph::Storage as _;
    use super::kernel::{Primitive, TestView};
    #[cfg(feature = "cache")]
    use super::progress::WorkCounters;
    use super::*;
    use crate::languages::history_table::compile;
    use crate::rvm::program::Program;
    use crate::rvm::vm::history_tables::graph::ArenaLifetimeCounts;
    use crate::rvm::vm::history_tables::kernel::MAX_GRAPH_BYTES;
    use crate::rvm::vm::ExecutionMode;
    use alloc::string::ToString as _;
    use lru::LruCache;
    use serde_json::{json, Value as Json};

    fn program(request: &str, tail: &str, batch: u32) -> Arc<Program> {
        let policy = alloc::format!(
            r#"{{"rules":[{{"mode":"require","request":{request},"history":{tail}}}]}}"#
        );
        compile(&Value::from_json_str(&policy).unwrap(), batch).unwrap()
    }

    fn event(store: &HistoryStore, principal: &str, action: &str) -> Event {
        Event {
            principal: store.intern_principal(principal).unwrap(),
            action: store.intern_action(action).unwrap(),
            resource: store.intern_resource("doc").unwrap(),
        }
    }

    fn vm(store: &Arc<HistoryStore>, history: &HistoryHandle, program: &Arc<Program>) -> RegoVM {
        let mut vm = RegoVM::new();
        vm.load_program(Arc::clone(program));
        vm.attach_history(Arc::clone(store)).unwrap();
        vm.set_history_input(history.clone(), event(store, "alice", "release"))
            .unwrap();
        vm
    }

    fn lazy_instance(vm: &RegoVM) -> Arc<Mutex<RuleRuntime>> {
        let table = &vm.history_attachment.as_ref().unwrap().tables[0];
        let slot = &table.rules[0];
        let instance = Arc::new(Mutex::new(
            RuleRuntime::new(
                &slot.template,
                false,
                &mut ExecutionTimer::new(None),
                &mut ObservationWorld,
            )
            .unwrap(),
        ));
        *slot.current.lock() = Arc::clone(&instance);
        instance
    }

    const ACTOR: &str = r#"{"object":{"principal":{"var":"actor"}}}"#;

    fn decide(
        vm: &mut RegoVM,
        store: &HistoryStore,
        history: &HistoryHandle,
        events: &[Event],
        request: Event,
    ) -> Value {
        store.truncate(history, 0).unwrap();
        store.append(history, events).unwrap();
        vm.set_history_input(history.clone(), request).unwrap();
        vm.execute_entry_point_by_name("decide").unwrap()
    }

    fn equality() -> Json {
        json!({"test": {"eq": {"path": ["principal"], "term": {"var": "actor"}}}})
    }

    #[test]
    fn fixed_bindings_share_classes_only_when_truth_words_match() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let program = program(ACTOR, &json!({"star": equality()}).to_string(), 256);
        let mut vm = vm(&store, &history, &program);
        vm.set_execution_mode(ExecutionMode::RunToCompletion);
        let instance = lazy_instance(&vm);
        instance.lock().pair.work.skip_guards = true;
        let alice = event(&store, "alice", "read");
        let bob = event(&store, "bob", "read");
        assert_eq!(
            decide(&mut vm, &store, &history, &[alice, alice], alice),
            Value::Null
        );
        {
            let runtime = instance.lock();
            assert_eq!(runtime.pair.work.successor_misses, 1);
            assert_eq!(runtime.pair.work.successor_hits, 1);
        }
        assert_eq!(decide(&mut vm, &store, &history, &[bob], bob), Value::Null);
        assert_eq!(instance.lock().pair.work.successor_hits, 2);
        assert_eq!(
            decide(&mut vm, &store, &history, &[bob], alice),
            Value::from(0_usize)
        );
        let runtime = instance.lock();
        assert_eq!(runtime.pair.work.successor_misses, 2);
        assert_eq!(runtime.pair.successors.as_ref().map(LruCache::len), Some(2));
    }

    #[test]
    fn negative_tests_cache_one_positive_equality_without_presence_atoms() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let program = program(
            ACTOR,
            &json!({"test": {"neq": {
                "path": ["principal"], "term": {"value": "alice"}
            }}})
            .to_string(),
            256,
        );
        let mut vm = vm(&store, &history, &program);
        vm.set_execution_mode(ExecutionMode::RunToCompletion);
        let instance = lazy_instance(&vm);
        let alice = event(&store, "alice", "read");
        let bob = event(&store, "bob", "read");
        assert_eq!(
            decide(&mut vm, &store, &history, &[bob], alice),
            Value::Null
        );
        {
            let runtime = instance.lock();
            let atoms = runtime.pair.atoms.iter().flatten().next().unwrap();
            assert_eq!(atoms.ids().len(), 1);
            for id in atoms.ids() {
                assert!(matches!(
                    runtime.pair.store.storage.test(*id).unwrap(),
                    TestView::Atom {
                        primitive: Primitive::Eq { .. },
                        positive: true
                    }
                ));
            }
        }
        assert_eq!(
            decide(&mut vm, &store, &history, &[alice], alice),
            Value::from(0_usize)
        );
        assert_eq!(
            instance.lock().pair.successors.as_ref().map(LruCache::len),
            Some(2)
        );
    }

    #[test]
    fn absorbing_states_skip_event_caches() {
        for (regex, expected, visits, count) in [
            (json!({"test": true}), Value::Null, 1, 1),
            (json!({"all": true}), Value::Null, 0, 2),
            (json!({"empty": true}), Value::from(0_usize), 0, 2),
        ] {
            let store = Arc::new(HistoryStore::new());
            let history = store.new_history().unwrap();
            let program = program(ACTOR, &regex.to_string(), 256);
            let mut vm = vm(&store, &history, &program);
            vm.set_execution_mode(ExecutionMode::RunToCompletion);
            let instance = lazy_instance(&vm);
            let alice = event(&store, "alice", "read");
            assert_eq!(
                decide(&mut vm, &store, &history, &[alice, alice][..count], alice),
                expected
            );
            let runtime = instance.lock();
            assert_eq!(runtime.pair.work.events, visits);
            assert!(runtime.pair.successors.is_none());
            assert!(runtime.pair.atoms.is_empty());
        }
    }

    #[test]
    fn derivative_cycles_keep_distinct_residuals_and_stabilize() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let program = program(
            ACTOR,
            &json!({"star": {"concat": [
                {"test": {"eq": {"path": ["principal"], "term": {"value": "alice"}}}},
                {"test": {"eq": {"path": ["principal"], "term": {"value": "bob"}}}}
            ]}})
            .to_string(),
            256,
        );
        let mut vm = vm(&store, &history, &program);
        vm.set_execution_mode(ExecutionMode::RunToCompletion);
        let instance = lazy_instance(&vm);
        let alice = event(&store, "alice", "read");
        let bob = event(&store, "bob", "read");
        assert_eq!(
            decide(&mut vm, &store, &history, &[alice, bob], alice),
            Value::Null
        );
        let before = {
            let runtime = instance.lock();
            (
                runtime.pair.store.bytes,
                runtime.pair.derivatives.len(),
                runtime.pair.atoms.len(),
            )
        };
        for _ in 0..64 {
            assert_eq!(
                decide(&mut vm, &store, &history, &[alice, bob], alice),
                Value::Null
            );
        }
        {
            let runtime = instance.lock();
            assert_eq!(
                (
                    runtime.pair.store.bytes,
                    runtime.pair.derivatives.len(),
                    runtime.pair.atoms.len()
                ),
                before
            );
        }
        assert_eq!(
            decide(&mut vm, &store, &history, &[alice], alice),
            Value::from(0_usize)
        );
        assert_eq!(
            decide(&mut vm, &store, &history, &[alice, alice], alice),
            Value::from(0_usize)
        );
        assert_eq!(
            decide(&mut vm, &store, &history, &[alice, bob, alice, bob], alice),
            Value::Null
        );
    }

    #[test]
    fn self_loop_guards_skip_full_event_classes() {
        for (skip_guards, hits, classes) in [(false, 3, 1), (true, 0, 4)] {
            let store = Arc::new(HistoryStore::new());
            let history = store.new_history().unwrap();
            let program = program(
                ACTOR,
                &json!({"concat": [{"all": true}, equality()]}).to_string(),
                256,
            );
            let mut vm = vm(&store, &history, &program);
            vm.set_execution_mode(ExecutionMode::RunToCompletion);
            let instance = lazy_instance(&vm);
            instance.lock().pair.work.skip_guards = skip_guards;
            let alice = event(&store, "alice", "read");
            let bob = event(&store, "bob", "read");
            assert_eq!(
                decide(&mut vm, &store, &history, &[bob, bob, bob, alice], alice),
                Value::Null
            );
            let runtime = instance.lock();
            assert_eq!(runtime.pair.work.guard_hits, hits);
            assert_eq!(runtime.pair.work.event_classes, classes);
        }
    }

    #[test]
    fn folding_batches_matches_whole_word_without_answering_prefixes() {
        for batch in [1, 2, 3] {
            let store = Arc::new(HistoryStore::new());
            let history = store.new_history().unwrap();
            let program = program(
                ACTOR,
                &json!({"concat": [equality(), equality(), equality()]}).to_string(),
                batch,
            );
            let mut vm = vm(&store, &history, &program);
            vm.set_execution_mode(ExecutionMode::RunToCompletion);
            let alice = event(&store, "alice", "read");
            let bob = event(&store, "bob", "read");
            for events in [[alice, alice, alice], [alice, bob, alice]] {
                let whole = decide(&mut vm, &store, &history, &events, alice);
                assert_eq!(
                    whole,
                    if events[1] == alice {
                        Value::Null
                    } else {
                        Value::from(0_usize)
                    }
                );
                for split in 0..=events.len() {
                    let prefix = decide(&mut vm, &store, &history, &events[..split], alice);
                    assert_eq!(
                        prefix,
                        if split == 3 {
                            whole.clone()
                        } else {
                            Value::from(0_usize)
                        }
                    );
                    store.append(&history, &events[split..]).unwrap();
                    vm.set_history_input(history.clone(), alice).unwrap();
                    assert_eq!(vm.execute_entry_point_by_name("decide").unwrap(), whole);
                }
            }
            let star_program =
                super::tests::program(ACTOR, &json!({"star": equality()}).to_string(), batch);
            let mut star_vm = super::tests::vm(&store, &history, &star_program);
            star_vm.set_execution_mode(ExecutionMode::RunToCompletion);
            assert_eq!(
                decide(&mut star_vm, &store, &history, &[alice], alice),
                Value::Null
            );
            assert_eq!(
                decide(&mut star_vm, &store, &history, &[alice, bob], alice),
                Value::from(0_usize)
            );
        }
    }

    #[cfg(feature = "cache")]
    #[test]
    fn precompile_keeps_the_typed_lazy_language() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let regex =
            json!({"concat": [{"all": true}, equality(), {"star": equality()}]}).to_string();
        let eager_program = program(ACTOR, &regex, 256);
        let lazy_program = program(ACTOR, &regex, 256);
        let mut eager = vm(&store, &history, &eager_program);
        let mut lazy = vm(&store, &history, &lazy_program);
        eager.set_execution_mode(ExecutionMode::RunToCompletion);
        lazy.set_execution_mode(ExecutionMode::RunToCompletion);
        let eager_instance = Arc::clone(
            &eager.history_attachment.as_ref().unwrap().tables[0].rules[0]
                .current
                .lock(),
        );
        let _lazy_instance = lazy_instance(&lazy);
        eager_instance.lock().pair.work = WorkCounters::default();
        let alice = event(&store, "alice", "read");
        let bob = event(&store, "bob", "read");
        for (events, expected) in [
            (&[][..], Value::from(0_usize)),
            (&[alice][..], Value::Null),
            (&[bob, alice, alice][..], Value::Null),
            (&[alice, bob][..], Value::from(0_usize)),
        ] {
            assert_eq!(
                decide(&mut eager, &store, &history, events, alice),
                expected
            );
            assert_eq!(decide(&mut lazy, &store, &history, events, alice), expected);
        }
        let runtime = eager_instance.lock();
        assert_eq!(runtime.pair.work.derivative_misses, 0);
        assert_eq!(runtime.pair.work.successor_misses, 0);
    }

    #[test]
    fn event_class_lru_keeps_its_256_entry_ceiling() {
        let tests: Vec<_> = (0..17)
            .flat_map(|id| {
                ["principal", "action"].map(|field| {
                    json!({"eq": {
                        "path": [field], "term": {"value": alloc::format!("identity-{id}")}
                    }})
                })
            })
            .collect();
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let program = program(ACTOR, &json!({"test": {"or": tests}}).to_string(), 256);
        let mut vm = vm(&store, &history, &program);
        vm.set_execution_mode(ExecutionMode::RunToCompletion);
        let instance = lazy_instance(&vm);
        let mut first = None;
        for principal in 0..17 {
            for action in 0..17 {
                let event = event(
                    &store,
                    &alloc::format!("identity-{principal}"),
                    &alloc::format!("identity-{action}"),
                );
                first.get_or_insert(event);
                assert_eq!(
                    decide(&mut vm, &store, &history, &[event], event),
                    Value::Null
                );
            }
        }
        {
            let runtime = instance.lock();
            assert_eq!(runtime.pair.work.successor_misses, 289);
            assert_eq!(
                runtime.pair.successors.as_ref().map(LruCache::len),
                Some(256)
            );
        }
        let first = first.unwrap();
        assert_eq!(
            decide(&mut vm, &store, &history, &[first], first),
            Value::Null
        );
        let runtime = instance.lock();
        assert_eq!(runtime.pair.work.successor_misses, 290);
        assert_eq!(
            runtime.pair.successors.as_ref().map(LruCache::len),
            Some(256)
        );
    }

    #[cfg(feature = "cache")]
    #[test]
    fn precompile_leaves_wide_typed_transitions_lazy() {
        for (count, entries) in [(9, None), (8, Some(256))] {
            let tests: Vec<_> = (0..count)
                .map(|id| {
                    json!({"eq": {
                        "path": ["principal"], "term": {"value": alloc::format!("identity-{id}")}
                    }})
                })
                .collect();
            let store = Arc::new(HistoryStore::new());
            let history = store.new_history().unwrap();
            let program = program(ACTOR, &json!({"test": {"or": tests}}).to_string(), 256);
            let mut vm = vm(&store, &history, &program);
            vm.set_execution_mode(ExecutionMode::RunToCompletion);
            let instance = Arc::clone(
                &vm.history_attachment.as_ref().unwrap().tables[0].rules[0]
                    .current
                    .lock(),
            );
            assert_eq!(
                instance.lock().pair.successors.as_ref().map(LruCache::len),
                entries
            );
            let matching = event(&store, "identity-0", "read");
            let nonmatching = event(&store, "outside", "read");
            assert_eq!(
                decide(&mut vm, &store, &history, &[matching], matching),
                Value::Null
            );
            assert_eq!(
                decide(&mut vm, &store, &history, &[nonmatching], nonmatching),
                Value::from(0_usize)
            );
        }
    }

    #[test]
    fn compiled_pair_uses_send_dependencies() {
        fn assert_send<T: Send>() {}
        assert_send::<CompiledPair>();
    }

    #[test]
    fn batch_cursor_ends_and_retained_prefix_are_exact() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let event = event(&store, "alice", "edit");
        store.append(&history, &[event; 7]).unwrap();
        let mut vm = vm(
            &store,
            &history,
            &program(r#"{"any":true}"#, r#"{"all":true}"#, 3),
        );
        let instance = lazy_instance(&vm);
        for expected in [3, 6] {
            assert!(matches!(
                vm.execute_history_step(0).unwrap(),
                InstructionOutcome::Repeat
            ));
            assert_eq!(
                vm.history_active_rule.as_ref().unwrap().cursor.consumed,
                expected
            );
            assert_eq!(instance.lock().cursors[0].consumed, expected);
        }
        assert!(matches!(
            vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert!(vm.history_active_rule.is_none());
        let mut graph = instance.lock();
        let latest = graph.cursors[0];
        assert_eq!(latest.consumed, 7);
        let root = graph.pair.root;
        graph.publish(HistoryCursor {
            consumed: 1,
            residual: root,
            ..latest
        });
        assert_eq!(graph.cursors[0].consumed, 7);
        assert_eq!(graph.cursors[0].residual, latest.residual);
    }

    #[test]
    fn failed_batch_and_final_answer_never_publish() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let vm = vm(
            &store,
            &history,
            &program(r#"{"any":true}"#, r#"{"epsilon":true}"#, 3),
        );
        let instance = lazy_instance(&vm);
        let mut runtime = instance.lock();
        let mut cursor = BatchCursor {
            consumed: 0,
            residual: runtime.pair.root,
        };
        let before = cursor;
        let error = cursor
            .advance(
                &mut runtime.pair,
                &[],
                &Bindings([0; 3]),
                1,
                3,
                &mut ExecutionTimer::new(None),
                &mut ObservationWorld,
            )
            .unwrap_err();
        assert!(matches!(error, HistoryError::Invariant { .. }));
        assert_eq!(cursor.consumed, before.consumed);
        assert_eq!(cursor.residual, before.residual);
        assert!(runtime.cursors.is_empty());

        drop(runtime);
        let event = event(&store, "alice", "edit");
        store.append(&history, &[event; 2]).unwrap();
        let mut final_vm = super::tests::vm(
            &store,
            &history,
            &program(r#"{"any":true}"#, r#"{"all":true}"#, 1),
        );
        let final_instance = lazy_instance(&final_vm);
        assert!(matches!(
            final_vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        let entry = final_vm.history_active_rule.as_ref().unwrap().cursor;
        let retained = final_instance.lock().cursors[0];
        final_instance.lock().pair.work.fail_answer_checkpoint = true;
        let final_error = final_vm.execute_history_step(0).unwrap_err();
        assert!(matches!(final_error, VmError::TimeLimitExceeded { .. }));
        let final_cursor = final_vm.history_active_rule.as_ref().unwrap().cursor;
        assert_eq!(final_cursor.consumed, entry.consumed);
        assert_eq!(final_cursor.residual, entry.residual);
        assert_eq!(final_instance.lock().cursors[0].consumed, retained.consumed);
        assert_eq!(final_instance.lock().cursors[0].residual, retained.residual);
        final_instance.lock().pair.work.fail_answer_checkpoint = false;
        assert!(matches!(
            final_vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert_eq!(final_instance.lock().cursors[0].consumed, 2);
    }

    const THREE_ACTIONS: &str = r#"{"concat":[
        {"test":{"eq":{"path":["action"],"term":{"value":"a"}}}},
        {"test":{"eq":{"path":["action"],"term":{"value":"b"}}}},
        {"test":{"eq":{"path":["action"],"term":{"value":"c"}}}}
    ]}"#;

    #[test]
    fn graph_replacement_keeps_two_old_continuations_valid() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        store
            .append(
                &history,
                &[
                    event(&store, "alice", "a"),
                    event(&store, "alice", "b"),
                    event(&store, "alice", "c"),
                ],
            )
            .unwrap();
        let program = program(r#"{"any":true}"#, THREE_ACTIONS, 1);
        let mut first = vm(&store, &history, &program);
        let old = lazy_instance(&first);
        let mut second = vm(&store, &history, &program);
        let counts = Arc::new(ArenaLifetimeCounts::default());
        old.lock()
            .pair
            .store
            .storage
            .track_lifetime(Arc::clone(&counts))
            .unwrap();
        assert!(matches!(
            first.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert!(matches!(
            second.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert_eq!(
            first.history_active_rule.as_ref().unwrap().cursor.consumed,
            1
        );
        assert_eq!(
            second.history_active_rule.as_ref().unwrap().cursor.consumed,
            2
        );
        assert!(Arc::ptr_eq(
            &first.history_active_rule.as_ref().unwrap().instance,
            &old
        ));
        assert!(Arc::ptr_eq(
            &second.history_active_rule.as_ref().unwrap().instance,
            &old
        ));
        let previous_bytes = old.lock().pair.store.bytes;
        old.lock().pair.store.bytes = MAX_GRAPH_BYTES;
        assert!(matches!(
            second.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        let replacement = Arc::clone(&second.history_active_rule.as_ref().unwrap().instance);
        assert!(!Arc::ptr_eq(&replacement, &old));
        assert_eq!(
            second.history_active_rule.as_ref().unwrap().cursor.consumed,
            0
        );
        assert!(second.history_active_rule.as_ref().unwrap().retried);
        assert_eq!(counts.snapshot(), (6, 0));

        old.lock().pair.store.bytes = previous_bytes;
        assert!(matches!(
            first.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert!(matches!(
            first.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert_eq!(counts.snapshot(), (6, 0));
        drop(old);
        assert_eq!(counts.snapshot(), (6, 6));
        for expected in [1, 2] {
            assert!(matches!(
                second.execute_history_step(0).unwrap(),
                InstructionOutcome::Repeat
            ));
            assert_eq!(
                second.history_active_rule.as_ref().unwrap().cursor.consumed,
                expected
            );
        }
        assert!(matches!(
            second.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert_eq!(replacement.lock().cursors[0].consumed, 3);
    }

    #[test]
    fn graph_recovery_has_one_retry_and_losing_replacements_drop() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        store
            .append(
                &history,
                &[
                    event(&store, "alice", "a"),
                    event(&store, "alice", "b"),
                    event(&store, "alice", "c"),
                ],
            )
            .unwrap();
        let program = program(r#"{"any":true}"#, THREE_ACTIONS, 1);
        let mut vm = vm(&store, &history, &program);
        let old = lazy_instance(&vm);
        old.lock().pair.store.bytes = MAX_GRAPH_BYTES;
        assert!(matches!(
            vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        let winner = Arc::clone(&vm.history_active_rule.as_ref().unwrap().instance);
        let table = Arc::clone(&vm.history_attachment.as_ref().unwrap().tables[0]);
        let slot = &table.rules[0];
        let mut losing = RuleRuntime::new(
            &slot.template,
            false,
            &mut ExecutionTimer::new(None),
            &mut ObservationWorld,
        )
        .unwrap();
        let counts = Arc::new(ArenaLifetimeCounts::default());
        losing
            .pair
            .store
            .storage
            .track_lifetime(Arc::clone(&counts))
            .unwrap();
        let selected = slot.replace(&old, Arc::new(Mutex::new(losing)));
        assert!(Arc::ptr_eq(&selected, &winner));
        assert_eq!(counts.snapshot(), (6, 6));
        winner.lock().pair.store.bytes = MAX_GRAPH_BYTES;
        let error = vm.execute_history_step(0).unwrap_err();
        assert!(matches!(
            error,
            VmError::History {
                source: HistoryError::GraphLimit { .. },
                ..
            }
        ));
        assert_eq!(vm.history_active_rule.as_ref().unwrap().cursor.consumed, 0);
        assert!(winner.lock().cursors.is_empty());
    }

    #[test]
    fn table_eviction_reclaims_only_unpinned_graphs() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let event = event(&store, "alice", "edit");
        let first = store
            .table_runtime(&program(r#"{"any":true}"#, r#"{"all":true}"#, 1), 0)
            .unwrap();
        let weak = Arc::downgrade(&first);
        let pinned = Arc::clone(&first.rules[0].current.lock());
        let counts = Arc::new(ArenaLifetimeCounts::default());
        pinned
            .lock()
            .pair
            .store
            .storage
            .track_lifetime(Arc::clone(&counts))
            .unwrap();
        drop(first);
        for _ in 0..17 {
            store
                .table_runtime(&program(r#"{"any":true}"#, r#"{"all":true}"#, 1), 0)
                .unwrap();
        }
        assert!(weak.upgrade().is_none());
        assert_eq!(counts.snapshot(), (6, 0));
        store.append(&history, &[event]).unwrap();
        assert_eq!(store.len(&history).unwrap(), 1);
        assert_eq!(store.intern_action("edit").unwrap(), event.action);
        drop(pinned);
        assert_eq!(counts.snapshot(), (6, 6));
    }

    #[test]
    fn terminal_snapshot_failure_retains_only_successful_batches() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let event = event(&store, "alice", "edit");
        store.append(&history, &[event; 2]).unwrap();
        let mut vm = vm(
            &store,
            &history,
            &program(r#"{"any":true}"#, r#"{"all":true}"#, 1),
        );
        let instance = lazy_instance(&vm);
        assert!(matches!(
            vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert!(matches!(
            vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert_eq!(instance.lock().cursors[0].consumed, 2);
        store.truncate(&history, 0).unwrap();
        let error = vm.finish_history_execution().unwrap_err();
        assert!(matches!(
            error,
            VmError::History {
                source: HistoryError::HistoryChanged {
                    expected: 0,
                    actual: 1
                },
                ..
            }
        ));
        assert!(vm.history_decision.is_none());
        assert!(vm.history_active_rule.is_none());
        assert_eq!(instance.lock().cursors[0].consumed, 2);
        assert_eq!(instance.lock().cursors[0].revision, 0);
    }

    #[test]
    fn retained_cursor_lru_is_bounded_and_keeps_recent_histories() {
        let store = Arc::new(HistoryStore::new());
        let program = program(r#"{"any":true}"#, r#"{"all":true}"#, 3);
        let first = store.new_history().unwrap();
        let initial = vm(&store, &first, &program);
        let instance = lazy_instance(&initial);
        for _ in 0..17 {
            let history = store.new_history().unwrap();
            let mut vm = vm(&store, &history, &program);
            assert!(matches!(
                vm.execute_history_step(0).unwrap(),
                InstructionOutcome::Continue
            ));
        }
        let runtime = instance.lock();
        assert_eq!(runtime.cursors.len(), 16);
        assert_eq!(runtime.cursors[0].history, 17);
        assert_eq!(runtime.cursors[15].history, 2);
        assert!(runtime
            .cursors
            .iter()
            .all(|cursor| cursor.bindings == Bindings([0; 3])));
    }

    #[cfg(feature = "std")]
    #[test]
    fn typed_history_runtime_is_thread_safe() {
        fn send<T: Send>() {}
        fn send_sync<T: Send + Sync>() {}
        send_sync::<HistoryStore>();
        send::<RuleRuntime>();
        send::<RegoVM>();
    }
}
