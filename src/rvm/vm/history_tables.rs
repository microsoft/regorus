// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Bounded typed history steps. A decision pins one revision/prefix and each active
//! rule pins its graph generation; no synchronization guard survives a dispatch.

use super::dispatch::InstructionOutcome;
use super::errors::{Result, VmError};
use super::execution_model::ExecutionState;
use super::machine::RegoVM;
use crate::languages::history_table::limits::RegorusLimits;
use crate::languages::history_table::store::HistoryTableRuntime;
use crate::languages::history_table::{Event, HistoryError, HistoryHandle, HistoryStore};
use crate::rvm::program::Program;
use crate::utils::limits::LimitError;
use crate::value::Value;
use alloc::sync::Arc;
use alloc::vec::Vec;
use history_semantics::runtime::{BatchCursor, RuleRuntime};
use history_store::history::StoredHistory;
use history_store::store::HistoryRecord;
use history_syntax::RuleMode;
use junco_core::kernel::Bindings;
use junco_core::limits::Limits as _;
use junco_core::observation::ObservationWorld;
#[cfg(feature = "std")]
use parking_lot::Mutex;
#[cfg(not(feature = "std"))]
use spin::Mutex;

#[derive(Debug)]
pub(super) struct HistoryAttachment {
    store: Arc<HistoryStore>,
    tables: Vec<Arc<HistoryTableRuntime>>,
}

#[derive(Debug)]
pub(super) struct HistoryDecision {
    record: HistoryRecord,
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

impl HistoryAttachment {
    fn new(
        store: Arc<HistoryStore>,
        program: &Arc<Program>,
    ) -> core::result::Result<Self, HistoryError> {
        let mut tables = Vec::new();
        tables
            .try_reserve_exact(program.history_tables.len())
            .map_err(|_| HistoryError::AllocationFailed)?;
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
        limits: &mut RegorusLimits<'_>,
    ) -> core::result::Result<(), HistoryError> {
        limits.publication_checkpoint()?;
        if stored.revision() != self.revision || stored.len() < self.target_len {
            return Err(HistoryError::HistoryChanged {
                expected: self.revision,
                actual: stored.revision(),
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
        RegorusLimits {
            timer: &mut self.execution_timer,
        }
        .publication_checkpoint()
        .map_err(|error| VmError::from_history(error.into(), self.pc))?;
        let revision = stored.revision();
        let target_len = stored.len();
        drop(stored);
        self.history_decision = Some(HistoryDecision {
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
                .check(
                    &stored,
                    &mut RegorusLimits {
                        timer: &mut self.execution_timer,
                    },
                )
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
                HistoryError::Invariant {
                    message: "history batch_size does not fit usize",
                },
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
                HistoryError::Invariant {
                    message: "history continuation belongs to another instruction",
                },
                pc,
            ));
        }
        let mut world = ObservationWorld;
        let mut limits = RegorusLimits {
            timer: &mut self.execution_timer,
        };
        if self.history_active_rule.is_none() {
            let instance = Arc::clone(&slot.current.lock());
            // Lock graph before history consistently; retain both guards through validation.
            let mut graph = instance.lock();
            let stored = decision.record.read();
            decision
                .check(&stored, &mut limits)
                .map_err(|error| VmError::from_history(error, pc))?;
            let Some(bindings) =
                history_semantics::compile::bindings(&slot.template, &decision.request)
            else {
                return Ok(InstructionOutcome::Continue);
            };
            // Native provenance: this locked record is the staged history, and
            // same-revision observations extend its previously recorded word.
            let cursor = graph.resume_cursor(&bindings, &stored, decision.target_len);
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
            .check(&stored, &mut limits)
            .map_err(|error| VmError::from_history(error, pc))?;
        let outcome = graph.advance_cursor(
            &mut active.cursor,
            &active.bindings,
            &stored,
            decision.target_len,
            batch_size,
            &mut limits,
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
                            RuleMode::Require => !answer,
                            RuleMode::Forbid => answer,
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
                let numeric_store = Arc::clone(graph.store());
                drop(stored);
                drop(graph);
                let replacement = RuleRuntime::new(
                    &numeric_store,
                    &slot.template,
                    false,
                    &mut limits,
                    &mut world,
                )
                .map_err(|error| VmError::from_history(error, pc))?;
                let replacement = slot.replace(&exhausted, Arc::new(Mutex::new(replacement)));
                let cursor = replacement.lock().root_cursor();
                active.instance = replacement;
                active.cursor = cursor;
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

    use super::*;
    use crate::languages::history_table::{
        compile, AtomPattern, Comparison, ComponentPattern, Head, RegexExpr, Rule, RuleMode,
        SourceEvent, TestExpr,
    };
    use crate::rvm::program::Program;
    use crate::rvm::vm::ExecutionMode;
    use crate::utils::limits::ExecutionTimer;
    use junco_core::limits::MAX_GRAPH_BYTES;

    fn program<'a>(
        head: Head<SourceEvent<'a>>,
        tail: RegexExpr<SourceEvent<'a>>,
        batch: u32,
    ) -> Arc<Program> {
        compile(&[Rule::new(RuleMode::Require, head, tail)], batch).unwrap()
    }

    fn any_head<'a>() -> Head<SourceEvent<'a>> {
        Head::new(
            ComponentPattern::variable("_principal"),
            ComponentPattern::variable("_action"),
            ComponentPattern::variable("_resource"),
        )
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
                &history_store::store::HistoryStore::global(),
                &slot.template,
                false,
                &mut RegorusLimits {
                    timer: &mut ExecutionTimer::new(None),
                },
                &mut ObservationWorld,
            )
            .unwrap(),
        ));
        *slot.current.lock() = Arc::clone(&instance);
        instance
    }

    fn actor_head<'a>() -> Head<SourceEvent<'a>> {
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::variable("_action"),
            ComponentPattern::variable("_resource"),
        )
    }

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

    fn equality<'a>() -> RegexExpr<SourceEvent<'a>> {
        RegexExpr::test(TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Principal(ComponentPattern::variable("actor")),
        ))
    }

    #[test]
    fn fixed_bindings_share_classes_only_when_truth_words_match() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let program = program(actor_head(), RegexExpr::star(equality()), 256);
        let mut vm = vm(&store, &history, &program);
        vm.set_execution_mode(ExecutionMode::RunToCompletion);
        let instance = lazy_instance(&vm);
        instance.lock().set_skip_guards(true);
        let alice = event(&store, "alice", "read");
        let bob = event(&store, "bob", "read");
        assert_eq!(
            decide(&mut vm, &store, &history, &[alice, alice], alice),
            Value::Null
        );
        {
            let runtime = instance.lock();
            assert_eq!(runtime.work_counters().successor_misses, 1);
            assert_eq!(runtime.work_counters().successor_hits, 1);
        }
        assert_eq!(decide(&mut vm, &store, &history, &[bob], bob), Value::Null);
        assert_eq!(instance.lock().work_counters().successor_hits, 2);
        assert_eq!(
            decide(&mut vm, &store, &history, &[bob], alice),
            Value::from(0_usize)
        );
        let runtime = instance.lock();
        assert_eq!(runtime.work_counters().successor_misses, 2);
    }

    #[test]
    fn negative_tests_cache_one_positive_equality_without_presence_atoms() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let program = program(
            actor_head(),
            RegexExpr::test(TestExpr::atom(
                Comparison::Neq,
                AtomPattern::Principal(ComponentPattern::constant("alice")),
            )),
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
        assert_eq!(
            decide(&mut vm, &store, &history, &[alice], alice),
            Value::from(0_usize)
        );
        assert_eq!(instance.lock().work_counters().successor_misses, 2);
    }

    #[test]
    fn absorbing_states_skip_event_caches() {
        for (regex, expected, visits, count) in [
            (RegexExpr::test(TestExpr::True), Value::Null, 1, 1),
            (RegexExpr::All, Value::Null, 0, 2),
            (RegexExpr::Empty, Value::from(0_usize), 0, 2),
        ] {
            let store = Arc::new(HistoryStore::new());
            let history = store.new_history().unwrap();
            let program = program(actor_head(), regex, 256);
            let mut vm = vm(&store, &history, &program);
            vm.set_execution_mode(ExecutionMode::RunToCompletion);
            let instance = lazy_instance(&vm);
            let alice = event(&store, "alice", "read");
            assert_eq!(
                decide(&mut vm, &store, &history, &[alice, alice][..count], alice),
                expected
            );
            let runtime = instance.lock();
            assert_eq!(runtime.work_counters().events, visits);
            assert_eq!(runtime.work_counters().successor_misses, 0);
            assert_eq!(runtime.work_counters().event_classes, 0);
        }
    }

    #[test]
    fn derivative_cycles_keep_distinct_residuals_and_stabilize() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let program = program(
            actor_head(),
            RegexExpr::star(RegexExpr::concat(["alice", "bob"].map(|principal| {
                RegexExpr::test(TestExpr::atom(
                    Comparison::Eq,
                    AtomPattern::Principal(ComponentPattern::constant(principal)),
                ))
            }))),
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
            runtime.work_counters().derivative_misses
        };
        for _ in 0..64 {
            assert_eq!(
                decide(&mut vm, &store, &history, &[alice, bob], alice),
                Value::Null
            );
        }
        {
            let runtime = instance.lock();
            assert_eq!(runtime.work_counters().derivative_misses, before);
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
                actor_head(),
                RegexExpr::concat([RegexExpr::All, equality()]),
                256,
            );
            let mut vm = vm(&store, &history, &program);
            vm.set_execution_mode(ExecutionMode::RunToCompletion);
            let instance = lazy_instance(&vm);
            instance.lock().set_skip_guards(skip_guards);
            let alice = event(&store, "alice", "read");
            let bob = event(&store, "bob", "read");
            assert_eq!(
                decide(&mut vm, &store, &history, &[bob, bob, bob, alice], alice),
                Value::Null
            );
            let runtime = instance.lock();
            assert_eq!(runtime.work_counters().guard_hits, hits);
            assert_eq!(runtime.work_counters().event_classes, classes);
        }
    }

    #[test]
    fn folding_batches_matches_whole_word_without_answering_prefixes() {
        for batch in [1, 2, 3] {
            let store = Arc::new(HistoryStore::new());
            let history = store.new_history().unwrap();
            let program = program(
                actor_head(),
                RegexExpr::concat([equality(), equality(), equality()]),
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
                super::tests::program(actor_head(), RegexExpr::star(equality()), batch);
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

    #[test]
    fn retained_residuals_avoid_replay_without_changing_answers() {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let store = Arc::new(HistoryStore::new());
            let history = store.new_history().unwrap();
            let matching = event(&store, "alice", "edit");
            let rejecting = event(&store, "alice", "read");
            store.append(&history, &[matching; 256]).unwrap();
            let program = program(
                any_head(),
                RegexExpr::star(RegexExpr::test(TestExpr::atom(
                    Comparison::Eq,
                    AtomPattern::Action(ComponentPattern::constant("edit")),
                ))),
                64,
            );
            let mut vm = vm(&store, &history, &program);
            vm.set_execution_mode(mode);
            let instance = lazy_instance(&vm);
            assert_eq!(
                vm.execute_entry_point_by_name("decide").unwrap(),
                Value::Null
            );

            let mut compare = |length, reused_events, expected: Value| {
                for retain in [true, false] {
                    {
                        let mut runtime = instance.lock();
                        if !retain {
                            runtime.clear_cursors();
                        }
                        runtime.reset_work_events();
                    }
                    assert_eq!(vm.execute_entry_point_by_name("decide").unwrap(), expected);
                    assert_eq!(
                        instance.lock().work_counters().events,
                        if retain { reused_events } else { length },
                    );
                }
            };
            compare(256, 0, Value::Null);
            store.append(&history, &[matching]).unwrap();
            compare(257, 1, Value::Null);
            store.append(&history, &[rejecting]).unwrap();
            compare(258, 1, Value::from(0_usize));
        }
    }

    #[cfg(feature = "cache")]
    #[test]
    fn precompile_keeps_the_typed_lazy_language() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let regex = RegexExpr::concat([RegexExpr::All, equality(), RegexExpr::star(equality())]);
        let eager_program = program(actor_head(), regex.clone(), 256);
        let lazy_program = program(actor_head(), regex, 256);
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
        eager_instance.lock().reset_work_counters();
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
        assert_eq!(runtime.work_counters().derivative_misses, 0);
        assert_eq!(runtime.work_counters().successor_misses, 0);
    }

    #[test]
    fn event_class_lru_keeps_its_256_entry_ceiling() {
        let identities: Vec<_> = (0..17).map(|id| alloc::format!("identity-{id}")).collect();
        let tests = identities.iter().flat_map(|id| {
            [
                TestExpr::atom(
                    Comparison::Eq,
                    AtomPattern::Principal(ComponentPattern::constant(id.as_str())),
                ),
                TestExpr::atom(
                    Comparison::Eq,
                    AtomPattern::Action(ComponentPattern::constant(id.as_str())),
                ),
            ]
        });
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let program = program(actor_head(), RegexExpr::test(TestExpr::or(tests)), 256);
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
            assert_eq!(runtime.work_counters().successor_misses, 289);
        }
        let first = first.unwrap();
        assert_eq!(
            decide(&mut vm, &store, &history, &[first], first),
            Value::Null
        );
        let runtime = instance.lock();
        assert_eq!(runtime.work_counters().successor_misses, 290);
    }

    #[cfg(feature = "cache")]
    #[test]
    fn precompile_leaves_wide_typed_transitions_lazy() {
        for count in [9, 8] {
            let identities: Vec<_> = (0..count)
                .map(|id| alloc::format!("identity-{id}"))
                .collect();
            let tests = identities.iter().map(|id| {
                TestExpr::atom(
                    Comparison::Eq,
                    AtomPattern::Principal(ComponentPattern::constant(id.as_str())),
                )
            });
            let store = Arc::new(HistoryStore::new());
            let history = store.new_history().unwrap();
            let program = program(actor_head(), RegexExpr::test(TestExpr::or(tests)), 256);
            let mut vm = vm(&store, &history, &program);
            vm.set_execution_mode(ExecutionMode::RunToCompletion);
            let instance = Arc::clone(
                &vm.history_attachment.as_ref().unwrap().tables[0].rules[0]
                    .current
                    .lock(),
            );
            instance.lock().reset_work_counters();
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
            assert_eq!(
                instance.lock().work_counters().successor_misses == 0,
                count == 8
            );
        }
    }

    #[test]
    fn compiled_runtime_uses_send_dependencies() {
        fn assert_send<T: Send>() {}
        assert_send::<RuleRuntime>();
    }

    #[test]
    fn batch_cursor_ends_and_retained_prefix_are_exact() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let event = event(&store, "alice", "edit");
        store.append(&history, &[event; 7]).unwrap();
        let program = program(any_head(), RegexExpr::All, 3);
        let mut first = vm(&store, &history, &program);
        let instance = lazy_instance(&first);
        assert!(matches!(
            first.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert_eq!(
            first
                .history_active_rule
                .as_ref()
                .unwrap()
                .cursor
                .consumed(),
            3
        );
        assert_eq!(instance.lock().cursor_positions()[0].3, 3);
        let mut second = vm(&store, &history, &program);
        assert!(matches!(
            second.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert_eq!(
            second
                .history_active_rule
                .as_ref()
                .unwrap()
                .cursor
                .consumed(),
            6
        );
        assert!(matches!(
            second.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert_eq!(instance.lock().cursor_positions()[0].3, 7);
        // A slower decision cannot replace the shared longer committed prefix.
        assert!(matches!(
            first.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert_eq!(
            first
                .history_active_rule
                .as_ref()
                .unwrap()
                .cursor
                .consumed(),
            6
        );
        assert_eq!(instance.lock().cursor_positions()[0].3, 7);
        assert!(matches!(
            first.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert!(first.history_active_rule.is_none());
        assert_eq!(instance.lock().cursor_positions()[0].3, 7);
    }

    #[test]
    fn failed_batch_and_final_answer_never_publish() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let mut empty_vm = vm(
            &store,
            &history,
            &program(any_head(), RegexExpr::Epsilon, 3),
        );
        let empty_instance = lazy_instance(&empty_vm);
        empty_instance.lock().set_answer_checkpoint_failure(true);
        let pc = empty_vm.pc;
        assert!(
            matches!(empty_vm.execute_history_step(0).unwrap_err(), VmError::TimeLimitExceeded { pc: actual, .. } if actual == pc)
        );
        assert_eq!(
            empty_vm
                .history_active_rule
                .as_ref()
                .unwrap()
                .cursor
                .consumed(),
            0
        );
        assert!(empty_instance.lock().cursor_positions().is_empty());
        empty_instance.lock().set_answer_checkpoint_failure(false);
        assert!(matches!(
            empty_vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert_eq!(empty_instance.lock().cursor_positions()[0].3, 0);

        let event = event(&store, "alice", "edit");
        store.append(&history, &[event; 2]).unwrap();
        let mut final_vm = vm(&store, &history, &program(any_head(), RegexExpr::All, 1));
        let final_instance = lazy_instance(&final_vm);
        assert!(matches!(
            final_vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        let entry = final_vm.history_active_rule.as_ref().unwrap().cursor;
        let retained = final_instance.lock().cursor_positions();
        final_instance.lock().set_answer_checkpoint_failure(true);
        let final_pc = final_vm.pc;
        assert!(
            matches!(final_vm.execute_history_step(0).unwrap_err(), VmError::TimeLimitExceeded { pc: actual, .. } if actual == final_pc)
        );
        let final_cursor = final_vm.history_active_rule.as_ref().unwrap().cursor;
        assert_eq!(final_cursor.consumed(), entry.consumed());
        assert_eq!(final_instance.lock().cursor_positions(), retained);
        final_instance.lock().set_answer_checkpoint_failure(false);
        assert!(matches!(
            final_vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert_eq!(final_instance.lock().cursor_positions()[0].3, 2);
    }

    fn three_actions<'a>() -> RegexExpr<SourceEvent<'a>> {
        RegexExpr::concat(["a", "b", "c"].map(|action| {
            RegexExpr::test(TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Action(ComponentPattern::constant(action)),
            ))
        }))
    }

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
        let program = program(any_head(), three_actions(), 1);
        let mut first = vm(&store, &history, &program);
        let old = lazy_instance(&first);
        let mut second = vm(&store, &history, &program);
        let old_weak = Arc::downgrade(&old);
        assert!(matches!(
            first.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert!(matches!(
            second.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert_eq!(
            first
                .history_active_rule
                .as_ref()
                .unwrap()
                .cursor
                .consumed(),
            1
        );
        assert_eq!(
            second
                .history_active_rule
                .as_ref()
                .unwrap()
                .cursor
                .consumed(),
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
        let previous_bytes = old.lock().replace_graph_byte_pressure(MAX_GRAPH_BYTES);
        assert!(matches!(
            second.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        let replacement = Arc::clone(&second.history_active_rule.as_ref().unwrap().instance);
        assert!(!Arc::ptr_eq(&replacement, &old));
        assert_eq!(
            second
                .history_active_rule
                .as_ref()
                .unwrap()
                .cursor
                .consumed(),
            0
        );
        assert!(second.history_active_rule.as_ref().unwrap().retried);
        assert!(old_weak.upgrade().is_some());

        old.lock().replace_graph_byte_pressure(previous_bytes);
        assert!(matches!(
            first.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert!(matches!(
            first.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert!(old_weak.upgrade().is_some());
        drop(old);
        assert!(old_weak.upgrade().is_none());
        for expected in [1, 2] {
            assert!(matches!(
                second.execute_history_step(0).unwrap(),
                InstructionOutcome::Repeat
            ));
            assert_eq!(
                second
                    .history_active_rule
                    .as_ref()
                    .unwrap()
                    .cursor
                    .consumed(),
                expected
            );
        }
        assert!(matches!(
            second.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert_eq!(replacement.lock().cursor_positions()[0].3, 3);
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
        let program = program(any_head(), three_actions(), 1);
        let mut vm = vm(&store, &history, &program);
        let old = lazy_instance(&vm);
        old.lock().replace_graph_byte_pressure(MAX_GRAPH_BYTES);
        assert!(matches!(
            vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        let winner = Arc::clone(&vm.history_active_rule.as_ref().unwrap().instance);
        let table = Arc::clone(&vm.history_attachment.as_ref().unwrap().tables[0]);
        let slot = &table.rules[0];
        let losing = RuleRuntime::new(
            &history_store::store::HistoryStore::global(),
            &slot.template,
            false,
            &mut RegorusLimits {
                timer: &mut ExecutionTimer::new(None),
            },
            &mut ObservationWorld,
        )
        .unwrap();
        let losing = Arc::new(Mutex::new(losing));
        let losing_weak = Arc::downgrade(&losing);
        let selected = slot.replace(&old, losing);
        assert!(Arc::ptr_eq(&selected, &winner));
        assert!(losing_weak.upgrade().is_none());
        // Recovery rebinds the replacement to the exhausted runtime's numeric store.
        assert!(Arc::ptr_eq(winner.lock().store(), old.lock().store()));
        winner.lock().replace_graph_byte_pressure(MAX_GRAPH_BYTES);
        let error = vm.execute_history_step(0).unwrap_err();
        assert!(matches!(
            error,
            VmError::History {
                source: HistoryError::GraphLimit { .. },
                ..
            }
        ));
        assert_eq!(
            vm.history_active_rule.as_ref().unwrap().cursor.consumed(),
            0
        );
        assert!(winner.lock().cursor_positions().is_empty());
    }

    #[test]
    fn table_eviction_reclaims_only_unpinned_graphs() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let event = event(&store, "alice", "edit");
        let first = store
            .table_runtime(&program(any_head(), RegexExpr::All, 1), 0)
            .unwrap();
        let weak = Arc::downgrade(&first);
        let pinned = Arc::clone(&first.rules[0].current.lock());
        let pinned_weak = Arc::downgrade(&pinned);
        drop(first);
        for _ in 0..17 {
            store
                .table_runtime(&program(any_head(), RegexExpr::All, 1), 0)
                .unwrap();
        }
        assert!(weak.upgrade().is_none());
        assert!(pinned_weak.upgrade().is_some());
        store.append(&history, &[event]).unwrap();
        assert_eq!(store.len(&history).unwrap(), 1);
        assert_eq!(store.intern_action("edit").unwrap(), event.action);
        drop(pinned);
        assert!(pinned_weak.upgrade().is_none());
    }

    #[test]
    fn terminal_snapshot_failure_retains_only_successful_batches() {
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let event = event(&store, "alice", "edit");
        store.append(&history, &[event; 2]).unwrap();
        let mut vm = vm(&store, &history, &program(any_head(), RegexExpr::All, 1));
        let instance = lazy_instance(&vm);
        assert!(matches!(
            vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Repeat
        ));
        assert!(matches!(
            vm.execute_history_step(0).unwrap(),
            InstructionOutcome::Continue
        ));
        assert_eq!(instance.lock().cursor_positions()[0].3, 2);
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
        assert_eq!(instance.lock().cursor_positions()[0].3, 2);
        assert_eq!(instance.lock().cursor_positions()[0].2, 0);
    }

    #[test]
    fn retained_cursor_lru_is_bounded_and_keeps_recent_histories() {
        let store = Arc::new(HistoryStore::new());
        let program = program(any_head(), RegexExpr::All, 3);
        let first = store.new_history().unwrap();
        let initial = vm(&store, &first, &program);
        let instance = lazy_instance(&initial);
        let mut keys = Vec::new();
        for _ in 0..17 {
            let history = store.new_history().unwrap();
            keys.push(history.index());
            let mut vm = vm(&store, &history, &program);
            assert!(matches!(
                vm.execute_history_step(0).unwrap(),
                InstructionOutcome::Continue
            ));
        }
        let runtime = instance.lock();
        let positions = runtime.cursor_positions();
        assert_eq!(positions.len(), 16);
        assert_eq!(positions[0].0, keys[16]);
        assert_eq!(positions[15].0, keys[1]);
        assert!(positions.iter().all(|cursor| cursor.1 == positions[0].1));
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
