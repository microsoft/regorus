// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Bounded history steps. A decision pins one revision and prefix; each active rule folds at
//! most one batch of that prefix per dispatch and holds no lock across dispatches.

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
use history_store::history::StoredHistory;
use history_store::store::HistoryRecord;
use history_syntax::RuleMode;
use junco_core::limits::Limits as _;
use junco_core::reference::{head_matches, Lang};

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

/// One rule's derivative fold over the pinned prefix, resumed by each repeated dispatch.
#[derive(Debug)]
pub(super) struct ActiveHistoryRule {
    pc: usize,
    consumed: usize,
    residual: Lang,
}

impl HistoryAttachment {
    fn new(
        store: Arc<HistoryStore>,
        program: &Program,
    ) -> core::result::Result<Self, HistoryError> {
        let mut tables = Vec::new();
        tables
            .try_reserve_exact(program.history_tables.len())
            .map_err(|_| HistoryError::AllocationFailed)?;
        for table in 0..program.history_tables.len() {
            tables.push(Arc::new(store.table_runtime(program, table)?));
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
    /// Rule constants are interned outside decision timing.
    pub fn attach_history(&mut self, store: Arc<HistoryStore>) -> Result<()> {
        self.ensure_history_idle()?;
        let attachment = HistoryAttachment::new(store, &self.program)
            .map_err(|error| VmError::from_history(error, self.pc))?;
        self.history_attachment = Some(attachment);
        self.history_input = None;
        self.clear_history_execution();
        Ok(())
    }

    /// Stage a request without appending it to the supplied history.
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
        // A failed suspendable run may leave a stale `Running` state; only suspension or an
        // unpublished decision means a history execution is still live.
        if matches!(self.execution_state, ExecutionState::Suspended { .. })
            || self.history_decision.is_some()
        {
            return Err(VmError::HistoryExecutionActive { pc: self.pc });
        }
        Ok(())
    }

    pub(super) fn clear_history_execution(&mut self) {
        self.history_decision = None;
        self.history_active_rule = None;
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
        let mut limits = RegorusLimits {
            timer: &mut self.execution_timer,
        };
        let request = decision.request.active();
        if self.history_active_rule.is_none() {
            if !head_matches(&slot.template.head, request) {
                // A request outside the head leaves the rule vacuously honored.
                self.set_register(params.dest, Value::Bool(true))?;
                return Ok(InstructionOutcome::Continue);
            }
            let residual = Lang::inflate(&slot.template, &mut limits)
                .map_err(|error| VmError::from_history(error, pc))?;
            self.history_active_rule = Some(ActiveHistoryRule {
                pc,
                consumed: 0,
                residual,
            });
        }
        let active = self
            .history_active_rule
            .as_mut()
            .ok_or(VmError::HistoryContextMissing { pc })?;
        let stored = decision.record.read();
        decision
            .check(&stored, &mut limits)
            .map_err(|error| VmError::from_history(error, pc))?;
        let end = decision
            .target_len
            .min(active.consumed.saturating_add(batch_size));
        // `check` guarantees the pinned prefix is still present.
        let batch = stored.as_slice().get(active.consumed..end).ok_or_else(|| {
            VmError::from_history(
                HistoryError::invariant("history batch outside the pinned prefix"),
                pc,
            )
        })?;
        // Fold into a local residual so a failed batch leaves the continuation unchanged.
        let mut residual = active.residual.clone();
        for event in batch {
            residual = residual
                .step(&slot.template, event.active(), request, &mut limits)
                .map_err(|error| VmError::from_history(error, pc))?;
        }
        drop(stored);
        active.residual = residual;
        active.consumed = end;
        if end < decision.target_len {
            return Ok(InstructionOutcome::Repeat);
        }
        let accepted = active.residual.nullable();
        self.history_active_rule = None;
        let violated = match slot.mode {
            RuleMode::Require => !accepted,
            RuleMode::Forbid => accepted,
        };
        self.set_register(params.dest, Value::Bool(!violated))?;
        Ok(InstructionOutcome::Continue)
    }
}
