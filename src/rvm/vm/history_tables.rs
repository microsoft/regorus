// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! History tables (`HistoryDecide`) and VM-owned histories.
//!
//! Invariant: every cursor `(history, bindings) -> (revision, consumed, residual)`
//! whose revision equals its history's revision denotes the quotient of the
//! rule's root by `events[..consumed]` under `bindings` (kernel `fold` contract).
//! Appends keep the revision; truncation bumps it, so stale cursors are ignored.

use super::errors::{Result, VmError};
use super::machine::RegoVM;
use crate::builtins::history::kernel::RegexId;
use crate::builtins::history::progress::CompiledPair;
use crate::builtins::history::{source, HistoryError, ObservationWorld};
use crate::rvm::program::HistoryRuleMode;
use crate::utils::limits::ExecutionTimer;
use crate::value::Value;
use alloc::vec::Vec;

/// Cursors retained per rule (move-to-front LRU).
const HISTORY_CURSOR_CAPACITY: usize = 16;

/// A host-owned event sequence addressed by handle.
#[derive(Debug, Default)]
pub(super) struct VmHistory {
    pub(super) events: Vec<Value>,
    pub(super) revision: u64,
}

/// Compiled kernel state for one `Program::history_tables` entry.
#[derive(Debug)]
pub(super) struct HistoryTableRuntime {
    rules: Vec<HistoryRuleRuntime>,
}

#[derive(Debug)]
struct HistoryRuleRuntime {
    mode: HistoryRuleMode,
    literal: u16,
    pair: CompiledPair,
    hints: source::PairHints,
    cursors: Vec<Cursor>,
}

#[derive(Debug)]
struct Cursor {
    history: usize,
    bindings: Vec<Value>,
    revision: u64,
    consumed: usize,
    residual: RegexId,
}

impl Drop for HistoryTableRuntime {
    fn drop(&mut self) {
        for rule in self.rules.drain(..) {
            rule.pair.release();
        }
    }
}

fn compile_rule(
    literal: &Value,
    precompile: bool,
    timer: &mut ExecutionTimer,
    world: &mut ObservationWorld,
) -> core::result::Result<(CompiledPair, source::PairHints), HistoryError> {
    #[cfg_attr(not(feature = "cache"), allow(unused_mut))]
    let mut pair = source::compile_pair(literal, timer, world)?;
    #[cfg(feature = "cache")]
    if precompile {
        if let Err(error) = pair.precompile(timer, world) {
            pair.release();
            if !matches!(error, HistoryError::GraphLimit { .. }) {
                return Err(error);
            }
            // Exploration overran the graph cap: fall back to an untouched lazy pair.
            pair = source::compile_pair(literal, timer, world)?;
        }
    }
    #[cfg(not(feature = "cache"))]
    let _ = precompile;
    match source::pair_hints(&pair) {
        Ok(hints) => Ok((pair, hints)),
        Err(error) => {
            pair.release();
            Err(error)
        }
    }
}

impl HistoryRuleRuntime {
    /// `history ∈ L_θ(R)`, folding only the events appended since the cursor.
    fn contains(
        &mut self,
        hid: usize,
        history: &VmHistory,
        bindings: &[Value],
        timer: &mut ExecutionTimer,
        world: &mut ObservationWorld,
    ) -> core::result::Result<bool, HistoryError> {
        let position = self
            .cursors
            .iter()
            .position(|c| c.history == hid && c.bindings.as_slice() == bindings);
        let (start, residual) = match position.and_then(|p| self.cursors.get(p)) {
            Some(c) if c.revision == history.revision && c.consumed <= history.events.len() => {
                (c.consumed, c.residual)
            }
            _ => (0, self.pair.root),
        };
        let suffix = history.events.get(start..).ok_or(HistoryError::Invariant {
            message: "invalid history cursor",
        })?;
        let binding_ids = self.pair.interner.intern_values(bindings, world)?;
        let residual = self.pair.fold(
            residual,
            suffix,
            bindings,
            &binding_ids,
            &mut self.hints.paths,
            timer,
            world,
        )?;
        let answer = self.pair.answer(residual, timer, world)?;
        // Publish only after every fallible step.
        let cursor = match position {
            Some(p) => {
                let mut cursor = self.cursors.remove(p);
                cursor.revision = history.revision;
                cursor.consumed = history.events.len();
                cursor.residual = residual;
                cursor
            }
            None => {
                if self.cursors.len() >= HISTORY_CURSOR_CAPACITY {
                    self.cursors.pop();
                }
                Cursor {
                    history: hid,
                    bindings: bindings.to_vec(),
                    revision: history.revision,
                    consumed: history.events.len(),
                    residual,
                }
            }
        };
        self.cursors.insert(0, cursor);
        Ok(answer)
    }
}

impl RegoVM {
    /// Create an empty history and return its handle.
    pub fn history_new(&mut self) -> usize {
        self.histories.push(VmHistory::default());
        self.histories.len().saturating_sub(1)
    }

    /// Append events to a history. Existing cursors stay valid.
    pub fn history_append(
        &mut self,
        hid: usize,
        events: impl IntoIterator<Item = Value>,
    ) -> Result<()> {
        let pc = self.pc;
        let history = self
            .histories
            .get_mut(hid)
            .ok_or(VmError::InvalidHistoryHandle {
                handle: Value::from(hid),
                pc,
            })?;
        let before = history.events.len();
        for event in events {
            if event == Value::Undefined {
                history.events.truncate(before);
                return Err(VmError::InvalidHistoryEvent { pc });
            }
            history.events.push(event);
        }
        self.memory_check()
    }

    /// Truncate a history to `len` events; shrinking invalidates its cursors.
    pub fn history_truncate(&mut self, hid: usize, len: usize) -> Result<()> {
        let history = self
            .histories
            .get_mut(hid)
            .ok_or(VmError::InvalidHistoryHandle {
                handle: Value::from(hid),
                pc: self.pc,
            })?;
        if len < history.events.len() {
            history.revision = history.revision.wrapping_add(1);
            history.events.truncate(len);
        }
        Ok(())
    }

    /// Number of events in a history.
    pub fn history_len(&self, hid: usize) -> Result<usize> {
        self.histories
            .get(hid)
            .map(|h| h.events.len())
            .ok_or(VmError::InvalidHistoryHandle {
                handle: Value::from(hid),
                pc: self.pc,
            })
    }

    fn history_kernel_error(error: HistoryError, pc: usize) -> VmError {
        Self::history_match_error(error.into(), pc)
    }

    pub(super) fn execute_history_decide(&mut self, params_index: u16) -> Result<()> {
        let pc = self.pc;
        let program = self.program.clone();
        let params = program
            .instruction_data
            .history_decide_params
            .get(usize::from(params_index))
            .ok_or(VmError::InvalidHistoryDecideParams {
                index: params_index,
                pc,
            })?;
        let handle = self.get_register(params.history)?;
        let hid = match *handle {
            Value::Number(ref n) => n
                .as_u64()
                .and_then(|n| usize::try_from(n).ok())
                .filter(|&hid| hid < self.histories.len()),
            _ => None,
        }
        .ok_or_else(|| VmError::InvalidHistoryHandle {
            handle: handle.clone(),
            pc,
        })?;
        let request = self.get_register(params.request)?.clone();
        if request == Value::Undefined {
            return self.set_register(params.dest, Value::Undefined);
        }

        let table_index = usize::from(params.table);
        let table =
            program
                .history_tables
                .get(table_index)
                .ok_or(VmError::InvalidHistoryDecideParams {
                    index: params_index,
                    pc,
                })?;
        let RegoVM {
            ref histories,
            ref mut history_tables,
            ref mut execution_timer,
            ..
        } = *self;
        let timer = execution_timer;
        let mut world = ObservationWorld;
        let slot =
            history_tables
                .get_mut(table_index)
                .ok_or(VmError::InvalidHistoryDecideParams {
                    index: params_index,
                    pc,
                })?;
        if slot.is_none() {
            let mut runtime = HistoryTableRuntime {
                rules: Vec::with_capacity(table.rules.len()),
            };
            for (rule, spec) in table.rules.iter().enumerate() {
                let literal = program.literals.get(usize::from(spec.pair_literal)).ok_or(
                    VmError::LiteralIndexOutOfBounds {
                        index: spec.pair_literal,
                        pc,
                    },
                )?;
                let (pair, hints) =
                    compile_rule(literal, true, timer, &mut world).map_err(|error| {
                        if matches!(error, HistoryError::Limit(_)) {
                            Self::history_kernel_error(error, pc)
                        } else {
                            VmError::HistoryTableCompile {
                                table: params.table,
                                rule,
                                message: alloc::format!("{error}"),
                                pc,
                            }
                        }
                    })?;
                runtime.rules.push(HistoryRuleRuntime {
                    mode: spec.mode,
                    literal: spec.pair_literal,
                    pair,
                    hints,
                    cursors: Vec::new(),
                });
            }
            *slot = Some(runtime);
        }
        let runtime = slot.as_mut().ok_or(VmError::InvalidHistoryDecideParams {
            index: params_index,
            pc,
        })?;
        let history = histories
            .get(hid)
            .ok_or_else(|| VmError::InvalidHistoryHandle {
                handle: Value::from(hid),
                pc,
            })?;

        let mut result = Value::Null;
        for (index, rule) in runtime.rules.iter_mut().enumerate() {
            let Some(bindings) = rule
                .pair
                .pattern
                .matches(
                    &request,
                    &rule.pair.symbols,
                    &mut rule.hints.pattern,
                    timer,
                    &mut world,
                )
                .map_err(|e| Self::history_kernel_error(e, pc))?
            else {
                continue;
            };
            let inside = match rule.contains(hid, history, &bindings, timer, &mut world) {
                Err(HistoryError::GraphLimit { .. }) => {
                    // The retained graph is full of unrelated exploration: replay
                    // once from a fresh lazy pair; a second failure is fatal.
                    let literal = program.literals.get(usize::from(rule.literal)).ok_or(
                        VmError::LiteralIndexOutOfBounds {
                            index: rule.literal,
                            pc,
                        },
                    )?;
                    let (fresh, hints) = compile_rule(literal, false, timer, &mut world)
                        .map_err(|e| Self::history_kernel_error(e, pc))?;
                    core::mem::replace(&mut rule.pair, fresh).release();
                    rule.hints = hints;
                    rule.cursors.clear();
                    rule.contains(hid, history, &bindings, timer, &mut world)
                }
                other => other,
            }
            .map_err(|e| Self::history_kernel_error(e, pc))?;
            let violated = match rule.mode {
                HistoryRuleMode::Forbid => inside,
                HistoryRuleMode::Require => !inside,
            };
            if violated {
                result = Value::from(index);
                break;
            }
        }
        self.set_register(params.dest, result)
    }
}
