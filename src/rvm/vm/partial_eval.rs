// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Partial evaluation: concrete evaluation with some input or context paths
//! declared unknown.
//!
//! Any read of a root that has unknown paths at or under it makes the
//! result `Unsupported`, so constructs not handled here fail closed. When
//! no such root is read, the result is `Exact` with the concrete value.
//! Errors the VM treats as fatal, such as resource limits, numeric overflow
//! and builtin limits, are always returned as errors, even when an unknown
//! being undefined led to them, so limits are enforced. Any other
//! evaluation error after a read of such a root may come from the unknowns
//! being undefined, so it is reported as `Unsupported` too, to fail closed.
//! Rule bodies already absorb such errors, so this mainly applies to errors
//! outside rules.
//!
//! See [`RegoVM::partial_eval`] for the limitation on input-dependent defaults.

use super::dispatch::InstructionOutcome;
use super::errors::Result;
use super::execution_model::ExecutionMode;
use super::machine::RegoVM;
use crate::explain::{
    ExplainError, PartialEvalResult, PartialEvalSettings, PathSegment, ResidualStatus, RuleKind,
    UnknownRoot,
};
use crate::rvm::instructions::Instruction;
use crate::rvm::program::Program;
use crate::value::Value;
use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;

type Path = (UnknownRoot, Vec<PathSegment>);

#[derive(Debug, Clone, Copy)]
enum Reason {
    RootRead(UnknownRoot),
}

/// Partial evaluation state for one evaluation.
#[derive(Debug)]
pub(super) struct PeState {
    input_has_unknowns: bool,
    context_has_unknowns: bool,
    unsupported: Option<(Reason, usize)>,
}

impl PeState {
    const fn has_unknowns(&self, root: UnknownRoot) -> bool {
        match root {
            UnknownRoot::Input => self.input_has_unknowns,
            UnknownRoot::Context => self.context_has_unknowns,
        }
    }

    fn flag(&mut self, reason: Reason, pc: usize) {
        self.unsupported.get_or_insert((reason, pc));
    }
}

const fn root_name(root: UnknownRoot) -> &'static str {
    match root {
        UnknownRoot::Input => "input",
        UnknownRoot::Context => "context",
    }
}

/// Renders a path as Rego, such as `input["user"]["role"]` or
/// `input["xs"][0]`.
fn render_path(
    root: UnknownRoot,
    segments: &[PathSegment],
    checkpoint: &mut impl FnMut() -> Result<()>,
) -> core::result::Result<String, ExplainError> {
    checkpoint()?;
    let mut text = String::from(root_name(root));
    for segment in segments {
        match *segment {
            PathSegment::Key(ref key) => {
                let key_value = Value::from(key.as_str());
                checkpoint()?;
                #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
                let quoted = key_value.to_json_str_with_checkpoint(checkpoint)?;
                #[cfg(any(not(feature = "allocator-memory-limits"), miri))]
                let quoted = key_value
                    .to_json_str_compact()
                    .map_err(super::VmError::from)?;
                checkpoint()?;
                drop(key_value);
                let _ = write!(text, "[{quoted}]");
                checkpoint()?;
            }
            PathSegment::Index(i) => {
                let _ = write!(text, "[{i}]");
            }
        }
        checkpoint()?;
    }
    Ok(text)
}

struct PartialEvaluation<'a>(&'a mut RegoVM);

impl Drop for PartialEvaluation<'_> {
    fn drop(&mut self) {
        self.0.pe = None;
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        self.0.finish_active_memory_budget_execution();
    }
}

/// The kind of rule whose result the entry point at `pc` returns, or `None`
/// if it can't be told. An entry point that does more than call a rule and
/// return its result, such as Azure Policy's, is only classified if every
/// rule is complete. A malformed entry point is classified as complete, as
/// running it fails.
fn entry_rule_kind(program: &Program, pc: usize) -> Option<RuleKind> {
    let kind = |info: &crate::rvm::program::RuleInfo| {
        if info.function_info.is_some() {
            RuleKind::Function
        } else {
            RuleKind::from(info.rule_type.clone())
        }
    };
    match (
        program.instructions.get(pc),
        program.instructions.get(pc.saturating_add(1)),
    ) {
        (None, _) => Some(RuleKind::Complete),
        (
            Some(&Instruction::CallRule { rule_index, dest }),
            Some(&Instruction::Return { value }),
        ) if dest == value => Some(
            program
                .rule_infos
                .get(usize::from(rule_index))
                .map_or(RuleKind::Complete, kind),
        ),
        _ => program
            .rule_infos
            .iter()
            .all(|info| kind(info) == RuleKind::Complete)
            .then_some(RuleKind::Complete),
    }
}

impl RegoVM {
    /// Sets the unknown paths for [`partial_eval`](Self::partial_eval).
    pub fn set_partial_eval_settings(&mut self, settings: PartialEvalSettings) {
        self.pe_settings = settings;
    }

    /// Evaluates the entry point with the configured unknown paths and
    /// returns what the result depends on. The VM's input and context are
    /// the known values; none may be supplied at or under an unknown path.
    ///
    /// Returns [`ExplainError::PartialEvalWithRecorder`] if an explanation
    /// recorder is installed: explanations and partial evaluation are
    /// separate runs. Returns [`ExplainError::PartialEvalUnknownRuleKind`] if the
    /// kind of rule whose result the entry point returns can't be told,
    /// which only happens for programs not produced by the built-in
    /// compilers.
    ///
    /// Rule defaults are evaluated at compile time with undefined `input`.
    /// Dependencies read by a default are not recorded, so an input-dependent
    /// default can produce an `Exact` result even when it depends on an unknown.
    /// Memory limits cover validation, execution and report construction.
    pub fn partial_eval(
        &mut self,
        entry: &str,
    ) -> core::result::Result<PartialEvalResult, ExplainError> {
        if matches!(self.next_execution_mode, ExecutionMode::Suspendable) {
            return Err(ExplainError::PartialEvalSuspendable);
        }
        if self.explain_enabled() {
            return Err(ExplainError::PartialEvalWithRecorder);
        }
        crate::utils::limits::without_memory_budget_scope(|| {
            self.release_previous_execution_state();
            #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
            {
                self.reset_memory_budget_state();
                self.memory_budget_lifecycle =
                    super::machine::MemoryBudgetLifecycle::PartialEvaluation;
            }
            let evaluation = PartialEvaluation(self);
            evaluation.0.check_initial_memory_limit()?;
            let result = evaluation.0.partial_eval_inner(entry);
            if let Err(error) = evaluation.0.check_initial_memory_limit() {
                return Err(evaluation.0.fail_run_to_completion(error).into());
            }
            result
        })
    }

    fn partial_eval_inner(
        &mut self,
        entry: &str,
    ) -> core::result::Result<PartialEvalResult, ExplainError> {
        let pe_state = self.validate_unknowns()?;
        let program = self.program.clone();
        let kind = match program.get_entry_point(entry) {
            Some(pc) => entry_rule_kind(&program, pc).ok_or_else(|| {
                ExplainError::PartialEvalUnknownRuleKind {
                    entry: String::from(entry),
                }
            })?,
            // Running an unknown entry point fails, so the kind is unused.
            None => RuleKind::Complete,
        };
        self.pe = Some(Box::new(pe_state));
        let run = self.execute_entry_point_by_name(entry);
        let state = self.pe.as_deref().ok_or(ExplainError::NotEnabled)?;
        if let Err(ref error) = run {
            if self.is_fatal_vm_error(error) {
                return Err(error.clone().into());
            }
        }
        if let Some((reason, pc)) = state.unsupported {
            return Ok(PartialEvalResult {
                kind,
                status: ResidualStatus::Unsupported,
                result: Value::Undefined,
                residual_queries: Vec::new(),
                warnings: alloc::vec![warning(&program, reason, pc)],
            });
        }
        let result = run?;
        Ok(PartialEvalResult {
            kind,
            status: ResidualStatus::Exact,
            result,
            residual_queries: Vec::new(),
            warnings: Vec::new(),
        })
    }

    fn validate_unknowns(&mut self) -> core::result::Result<PeState, ExplainError> {
        let mut paths: Vec<Path> = Vec::new();
        for i in 0..self.pe_settings.unknowns.len() {
            #[allow(clippy::indexing_slicing)]
            let unknown = self.pe_settings.unknowns[i].clone();
            self.check_initial_memory_limit()?;
            let (root, segments) = (unknown.root, &unknown.segments);
            if let Some(other) = paths
                .iter()
                .find(|p| p.0 == root && (p.1.starts_with(segments) || segments.starts_with(&p.1)))
            {
                return Err(ExplainError::InvalidUnknownPath {
                    path: render_path(root, segments, &mut || self.check_initial_memory_limit())?,
                    reason: format!(
                        "overlaps `{}`",
                        render_path(other.0, &other.1, &mut || self.check_initial_memory_limit())?
                    ),
                });
            }
            let mut value = match root {
                UnknownRoot::Input => self.input.clone(),
                UnknownRoot::Context => self.context.clone(),
            };
            for segment in segments {
                // Rego keys also select set members, and indices select numeric object keys.
                let key = match *segment {
                    PathSegment::Key(ref key) => Value::from(key.as_str()),
                    PathSegment::Index(index) => Value::from(index),
                };
                self.check_initial_memory_limit()?;
                value = value[&key].clone();
                self.check_initial_memory_limit()?;
            }
            // The VM's input is null until it is set; its context is undefined.
            let absent = matches!(value, Value::Undefined)
                || (root == UnknownRoot::Input
                    && segments.is_empty()
                    && matches!(value, Value::Null));
            if !absent {
                return Err(ExplainError::UnknownValueSupplied {
                    path: render_path(root, segments, &mut || self.check_initial_memory_limit())?,
                });
            }
            paths.push((root, unknown.segments));
            self.check_initial_memory_limit()?;
        }
        Ok(PeState {
            input_has_unknowns: paths.iter().any(|p| p.0 == UnknownRoot::Input),
            context_has_unknowns: paths.iter().any(|p| p.0 == UnknownRoot::Context),
            unsupported: None,
        })
    }

    /// Handles an instruction that involves unknown paths. Returns `None`
    /// to run it normally.
    #[cold]
    #[inline(never)]
    pub(super) fn pe_execute(
        &mut self,
        _program: &Program,
        instruction: &Instruction,
    ) -> Result<Option<InstructionOutcome>> {
        let root = match *instruction {
            Instruction::LoadInput { .. } => UnknownRoot::Input,
            Instruction::LoadContext { .. } => UnknownRoot::Context,
            _ => return Ok(None),
        };
        let pc = self.pc;
        if let Some(pe) = self.pe.as_deref_mut() {
            if pe.has_unknowns(root) {
                pe.flag(Reason::RootRead(root), pc);
            }
        }
        Ok(None)
    }
}

fn warning(program: &Program, reason: Reason, pc: usize) -> String {
    let Reason::RootRead(root) = reason;
    let mut text = format!(
        "partial evaluation unsupported: `{}` has unknown paths and is read",
        root_name(root)
    );
    if let Some(span) = program.get_instruction_span(pc) {
        if let Some(source) = program.sources.get(span.source_index) {
            let _ = write!(text, " at {}:{}:{}", source.name, span.line, span.column);
        }
    }
    text
}

#[cfg(test)]
#[allow(
    clippy::panic_in_result_fn,
    clippy::indexing_slicing,
    clippy::field_reassign_with_default,
    clippy::shadow_unrelated
)]
mod tests;
