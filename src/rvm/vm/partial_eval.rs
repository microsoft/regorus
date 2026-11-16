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
//! Limitation: the compiler evaluates rule defaults once, at compile time,
//! with `input` undefined, and the compiled program does not record which
//! roots a default read. A default that reads `input`, such as
//! `default reasons := [x | x := input.reasons[_]]`, is therefore a constant
//! here, and the result can be `Exact` although it depends on unknowns.

use super::dispatch::InstructionOutcome;
use super::errors::Result;
use super::execution_model::ExecutionMode;
use super::machine::RegoVM;
use super::VmError;
use crate::explain::{
    ExplainError, PartialEvalResult, PartialEvalSettings, PathSegment, ResidualStatus, RuleKind,
    SourceLocation, UnknownRoot,
};
use crate::rvm::instructions::Instruction;
use crate::rvm::program::Program;
use crate::value::Value;
use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

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

/// The value at `segment` of `value`, as Rego indexes it: a key also
/// selects a set member and an index an object's number key, so any value a
/// policy could read at an unknown path counts as supplied.
fn index(value: &Value, segment: &PathSegment) -> Value {
    match *segment {
        PathSegment::Key(ref key) => value[&Value::from(key.as_str())].clone(),
        PathSegment::Index(i) => value[&Value::from(i)].clone(),
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
) -> core::result::Result<String, ExplainError> {
    let mut text = String::from(root_name(root));
    for segment in segments {
        match *segment {
            PathSegment::Key(ref key) => {
                let quoted = Value::from(key.as_str())
                    .to_json_str_compact()
                    .map_err(VmError::from)?;
                text.push_str(&format!("[{quoted}]"));
            }
            PathSegment::Index(i) => text.push_str(&format!("[{i}]")),
        }
    }
    Ok(text)
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
        let Some(state) = self.pe.take() else {
            return Err(ExplainError::NotEnabled);
        };
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

    fn validate_unknowns(&self) -> core::result::Result<PeState, ExplainError> {
        let mut paths: Vec<Path> = Vec::new();
        for unknown in &self.pe_settings.unknowns {
            let (root, segments) = (unknown.root, &unknown.segments);
            if let Some(other) = paths
                .iter()
                .find(|p| p.0 == root && (p.1.starts_with(segments) || segments.starts_with(&p.1)))
            {
                return Err(ExplainError::InvalidUnknownPath {
                    path: render_path(root, segments)?,
                    reason: format!("overlaps `{}`", render_path(other.0, &other.1)?),
                });
            }
            let mut value = match root {
                UnknownRoot::Input => self.input.clone(),
                UnknownRoot::Context => self.context.clone(),
            };
            for segment in segments {
                value = index(&value, segment);
            }
            // The VM's input is null until it is set; its context is undefined.
            let absent = matches!(value, Value::Undefined)
                || (root == UnknownRoot::Input
                    && segments.is_empty()
                    && matches!(value, Value::Null));
            if !absent {
                return Err(ExplainError::UnknownValueSupplied {
                    path: render_path(root, segments)?,
                });
            }
            paths.push((root, segments.clone()));
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

fn location(program: &Program, pc: usize) -> Option<SourceLocation> {
    let span = program.get_instruction_span(pc)?;
    Some(SourceLocation {
        file: program.sources.get(span.source_index)?.name.clone(),
        line: span.line,
        column: span.column,
    })
}

fn warning(program: &Program, reason: Reason, pc: usize) -> String {
    let at = location(program, pc)
        .map(|l| format!(" at {}:{}:{}", l.file, l.line, l.column))
        .unwrap_or_default();
    let text = match reason {
        Reason::RootRead(root) => format!("`{}` has unknown paths and is read", root_name(root)),
    };
    format!("partial evaluation unsupported: {text}{at}")
}

#[cfg(test)]
#[allow(
    clippy::panic_in_result_fn,
    clippy::indexing_slicing,
    clippy::field_reassign_with_default,
    clippy::shadow_unrelated
)]
mod tests;
