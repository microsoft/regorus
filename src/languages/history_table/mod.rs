// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Ordered Rust-DSL rules compiled to bounded `HistoryStep` instructions.
//! Rules borrow exact principal/action/resource strings; compiled programs own
//! them. Execution accepts only a staged typed event and shared history.
//! Each decision returns `null` (grant) or the first violated rule's index.

pub(crate) mod limits;
pub(crate) mod store;

pub use history_syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
pub use junco_core::{CompileError, HistoryError};
pub use store::{Event, HistoryHandle, HistoryStore};

use crate::rvm::instructions::HistoryStepParams;
use crate::rvm::program::{HistoryTable, HistoryTableRule, Program};
use crate::rvm::Instruction;
use crate::utils::limits::ExecutionTimer;
use alloc::string::{String, ToString as _};
use alloc::sync::Arc;
use alloc::vec::Vec;
use junco_core::flat::{FlatHead, FlatPair, FlatTerm, FlatTest};
use junco_core::limits::Limits as _;
use junco_core::observation::ObservationWorld;

/// Principal coordinate of a [`SourceEvent`] and of store events.
pub const PRINCIPAL: Component = Component(0);
/// Action coordinate of a [`SourceEvent`] and of store events.
pub const ACTION: Component = Component(1);
/// Resource coordinate of a [`SourceEvent`] and of store events.
pub const RESOURCE: Component = Component(2);

/// Borrowed-string authoring event for portable history-table rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SourceEvent<'a> {
    pub principal: &'a str,
    pub action: &'a str,
    pub resource: &'a str,
}

/// Tagged coordinate of a [`SourceEvent`]; constants in rules carry their coordinate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SourceComponent<'a> {
    Principal(&'a str),
    Action(&'a str),
    Resource(&'a str),
}

impl history_syntax::KeyHash for SourceComponent<'_> {
    fn key_hash(&self) -> u64 {
        history_syntax::key_hash::hash_via_std(self)
    }
}

impl<'a> history_syntax::Event for SourceEvent<'a> {
    type Component = SourceComponent<'a>;
    type Arity = history_syntax::N3;

    fn component(self, index: usize) -> SourceComponent<'a> {
        match index {
            0 => SourceComponent::Principal(self.principal),
            1 => SourceComponent::Action(self.action),
            _ => SourceComponent::Resource(self.resource),
        }
    }

    fn coordinate(component: SourceComponent<'a>) -> usize {
        match component {
            SourceComponent::Principal(_) => 0,
            SourceComponent::Action(_) => 1,
            SourceComponent::Resource(_) => 2,
        }
    }
}

/// History table compilation failures.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum HistoryTableError {
    #[error("history batch_size must be greater than zero")]
    InvalidBatchSize,
    #[error("history table rule {index} is invalid: {source}")]
    InvalidRule {
        index: usize,
        #[source]
        source: CompileError,
    },
    #[error("history table has too many rules ({0})")]
    TooManyRules(usize),
    #[error("invalid compiled history program: {0}")]
    InvalidProgram(String),
}

/// Compile ordered borrowed Rust rules into a portable program with entry point
/// `decide`. `batch_size` bounds the events consumed by each instruction dispatch.
pub fn compile(
    rules: &[Rule<SourceEvent<'_>>],
    batch_size: u32,
) -> Result<Arc<Program>, HistoryTableError> {
    if batch_size == 0 {
        return Err(HistoryTableError::InvalidBatchSize);
    }
    if rules.len() > Program::MAX_INSTRUCTIONS.saturating_sub(2) {
        return Err(HistoryTableError::TooManyRules(rules.len()));
    }

    let mut program = Program::new();
    let mut table_rules = Vec::with_capacity(rules.len());
    for (index, rule) in rules.iter().enumerate() {
        let mut timer = ExecutionTimer::new(None);
        let mut limits = limits::RegorusLimits { timer: &mut timer };
        let mut world = ObservationWorld;
        let flat = junco_core::flatten_rule(rule, &mut limits, &mut world)
            .map_err(|source| HistoryTableError::InvalidRule { index, source })?;
        let source = into_portable_source(flat.source, &mut limits, &mut world).map_err(|e| {
            HistoryTableError::InvalidRule {
                index,
                source: CompileError::Runtime(e),
            }
        })?;
        table_rules.push(HistoryTableRule {
            mode: flat.mode,
            source,
        });
    }

    let table_index = program.add_history_table(HistoryTable { rules: table_rules });
    for index in 0..rules.len() {
        let rule =
            u16::try_from(index).map_err(|_| HistoryTableError::TooManyRules(rules.len()))?;
        let params_index = program.add_history_step_params(HistoryStepParams {
            table: table_index,
            rule,
            batch_size,
        });
        program
            .instructions
            .push(Instruction::HistoryStep { params_index });
    }
    program.instructions.push(Instruction::LoadNull { dest: 0 });
    program.instructions.push(Instruction::Return { value: 0 });
    program.instruction_spans = alloc::vec![None; program.instructions.len()];
    program.main_entry_point = 0;
    program.add_entry_point("decide".to_string(), 0);
    program.dispatch_window_size = 1;
    program.max_rule_window_size = 1;
    program.metadata.language = "history_table".to_string();
    program
        .initialize_resolved_builtins()
        .and_then(|()| program.validate_limits().map_err(anyhow::Error::msg))
        .map_err(|e| HistoryTableError::InvalidProgram(e.to_string()))?;
    Ok(Arc::new(program))
}

/// Copy borrowed constants into a store-independent source, moving every other table unchanged.
fn into_portable_source(
    source: FlatPair<SourceComponent<'_>>,
    limits: &mut limits::RegorusLimits<'_>,
    world: &mut ObservationWorld,
) -> Result<FlatPair<String>, HistoryError> {
    let FlatPair {
        head,
        tests,
        regexes,
        root,
    } = source;
    let mut owned_head = Vec::new();
    world
        .try_reserve_vec_exact(&mut owned_head, head.len())
        .map_err(|_| HistoryError::AllocationFailed)?;
    limits.enforce_memory()?;
    for slot in head {
        owned_head.push(match slot {
            FlatHead::Any => FlatHead::Any,
            FlatHead::Bind => FlatHead::Bind,
            FlatHead::Constant(value) => FlatHead::Constant(own_constant(value, limits)?),
        });
    }
    let mut owned = Vec::new();
    world
        .try_reserve_vec_exact(&mut owned, tests.len())
        .map_err(|_| HistoryError::AllocationFailed)?;
    limits.enforce_memory()?;
    for test in tests {
        limits.checkpoint()?;
        owned.push(match test {
            FlatTest::Bool(value) => FlatTest::Bool(value),
            FlatTest::Atom {
                field,
                term,
                positive,
            } => FlatTest::Atom {
                field,
                term: match term {
                    FlatTerm::Constant(value) => FlatTerm::Constant(own_constant(value, limits)?),
                    FlatTerm::Variable(variable) => FlatTerm::Variable(variable),
                },
                positive,
            },
            FlatTest::And(children) => FlatTest::And(children),
            FlatTest::Or(children) => FlatTest::Or(children),
        });
    }
    Ok(FlatPair {
        head: owned_head,
        tests: owned,
        regexes,
        root,
    })
}

/// Copy one constant's exact bytes into an owned string; flattening already checked its coordinate.
fn own_constant(
    value: SourceComponent<'_>,
    limits: &mut limits::RegorusLimits<'_>,
) -> Result<String, HistoryError> {
    let (SourceComponent::Principal(text)
    | SourceComponent::Action(text)
    | SourceComponent::Resource(text)) = value;
    let mut owned = String::new();
    owned
        .try_reserve_exact(text.len())
        .map_err(|_| HistoryError::AllocationFailed)?;
    limits.enforce_memory()?;
    owned.push_str(text);
    Ok(owned)
}
