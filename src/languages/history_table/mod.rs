// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Rego history rules (`history.require`/`history.forbid`) lowered by the RVM
//! compiler into portable history tables; this module owns the limits adapter
//! and portable-source lowering.

pub(crate) mod limits;

pub use history_syntax::Component;
pub use junco_core::HistoryError;

use crate::rvm::program::HistoryTableRule;
use crate::utils::limits::ExecutionTimer;
use alloc::string::String;
use alloc::vec::Vec;
use junco_core::flat::{FlatHead, FlatPair, FlatTerm, FlatTest};
use junco_core::limits::Limits as _;
use junco_core::observation::ObservationWorld;
use junco_core::CompileError;

/// Principal coordinate of store events.
pub const PRINCIPAL: Component = Component(0);
/// Action coordinate of store events.
pub const ACTION: Component = Component(1);
/// Resource coordinate of store events.
pub const RESOURCE: Component = Component(2);

/// Borrowed-string authoring event of a lowered Rego history rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SourceEvent<'a> {
    pub(crate) principal: &'a str,
    pub(crate) action: &'a str,
    pub(crate) resource: &'a str,
}

/// Tagged coordinate of a [`SourceEvent`]; constants in rules carry their coordinate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum SourceComponent<'a> {
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

/// Flatten one borrowed rule and copy its constants into a store-independent table rule.
pub(crate) fn table_rule(
    rule: &history_syntax::Rule<SourceEvent<'_>>,
) -> Result<HistoryTableRule, CompileError> {
    let mut timer = ExecutionTimer::new(None);
    let mut limits = limits::RegorusLimits { timer: &mut timer };
    let mut world = ObservationWorld;
    let flat = junco_core::flatten_rule(rule, &mut limits, &mut world)?;
    let source = into_portable_source(flat.source, &mut limits, &mut world)
        .map_err(CompileError::Runtime)?;
    Ok(HistoryTableRule {
        mode: flat.mode,
        source,
    })
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
