//! Constant encoding preserves portable DAG topology; graph compilation is separate.

use crate::errors::HistoryError;
use crate::flat::{FlatBuilder, FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use crate::limits::Limits;
use crate::observation::ObservationWorld;
use alloc::vec::Vec;
use history_syntax::Event;
use history_syntax::syntax::Component;

/// Component-specific constant encoding. Hashes are lookup aids, never identities.
pub trait FlatEncoder<C>: Sized {
    fn encode(&mut self, field: Component, value: &C) -> Result<u64, HistoryError>;
}

/// Validate a typed constant's coordinate before touching a component codebook.
pub fn validate_component<E: Event>(
    field: Component,
    value: &E::Component,
) -> Result<(), HistoryError> {
    if E::coordinate(*value) == field.index() {
        Ok(())
    } else {
        Err(HistoryError::invalid_policy(
            "$",
            "constant belongs to another component",
        ))
    }
}

fn invalid_source() -> HistoryError {
    HistoryError::invalid_policy("$", "invalid portable history source")
}

fn copy_ids<L: Limits>(
    source: &[u32],
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<Vec<u32>, HistoryError> {
    let mut ids = Vec::new();
    if world.try_reserve_vec_exact(&mut ids, source.len()).is_err() {
        return Err(HistoryError::AllocationFailed);
    }
    for id in source {
        limits.checkpoint()?;
        ids.push(*id);
    }
    Ok(ids)
}

fn encode_head<C, M: FlatEncoder<C>>(
    source: &FlatHead<C>,
    field: Component,
    encoder: &mut M,
) -> Result<FlatHead<u64>, HistoryError> {
    match source {
        FlatHead::Any => Ok(FlatHead::Any),
        FlatHead::Bind => Ok(FlatHead::Bind),
        FlatHead::Constant(value) => Ok(FlatHead::Constant(encoder.encode(field, value)?)),
    }
}

fn encode_test<C, M: FlatEncoder<C>, L: Limits>(
    source: &FlatTest<C>,
    encoder: &mut M,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<FlatTest<u64>, HistoryError> {
    match source {
        FlatTest::Bool(value) => Ok(FlatTest::Bool(*value)),
        FlatTest::Atom {
            field,
            term,
            positive,
        } => {
            let term = match term {
                FlatTerm::Constant(value) => FlatTerm::Constant(encoder.encode(*field, value)?),
                FlatTerm::Variable(variable) => FlatTerm::Variable(*variable),
            };
            Ok(FlatTest::Atom {
                field: *field,
                term,
                positive: *positive,
            })
        }
        FlatTest::And(children) => Ok(FlatTest::And(copy_ids(children, limits, world)?)),
        FlatTest::Or(children) => Ok(FlatTest::Or(copy_ids(children, limits, world)?)),
    }
}

fn copy_regex<L: Limits>(
    source: &FlatRegex,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<FlatRegex, HistoryError> {
    Ok(match source {
        FlatRegex::Empty => FlatRegex::Empty,
        FlatRegex::All => FlatRegex::All,
        FlatRegex::Epsilon => FlatRegex::Epsilon,
        FlatRegex::Test(id) => FlatRegex::Test(*id),
        FlatRegex::Concat(ids) => FlatRegex::Concat(copy_ids(ids, limits, world)?),
        FlatRegex::Union(ids) => FlatRegex::Union(copy_ids(ids, limits, world)?),
        FlatRegex::Intersect(ids) => FlatRegex::Intersect(copy_ids(ids, limits, world)?),
        FlatRegex::Star(id) => FlatRegex::Star(*id),
        FlatRegex::Complement(id) => FlatRegex::Complement(*id),
    })
}

/// Validate before interning, then encode each stored constant exactly once.
/// Repeated edges, unreachable nodes, and non-last roots remain untouched.
pub fn lower_flat<C, M: FlatEncoder<C>, L: Limits>(
    source: &FlatPair<C>,
    encoder: &mut M,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<FlatPair<u64>, HistoryError> {
    if source.validate().is_err() {
        return Err(invalid_source());
    }
    let mut head = Vec::new();
    if world
        .try_reserve_vec_exact(&mut head, source.head.len())
        .is_err()
    {
        return Err(HistoryError::AllocationFailed);
    }
    limits.enforce_memory()?;
    for (index, slot) in source.head.iter().enumerate() {
        limits.checkpoint()?;
        head.push(encode_head(slot, Component::new(index), encoder)?);
    }
    let mut builder = FlatBuilder::new(head);
    for test in &source.tests {
        limits.checkpoint()?;
        let node = encode_test(test, encoder, limits, world)?;
        builder.test(node, limits, world)?;
    }
    for regex in &source.regexes {
        limits.checkpoint()?;
        let node = copy_regex(regex, limits, world)?;
        builder.regex(node, limits, world)?;
    }
    builder.finish(source.root)
}
