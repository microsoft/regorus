//! Constant encoding preserves portable DAG topology; graph compilation is separate.

use crate::error::HistoryError;
use crate::flat::{FlatBuilder, FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use crate::flatten::ComponentValue;
use crate::limits::Limits;
use crate::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use crate::verify::encoding::*;
use alloc::vec::Vec;
use history_syntax::Event;
use history_syntax::syntax::Component;
use vstd::prelude::*;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// Component-specific constant encoding. Hashes are lookup aids, never identities.
///
/// Native implementations opt in to the ghost contract only after establishing
/// their equality/hash correspondence and finite-map implementation obligations.
pub trait FlatEncoder<C>: Sized {
    spec fn equality() -> Equality<C>;
    spec fn domain() -> Domain<C>;
    spec fn maps(&self) -> Codebook<C>;
    spec fn obeys_encoding_spec(&self) -> bool;

    // Keep the original books valid when a nested mutable encoder borrow ends.
    #[verifier::prophetic]
    spec fn restoration(&self) -> (Codebook<C>, bool);

    fn encode(&mut self, field: Component, value: &C) -> (result: Result<u64, HistoryError>)
        ensures final(self).restoration() == old(self).restoration(),
            old(self).obeys_encoding_spec()
            && maps_wf(old(self).maps(), Self::equality(), Self::domain()) ==> {
            final(self).obeys_encoding_spec()
            && maps_wf(final(self).maps(), Self::equality(), Self::domain())
            && extends(old(self).maps(), final(self).maps(), Self::equality())
            && match result {
                Ok(id) => Self::domain()(field, *value)
                    && encoded(final(self).maps(), Self::equality(), field, *value, id),
                Err(_) => true,
            }
        };
}

pub open spec fn encoder_wf<C, M: FlatEncoder<C>>(encoder: M) -> bool {
    encoder.obeys_encoding_spec() && maps_wf(encoder.maps(), M::equality(), M::domain())
}

/// Validate a typed constant's coordinate before touching a component codebook.
pub fn validate_component<E: Event>(field: Component, value: &ComponentValue<E>)
    -> (result: Result<(), HistoryError>)
    ensures result.is_ok() == match (field, *value) {
        (Component::Principal, ComponentValue::Principal(_))
        | (Component::Action, ComponentValue::Action(_))
        | (Component::Resource, ComponentValue::Resource(_)) => true,
        _ => false,
    },
    result matches Err(error) ==> match error {
        HistoryError::InvalidPolicy { path, message } => path@ == "$"@
            && message == "constant belongs to another component",
        _ => false,
    },
{
    match (field, value) {
        (Component::Principal, ComponentValue::Principal(_))
        | (Component::Action, ComponentValue::Action(_))
        | (Component::Resource, ComponentValue::Resource(_)) => Ok(()),
        _ => Err(HistoryError::invalid_policy("$", "constant belongs to another component")),
    }
}

fn invalid_source() -> (error: HistoryError)
    ensures match error {
        HistoryError::InvalidPolicy { path, message } => path@ == "$"@
            && message == "invalid portable history source",
        _ => false,
    },
{
    HistoryError::invalid_policy("$", "invalid portable history source")
}

fn copy_ids<L: Limits>(source: &[u32], limits: &mut L, world: &mut ObservationWorld)
    -> (result: Result<Vec<u32>, HistoryError>)
    ensures result matches Ok(ids) ==> ids@ == source@,
{
    let mut ids = Vec::new();
    match world.try_reserve_vec_exact(&mut ids, source.len()) {
        Ok(()) => {}, Err(_) => return Err(HistoryError::AllocationFailed),
    }
    let mut index = 0;
    while index < source.len()
        invariant index <= source@.len(), ids@ == source@.take(index as int),
        decreases source@.len() - index,
    {
        limits.checkpoint()?;
        ids.push(source[index]);
        index += 1;
    }
    Ok(ids)
}

fn encode_head<C, M: FlatEncoder<C>>(source: &FlatHead<C>, field: Component, encoder: &mut M)
    -> (result: Result<FlatHead<u64>, HistoryError>)
    ensures result matches Ok(head) ==> head_shape(*source, head),
        final(encoder).restoration() == old(encoder).restoration(),
        encoder_wf::<C, M>(*old(encoder)) ==> encoder_wf::<C, M>(*final(encoder))
            && extends(old(encoder).maps(), final(encoder).maps(), M::equality())
            && (result matches Ok(head) ==> head_encoded(*source, head, field, final(encoder).maps(), M::equality())
                && head_in_domain(*source, field, M::domain())),
{
    match source {
        FlatHead::Any => Ok(FlatHead::Any),
        FlatHead::Bind => Ok(FlatHead::Bind),
        FlatHead::Constant(value) => Ok(FlatHead::Constant(encoder.encode(field, value)?)),
    }
}

fn encode_test<C, M: FlatEncoder<C>, L: Limits>(source: &FlatTest<C>, encoder: &mut M,
    limits: &mut L, world: &mut ObservationWorld) -> (result: Result<FlatTest<u64>, HistoryError>)
    ensures result matches Ok(test) ==> test_shape(*source, test),
        final(encoder).restoration() == old(encoder).restoration(),
        encoder_wf::<C, M>(*old(encoder)) ==> encoder_wf::<C, M>(*final(encoder))
            && extends(old(encoder).maps(), final(encoder).maps(), M::equality())
            && (result matches Ok(test) ==> test_encoded(*source, test, final(encoder).maps(), M::equality())
                && test_in_domain(*source, M::domain())),
{
    match source {
        FlatTest::Bool(value) => Ok(FlatTest::Bool(*value)),
        FlatTest::Atom { field, term, positive } => {
            let term = match term {
                FlatTerm::Constant(value) => FlatTerm::Constant(encoder.encode(*field, value)?),
                FlatTerm::Variable(variable) => FlatTerm::Variable(*variable),
            };
            Ok(FlatTest::Atom { field: *field, term, positive: *positive })
        },
        FlatTest::And(children) => Ok(FlatTest::And(copy_ids(children, limits, world)?)),
        FlatTest::Or(children) => Ok(FlatTest::Or(copy_ids(children, limits, world)?)),
    }
}

fn copy_regex<L: Limits>(source: &FlatRegex, limits: &mut L, world: &mut ObservationWorld)
    -> (result: Result<FlatRegex, HistoryError>)
    ensures result matches Ok(regex) ==> regex_same(*source, regex),
{
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
pub fn lower_flat<C, M: FlatEncoder<C>, L: Limits>(source: &FlatPair<C>, encoder: &mut M,
    limits: &mut L, world: &mut ObservationWorld) -> (result: Result<FlatPair<u64>, HistoryError>)
    ensures result matches Ok(target) ==> topology(*source, target)
            && crate::flat::verify::structural_wf(target),
        final(encoder).restoration() == old(encoder).restoration(),
        encoder_wf::<C, M>(*old(encoder)) ==> encoder_wf::<C, M>(*final(encoder))
            && extends(old(encoder).maps(), final(encoder).maps(), M::equality())
            && (result matches Ok(target) ==> lowering(*source, target, final(encoder).maps(), M::equality())
                && constants_in_domain(*source, M::domain())),
{
    if source.validate().is_err() { return Err(invalid_source()); }
    let ghost initial_maps = encoder.maps();
    let ghost verified = encoder_wf::<C, M>(*encoder);
    let principal = encode_head(&source.head[0], Component::Principal, encoder)?;
    let ghost principal_maps = encoder.maps();
    let action = encode_head(&source.head[1], Component::Action, encoder)?;
    let ghost action_maps = encoder.maps();
    let resource = encode_head(&source.head[2], Component::Resource, encoder)?;
    proof {
        if verified {
            lemma_extends_transitive(initial_maps, principal_maps, action_maps, M::equality());
            lemma_extends_transitive(principal_maps, action_maps, encoder.maps(), M::equality());
            lemma_extends_transitive(initial_maps, action_maps, encoder.maps(), M::equality());
            lemma_head_extends(source.head@[0], principal, Component::Principal, principal_maps, encoder.maps(), M::equality());
            lemma_head_extends(source.head@[1], action, Component::Action, action_maps, encoder.maps(), M::equality());
        }
    }
    let mut builder = FlatBuilder::new([principal, action, resource]);
    let mut index = 0;
    while index < source.tests.len()
        invariant index <= source.tests@.len(), builder.wf(),
            encoder.restoration() == old(encoder).restoration(),
            initial_maps == old(encoder).maps(), verified == encoder_wf::<C, M>(*old(encoder)),
            builder.tests_view().len() == index, builder.regexes_view().len() == 0,
            (forall|i: int| 0 <= i < 3 ==> head_shape(source.head@[i], builder.head_view()[i])),
            (forall|i: int| 0 <= i < index ==> test_shape(source.tests@[i], builder.tests_view()[i])),
            verified ==> encoder_wf::<C, M>(*encoder)
                && extends(initial_maps, encoder.maps(), M::equality())
                && (forall|i: int| 0 <= i < 3 ==> head_in_domain(source.head@[i], field_at(i), M::domain()))
                && (forall|i: int| 0 <= i < index ==> test_in_domain(source.tests@[i], M::domain()))
                && (forall|i: int| 0 <= i < 3 ==> head_encoded(source.head@[i], builder.head_view()[i], field_at(i), encoder.maps(), M::equality()))
                && (forall|i: int| 0 <= i < index ==> test_encoded(source.tests@[i], builder.tests_view()[i], encoder.maps(), M::equality())),
        decreases source.tests@.len() - index,
    {
        limits.checkpoint()?;
        let ghost before = encoder.maps();
        let node = encode_test(&source.tests[index], encoder, limits, world)?;
        proof {
            if verified {
                lemma_extends_transitive(initial_maps, before, encoder.maps(), M::equality());
                assert forall|i: int| 0 <= i < 3 implies head_encoded(source.head@[i], builder.head_view()[i], field_at(i), encoder.maps(), M::equality()) by {
                    lemma_head_extends(source.head@[i], builder.head_view()[i], field_at(i), before, encoder.maps(), M::equality());
                }
                assert forall|i: int| 0 <= i < index implies test_encoded(source.tests@[i], builder.tests_view()[i], encoder.maps(), M::equality()) by {
                    lemma_test_extends(source.tests@[i], builder.tests_view()[i], before, encoder.maps(), M::equality());
                }
            }
        }
        builder.test(node, limits, world)?;
        index += 1;
    }
    index = 0;
    while index < source.regexes.len()
        invariant index <= source.regexes@.len(), builder.wf(),
            encoder.restoration() == old(encoder).restoration(),
            initial_maps == old(encoder).maps(), verified == encoder_wf::<C, M>(*old(encoder)),
            regex_tables_same(source.regexes@.take(index as int), builder.regexes_view()),
            builder.tests_view().len() == source.tests@.len(),
            (forall|i: int| 0 <= i < 3 ==> head_shape(source.head@[i], builder.head_view()[i])),
            (forall|i: int| 0 <= i < source.tests@.len() ==> test_shape(source.tests@[i], builder.tests_view()[i])),
            verified ==> encoder_wf::<C, M>(*encoder)
                && extends(initial_maps, encoder.maps(), M::equality())
                && constants_in_domain(*source, M::domain())
                && (forall|i: int| 0 <= i < 3 ==> head_encoded(source.head@[i], builder.head_view()[i], field_at(i), encoder.maps(), M::equality()))
                && (forall|i: int| 0 <= i < source.tests@.len() ==> test_encoded(source.tests@[i], builder.tests_view()[i], encoder.maps(), M::equality())),
        decreases source.regexes@.len() - index,
    {
        limits.checkpoint()?;
        let node = copy_regex(&source.regexes[index], limits, world)?;
        builder.regex(node, limits, world)?;
        index += 1;
    }
    builder.finish(source.root)
}

}
