//! Constant encoding preserves portable DAG topology; graph compilation is separate.

use crate::errors::HistoryError;
use crate::flat::{FlatBuilder, FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use crate::limits::Limits;
use crate::observation::ObservationWorld;
#[cfg(verus_keep_ghost)]
use crate::verify::encoding::*;
#[cfg(verus_keep_ghost)]
use crate::verify::history_specs::no_invariant_failure;
use alloc::vec::Vec;
use history_syntax::Event;
#[cfg(verus_keep_ghost)]
use history_syntax::event::specs::EventSpec;
use history_syntax::syntax::Component;
use vstd::prelude::*;

// Expand inside the trait contract: calling a FlatEncoder-bounded predicate there is cyclic.
#[cfg(verus_keep_ghost)]
macro_rules! encoder_wf_clause {
    ($model:ty, $($encoder:tt)+) => {
        vstd::prelude::verus_proof_expr! {
            ($($encoder)+).obeys_encoding_spec()
                && maps_wf(($($encoder)+).maps(), <$model>::equality(), <$model>::domain())
        }
    };
}

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
    spec fn encoding_calls(&self) -> nat;

    open spec fn state_wf(&self) -> bool { true }

    /// Opt in only when valid component requests cannot report structural failures.
    open spec fn errors_are_non_invariant(&self) -> bool { false }
    open spec fn errors_are_resource(&self) -> bool { false }

    // Keep the original books valid when a nested mutable encoder borrow ends.
    #[verifier::prophetic]
    spec fn restoration(&self) -> (Codebook<C>, bool);

    fn encode(&mut self, field: Component, value: &C) -> (result: Result<u64, HistoryError>)
        requires old(self).state_wf(),
        ensures final(self).state_wf(),
            final(self).restoration() == old(self).restoration(),
            final(self).errors_are_non_invariant() == old(self).errors_are_non_invariant(),
            final(self).errors_are_resource() == old(self).errors_are_resource(),
            old(self).errors_are_resource() && encoder_wf_clause!(Self, old(self))
                && Self::domain()(field, *value)
                ==> (result matches Err(error) ==> crate::spec::semantics::resource_error(error)),
            old(self).errors_are_non_invariant() && encoder_wf_clause!(Self, old(self))
                ==> no_invariant_failure(result)
                    && (Self::domain()(field, *value)
                        ==> !(result matches Err(HistoryError::InvalidPolicy { .. }))),
            encoder_wf_clause!(Self, old(self)) ==> {
            encoder_wf_clause!(Self, final(self))
            && extends(old(self).maps(), final(self).maps(), Self::equality())
            && grows_by(old(self).maps(), final(self).maps(), only_value(field, *value))
            && final(self).encoding_calls() == old(self).encoding_calls() + 1
            && match result {
                Ok(id) => Self::domain()(field, *value)
                    && encoded(final(self).maps(), Self::equality(), field, *value, id),
                Err(_) => true,
            }
        };
}

pub open spec fn encoder_wf<C, M: FlatEncoder<C>>(encoder: M) -> bool {
    encoder_wf_clause!(M, encoder)
}

/// Validate a typed constant's coordinate before touching a component codebook.
pub fn validate_component<E: Event>(field: Component, value: &E::Component)
    -> (result: Result<(), HistoryError>)
    ensures E::obeys_projection_spec() ==>
        result.is_ok() == (E::coordinate_spec(*value) == field.0 as nat),
    E::obeys_projection_spec() && result.is_ok() ==>
        field.0 < history_syntax::spec::events::arity::<E>(),
    result matches Err(error) ==> match error {
        HistoryError::InvalidPolicy { path, message } => path@ == "$"@
            && message == "constant belongs to another component",
        _ => false,
    },
{
    if E::coordinate(*value) == field.index() {
        Ok(())
    } else {
        Err(HistoryError::invalid_policy("$", "constant belongs to another component"))
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
        no_invariant_failure(result),
        !(result matches Err(HistoryError::InvalidPolicy { .. })),
        result matches Err(error) ==> crate::spec::semantics::resource_error(error),
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
    requires old(encoder).state_wf(),
    ensures final(encoder).state_wf(),
        result matches Ok(head) ==> head_shape(*source, head),
        final(encoder).restoration() == old(encoder).restoration(),
        final(encoder).errors_are_non_invariant() == old(encoder).errors_are_non_invariant(),
        final(encoder).errors_are_resource() == old(encoder).errors_are_resource(),
        old(encoder).errors_are_resource() && encoder_wf::<C, M>(*old(encoder))
            && head_in_domain(*source, field, M::domain())
            ==> (result matches Err(error) ==> crate::spec::semantics::resource_error(error)),
        encoder_wf::<C, M>(*old(encoder)) ==>
            final(encoder).encoding_calls() <= old(encoder).encoding_calls() + 1,
        old(encoder).errors_are_non_invariant() && encoder_wf::<C, M>(*old(encoder))
            ==> no_invariant_failure(result)
                && (head_in_domain(*source, field, M::domain())
                    ==> !(result matches Err(HistoryError::InvalidPolicy { .. }))),
        encoder_wf::<C, M>(*old(encoder)) ==> encoder_wf::<C, M>(*final(encoder))
            && extends(old(encoder).maps(), final(encoder).maps(), M::equality())
            && grows_by(old(encoder).maps(), final(encoder).maps(), head_constant_of(*source, field))
            && (result matches Ok(head) ==> head_encoded(*source, head, field, final(encoder).maps(), M::equality())
                && head_in_domain(*source, field, M::domain())),
{
    let ghost added = head_constant_of(*source, field);
    match source {
        FlatHead::Any => { proof { lemma_grows_by_refl(encoder.maps(), added); } Ok(FlatHead::Any) },
        FlatHead::Bind => { proof { lemma_grows_by_refl(encoder.maps(), added); } Ok(FlatHead::Bind) },
        FlatHead::Constant(value) => {
            let result = encoder.encode(field, value);
            proof { if encoder_wf::<C, M>(*old(encoder)) {
                lemma_grows_by_weaken(old(encoder).maps(), encoder.maps(), only_value(field, *value), added);
            } }
            Ok(FlatHead::Constant(result?))
        },
    }
}

fn encode_test<C, M: FlatEncoder<C>, L: Limits>(source: &FlatTest<C>, encoder: &mut M,
    limits: &mut L, world: &mut ObservationWorld) -> (result: Result<FlatTest<u64>, HistoryError>)
    requires old(encoder).state_wf(),
    ensures final(encoder).state_wf(),
        result matches Ok(test) ==> test_shape(*source, test),
        final(encoder).restoration() == old(encoder).restoration(),
        final(encoder).errors_are_non_invariant() == old(encoder).errors_are_non_invariant(),
        final(encoder).errors_are_resource() == old(encoder).errors_are_resource(),
        old(encoder).errors_are_resource() && encoder_wf::<C, M>(*old(encoder))
            && test_in_domain(*source, M::domain())
            ==> (result matches Err(error) ==> crate::spec::semantics::resource_error(error)),
        encoder_wf::<C, M>(*old(encoder)) ==>
            final(encoder).encoding_calls() <= old(encoder).encoding_calls() + 1,
        old(encoder).errors_are_non_invariant() && encoder_wf::<C, M>(*old(encoder))
            ==> no_invariant_failure(result)
                && (test_in_domain(*source, M::domain())
                    ==> !(result matches Err(HistoryError::InvalidPolicy { .. }))),
        encoder_wf::<C, M>(*old(encoder)) ==> encoder_wf::<C, M>(*final(encoder))
            && extends(old(encoder).maps(), final(encoder).maps(), M::equality())
            && grows_by(old(encoder).maps(), final(encoder).maps(), test_constant_of(*source))
            && (result matches Ok(test) ==> test_encoded(*source, test, final(encoder).maps(), M::equality())
                && test_in_domain(*source, M::domain())),
{
    let ghost added = test_constant_of(*source);
    proof { lemma_grows_by_refl(encoder.maps(), added); }
    match source {
        FlatTest::Bool(value) => Ok(FlatTest::Bool(*value)),
        FlatTest::Atom { field, term, positive } => {
            let term = match term {
                FlatTerm::Constant(value) => {
                    let result = encoder.encode(*field, value);
                    proof { if encoder_wf::<C, M>(*old(encoder)) {
                        lemma_grows_by_weaken(old(encoder).maps(), encoder.maps(), only_value(*field, *value), added);
                    } }
                    FlatTerm::Constant(result?)
                },
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
        no_invariant_failure(result),
        !(result matches Err(HistoryError::InvalidPolicy { .. })),
        result matches Err(error) ==> crate::spec::semantics::resource_error(error),
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
/// Encoders retain their error capability; opted-in well-formed encoders cannot
/// report internal failures, or invalid-policy errors for valid in-domain sources.
pub fn lower_flat<C, M: FlatEncoder<C>, L: Limits>(source: &FlatPair<C>, encoder: &mut M,
    limits: &mut L, world: &mut ObservationWorld) -> (result: Result<FlatPair<u64>, HistoryError>)
    requires old(encoder).state_wf(),
    ensures final(encoder).state_wf(),
        result matches Ok(target) ==> topology(*source, target)
            && crate::flat::verify::structural_wf(target),
        final(encoder).restoration() == old(encoder).restoration(),
        final(encoder).errors_are_non_invariant() == old(encoder).errors_are_non_invariant(),
        final(encoder).errors_are_resource() == old(encoder).errors_are_resource(),
        old(encoder).errors_are_resource() && encoder_wf::<C, M>(*old(encoder))
            && crate::flat::verify::structural_wf(*source) && constants_in_domain(*source, M::domain())
            ==> (result matches Err(error) ==> crate::spec::semantics::resource_error(error)),
        encoder_wf::<C, M>(*old(encoder)) ==>
            final(encoder).encoding_calls() <= old(encoder).encoding_calls()
                + source.head@.len() + source.tests@.len(),
        old(encoder).errors_are_non_invariant() && encoder_wf::<C, M>(*old(encoder))
            ==> no_invariant_failure(result)
                && (crate::flat::verify::structural_wf(*source)
                    && constants_in_domain(*source, M::domain())
                    ==> !(result matches Err(HistoryError::InvalidPolicy { .. }))),
        encoder_wf::<C, M>(*old(encoder)) ==> encoder_wf::<C, M>(*final(encoder))
            && extends(old(encoder).maps(), final(encoder).maps(), M::equality())
            && grows_by(old(encoder).maps(), final(encoder).maps(), source_constants(*source))
            && (result matches Ok(target) ==> lowering(*source, target, final(encoder).maps(), M::equality())
                && constants_in_domain(*source, M::domain())),
{
    if source.validate().is_err() {
        proof { lemma_grows_by_refl(encoder.maps(), source_constants(*source)); }
        return Err(invalid_source());
    }
    let ghost initial_maps = encoder.maps();
    let ghost verified = encoder_wf::<C, M>(*encoder);
    let ghost initial_calls = encoder.encoding_calls();
    proof { lemma_grows_by_refl(initial_maps, source_constants(*source)); }
    let mut head = Vec::new();
    if world.try_reserve_vec_exact(&mut head, source.head.len()).is_err() {
        return Err(HistoryError::AllocationFailed);
    }
    limits.enforce_memory()?;
    let mut index = 0;
    while index < source.head.len()
        invariant index <= source.head@.len(), head@.len() == index,
            encoder.state_wf(),
            crate::flat::verify::structural_wf(*source),
            encoder.restoration() == old(encoder).restoration(),
            encoder.errors_are_non_invariant() == old(encoder).errors_are_non_invariant(),
            encoder.errors_are_resource() == old(encoder).errors_are_resource(),
            initial_maps == old(encoder).maps(), verified == encoder_wf::<C, M>(*old(encoder)),
            initial_calls == old(encoder).encoding_calls(),
            verified ==> encoder.encoding_calls() <= initial_calls + index,
            (forall|i: int| 0 <= i < index ==> head_shape(source.head@[i], head@[i])),
            verified ==> encoder_wf::<C, M>(*encoder)
                && extends(initial_maps, encoder.maps(), M::equality())
                && grows_by(initial_maps, encoder.maps(), source_constants(*source))
                && (forall|i: int| 0 <= i < index ==> head_in_domain(source.head@[i], field_at(i), M::domain()))
                && (forall|i: int| 0 <= i < index ==> head_encoded(source.head@[i], head@[i], field_at(i), encoder.maps(), M::equality())),
        decreases source.head@.len() - index,
    {
        limits.checkpoint()?;
        let field = Component::new(index);
        let ghost before = encoder.maps();
        proof {
            assert(field == field_at(index as int));
            assert(constants_in_domain(*source, M::domain())
                ==> head_in_domain(source.head@[index as int], field, M::domain()));
        }
        let slot = encode_head(&source.head[index], field, encoder);
        proof {
            if verified {
                lemma_extends_transitive(initial_maps, before, encoder.maps(), M::equality());
                lemma_head_source_constant(*source, index as int);
                lemma_grows_by_transitive(initial_maps, before, encoder.maps(), source_constants(*source),
                    head_constant_of(source.head@[index as int], field), source_constants(*source));
                if slot is Ok {
                    assert forall|i: int| 0 <= i < index implies
                        head_encoded(source.head@[i], head@[i], field_at(i), encoder.maps(), M::equality()) by {
                        lemma_head_extends(source.head@[i], head@[i], field_at(i), before, encoder.maps(), M::equality());
                    }
                }
            }
        }
        let slot = slot?;
        head.push(slot);
        index += 1;
    }
    let mut builder = FlatBuilder::new(head);
    index = 0;
    while index < source.tests.len()
        invariant index <= source.tests@.len(), builder.wf(),
            encoder.state_wf(),
            crate::flat::verify::structural_wf(*source),
            encoder.restoration() == old(encoder).restoration(),
            encoder.errors_are_non_invariant() == old(encoder).errors_are_non_invariant(),
            encoder.errors_are_resource() == old(encoder).errors_are_resource(),
            initial_maps == old(encoder).maps(), verified == encoder_wf::<C, M>(*old(encoder)),
            initial_calls == old(encoder).encoding_calls(),
            verified ==> encoder.encoding_calls() <= initial_calls + source.head@.len() + index,
            builder.tests_view().len() == index, builder.regexes_view().len() == 0,
            builder.head_view().len() == source.head@.len(),
            (forall|i: int| 0 <= i < source.head@.len() ==> head_shape(source.head@[i], builder.head_view()[i])),
            (forall|i: int| 0 <= i < index ==> test_shape(source.tests@[i], builder.tests_view()[i])),
            verified ==> encoder_wf::<C, M>(*encoder)
                && extends(initial_maps, encoder.maps(), M::equality())
                && grows_by(initial_maps, encoder.maps(), source_constants(*source))
                && (forall|i: int| 0 <= i < source.head@.len() ==> head_in_domain(source.head@[i], field_at(i), M::domain()))
                && (forall|i: int| 0 <= i < index ==> test_in_domain(source.tests@[i], M::domain()))
                && (forall|i: int| 0 <= i < source.head@.len() ==> head_encoded(source.head@[i], builder.head_view()[i], field_at(i), encoder.maps(), M::equality()))
                && (forall|i: int| 0 <= i < index ==> test_encoded(source.tests@[i], builder.tests_view()[i], encoder.maps(), M::equality())),
        decreases source.tests@.len() - index,
    {
        limits.checkpoint()?;
        let ghost before = encoder.maps();
        proof {
            assert(encoder.state_wf());
            assert(encoder.errors_are_non_invariant() == old(encoder).errors_are_non_invariant());
            assert(verified ==> encoder_wf::<C, M>(*encoder));
            assert(constants_in_domain(*source, M::domain())
                ==> test_in_domain(source.tests@[index as int], M::domain()));
        }
        let node = encode_test(&source.tests[index], encoder, limits, world);
        proof {
            if verified {
                lemma_extends_transitive(initial_maps, before, encoder.maps(), M::equality());
                lemma_test_source_constant(*source, index as int);
                lemma_grows_by_transitive(initial_maps, before, encoder.maps(), source_constants(*source),
                    test_constant_of(source.tests@[index as int]), source_constants(*source));
            }
        }
        let node = node?;
        proof {
            assert(crate::flat::verify::test_wf(source.head@, source.tests@[index as int], index as nat));
            if let FlatTest::Atom { field, term: FlatTerm::Variable(_), .. } = node {
                let f = crate::flat::verify::field_index(field);
                assert(source.head@[f] is Bind);
                assert(builder.head_view()[f] is Bind);
            }
            assert(crate::flat::verify::test_wf(builder.head_view(), node, builder.tests_view().len()));
            if verified {
                assert forall|i: int| 0 <= i < source.head@.len() implies head_encoded(source.head@[i], builder.head_view()[i], field_at(i), encoder.maps(), M::equality()) by {
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
            encoder.state_wf(),
            crate::flat::verify::structural_wf(*source),
            encoder.restoration() == old(encoder).restoration(),
            encoder.errors_are_non_invariant() == old(encoder).errors_are_non_invariant(),
            encoder.errors_are_resource() == old(encoder).errors_are_resource(),
            initial_maps == old(encoder).maps(), verified == encoder_wf::<C, M>(*old(encoder)),
            initial_calls == old(encoder).encoding_calls(),
            verified ==> encoder.encoding_calls() <= initial_calls + source.head@.len() + source.tests@.len(),
            regex_tables_same(source.regexes@.take(index as int), builder.regexes_view()),
            builder.tests_view().len() == source.tests@.len(),
            builder.regexes_view().len() == index,
            builder.head_view().len() == source.head@.len(),
            (forall|i: int| 0 <= i < source.head@.len() ==> head_shape(source.head@[i], builder.head_view()[i])),
            (forall|i: int| 0 <= i < source.tests@.len() ==> test_shape(source.tests@[i], builder.tests_view()[i])),
            verified ==> encoder_wf::<C, M>(*encoder)
                && extends(initial_maps, encoder.maps(), M::equality())
                && grows_by(initial_maps, encoder.maps(), source_constants(*source))
                && constants_in_domain(*source, M::domain())
                && (forall|i: int| 0 <= i < source.head@.len() ==> head_encoded(source.head@[i], builder.head_view()[i], field_at(i), encoder.maps(), M::equality()))
                && (forall|i: int| 0 <= i < source.tests@.len() ==> test_encoded(source.tests@[i], builder.tests_view()[i], encoder.maps(), M::equality())),
        decreases source.regexes@.len() - index,
    {
        limits.checkpoint()?;
        let node = copy_regex(&source.regexes[index], limits, world)?;
        proof {
            assert(crate::flat::verify::regex_wf(source.regexes@[index as int], index as nat, source.tests@.len()));
            assert(crate::flat::verify::regex_wf(node, builder.regexes_view().len(), builder.tests_view().len()));
        }
        builder.regex(node, limits, world)?;
        index += 1;
    }
    proof { assert(source.root < builder.regexes_view().len()); }
    builder.finish(source.root)
}

}
