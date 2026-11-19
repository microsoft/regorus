//! Fallible, iterative lowering of the owned DSL into the canonical portable tables.

use crate::errors::{CompileError, HistoryError};
use crate::flat::{FlatBuilder, FlatHead, FlatPair, FlatRegex, FlatRule, FlatTerm, FlatTest};
use crate::limits::Limits;
use crate::observation::ObservationWorld;
use crate::scope::VariableScope;
use alloc::vec::Vec;
use history_syntax::syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use history_syntax::{Arity, Event};
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::verify::flatten::*;
#[cfg(verus_keep_ghost)]
use crate::verify::history_specs::{no_invariant_compile_failure, no_invariant_failure};
#[cfg(verus_keep_ghost)]
use history_syntax::event::specs::EventSpec;
#[cfg(verus_keep_ghost)]
use history_syntax::spec::events::arity;

#[cfg(verus_keep_ghost)]
verus! {
    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};
}

// Only borrowed source nodes enter the work stack: every failure leaves caller-owned trees intact.
#[verus_verify]
pub(crate) enum Work<'a, E: Event> {
    Regex(&'a RegexExpr<E>),
    Test(&'a TestExpr<E>),
    FinishRegex(&'a RegexExpr<E>, usize),
    FinishTest(&'a TestExpr<E>, usize),
}

#[verus_verify]
#[verus_spec(result => ensures
    result is Ok ==> final(values)@ == old(values)@.push(value),
    result is Err ==> final(values)@ == old(values)@,
    no_invariant_failure(result),
    !(result matches Err(HistoryError::InvalidPolicy { .. })),
    result matches Err(error) ==> crate::spec::semantics::resource_error(error),
)]
fn push<T, L: Limits>(
    values: &mut Vec<T>,
    value: T,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<(), HistoryError> {
    match world.try_reserve_vec(values, 1) {
        Ok(()) => {}
        Err(_) => return Err(HistoryError::AllocationFailed),
    }
    limits.enforce_memory()?;
    values.push(value);
    Ok(())
}

#[verus_verify]
#[verus_spec(result => ensures
    start <= old(values)@.len() ==> no_invariant_failure(result),
    !(result matches Err(HistoryError::InvalidPolicy { .. })),
    start <= old(values)@.len() ==> (result matches Err(error) ==> crate::spec::semantics::resource_error(error)),
    match result {
        Ok(children) => start <= old(values)@.len()
            && children@ == old(values)@.subrange(start as int, old(values)@.len() as int)
            && final(values)@ == old(values)@.subrange(0, start as int),
        Err(_) => final(values)@ == old(values)@,
    },
)]
fn take_children<L: Limits>(
    values: &mut Vec<u32>,
    start: usize,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<Vec<u32>, HistoryError> {
    if start > values.len() {
        return Err(HistoryError::invariant("invalid source operand range"));
    }
    let count = values.len() - start;
    let mut children = Vec::new();
    match world.try_reserve_vec_exact(&mut children, count) {
        Ok(()) => {}
        Err(_) => return Err(HistoryError::AllocationFailed),
    }
    limits.enforce_memory()?;
    let mut index = start;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start <= index <= values@.len(),
            children@ == values@.subrange(start as int, index as int),
        decreases values@.len() - index,
    ))]
    while index < values.len() {
        limits.checkpoint()?;
        children.push(values[index]);
        index += 1;
    }
    values.truncate(start);
    Ok(children)
}

#[verus_verify]
#[verus_spec(result => requires
    old(scope).wf(), old(scope).arity_spec() == arity::<E>(),
    forall|i: int| 0 <= i < arity::<E>() ==> #[trigger] old(scope).name_spec(Component(i as u8)) is None,
    ensures result matches Ok(flat) ==>
        head_represents::<E>(flat@, head@) && crate::spec::semantics::head_scoped(head@)
        && scope_matches::<E>(*final(scope), head@)
        && (E::obeys_projection_spec() ==> head_coordinates_wf::<E>(head@)),
    crate::spec::semantics::head_scoped(head@) ==>
        !(result matches Err(CompileError::VariableComponentConflict { .. })),
    !(result matches Err(CompileError::UnboundVariable { .. })),
    E::obeys_projection_spec() && head_coordinates_wf::<E>(head@)
        && crate::spec::semantics::head_scoped(head@) ==> result is Ok || result matches Err(CompileError::Runtime(_)),
    no_invariant_compile_failure(result),
    !(result matches Err(CompileError::Runtime(HistoryError::InvalidPolicy { .. }))),
    result matches Err(CompileError::Runtime(error)) ==> crate::spec::semantics::resource_error(error),
)]
fn flatten_head<'a, E: Event, L: Limits>(
    head: &'a Head<E>,
    scope: &mut VariableScope<'a>,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<Vec<FlatHead<E::Component>>, CompileError> {
    let arity = E::Arity::value();
    let slots = head.slots();
    if slots.len() != arity {
        return Err(CompileError::HeadArity {
            expected: arity,
            found: slots.len(),
        });
    }
    let mut flat = Vec::new();
    match world.try_reserve_vec_exact(&mut flat, arity) {
        Ok(()) => {}
        Err(_) => return Err(HistoryError::AllocationFailed.into()),
    }
    limits.enforce_memory().map_err(HistoryError::from)?;
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= arity, arity == history_syntax::spec::events::arity::<E>(),
            1 <= arity <= history_syntax::MAX_ARITY,
            head@.len() == arity, slots@.len() == arity,
            forall|i: int| 0 <= i < arity ==> slots@[i]@ == head@[i],
            flat@.len() == index, scope.wf(), scope.arity_spec() == arity,
            forall|i: int| 0 <= i < index ==> head_slot_represents(flat@[i], head@[i]),
            crate::spec::semantics::head_scoped(head@.take(index as int)),
            forall|i: int| 0 <= i < arity ==> match #[trigger] scope.name_spec(Component(i as u8)) {
                Some(name) => i < index && crate::spec::semantics::pattern_name(head@[i]) == Some(name@),
                None => i >= index || crate::spec::semantics::pattern_name(head@[i]) is None,
            },
            E::obeys_projection_spec() ==> forall|i: int| 0 <= i < index ==> match #[trigger] head@[i] {
                history_syntax::spec::events::PatternView::Constant(value) => E::coordinate_spec(value) == i,
                _ => true,
            },
        decreases arity - index,
    ))]
    while index < arity {
        limits.checkpoint().map_err(HistoryError::from)?;
        let component = Component::new(index);
        proof_decl! { let ghost previous_scope = *scope; }
        let slot = match &slots[index] {
            ComponentPattern::Constant(value) => {
                let coordinate = E::coordinate(*value);
                if coordinate != index {
                    return Err(CompileError::ComponentCoordinate {
                        component: index,
                        coordinate,
                    });
                }
                FlatHead::Constant(*value)
            }
            ComponentPattern::Variable(name) => {
                proof! {
                    if crate::spec::semantics::head_scoped(head@) {
                        assert forall|i: int| 0 <= i < scope.arity_spec() && i != component.0 implies
                            !(#[trigger] scope.has_name(Component(i as u8), name@)) by {
                            if i < index {
                                assert(crate::spec::semantics::distinct_names(head@[i], head@[index as int]));
                            }
                        }
                    }
                }
                scope.bind(component, name.as_str())?;
                proof! {
                    assert forall|i: int| 0 <= i < index implies
                        crate::spec::semantics::distinct_names(head@[i], head@[index as int]) by {
                        assert(!previous_scope.has_name(Component(i as u8), name@));
                    }
                }
                FlatHead::Bind
            }
        };
        proof! {
            assert forall|i: int, j: int| 0 <= i < j < index + 1 implies
                crate::spec::semantics::distinct_names(head@[i], head@[j]) by {
                if j < index {
                    assert(head@.take(index as int)[i] == head@[i]);
                    assert(head@.take(index as int)[j] == head@[j]);
                } else {
                    assert(j == index);
                }
            }
        }
        flat.push(slot);
        index += 1;
    }
    proof! { assert(head@.take(index as int) =~= head@); }
    Ok(flat)
}

#[verus_verify]
#[verus_spec(result => requires scope.wf(), scope.arity_spec() == arity::<E>(),
    ensures result matches Ok((field, term)) ==>
        (forall|head| scope_matches::<E>(*scope, head) ==> atom_term_represents::<E>(field, term, atom@, head))
        && (E::obeys_projection_spec() ==> atom_coordinates_wf::<E>(atom@)),
    no_invariant_compile_failure(result),
    atom@.component < scope.arity_spec() ==>
        !(result matches Err(CompileError::Runtime(HistoryError::InvalidPolicy { .. }))),
    forall|head| scope_matches::<E>(*scope, head) && crate::spec::semantics::atom_scoped(atom@, head) ==>
        !(result matches Err(CompileError::VariableComponentConflict { .. }))
        && !(result matches Err(CompileError::UnboundVariable { .. })),
    E::obeys_projection_spec() && atom_coordinates_wf::<E>(atom@) ==>
        (forall|head| scope_matches::<E>(*scope, head) && crate::spec::semantics::atom_scoped(atom@, head)
            ==> result is Ok),
)]
fn flatten_atom<E: Event>(
    atom: &AtomPattern<E>,
    scope: &VariableScope<'_>,
) -> Result<(Component, FlatTerm<E::Component>), CompileError> {
    let component = atom.component;
    let index = component.index();
    if index >= scope.arity() {
        return Err(HistoryError::invalid_policy(
            "atom.component",
            "component index is outside the event arity",
        )
        .into());
    }
    let term = match &atom.pattern {
        ComponentPattern::Constant(value) => {
            let coordinate = E::coordinate(*value);
            if coordinate != index {
                return Err(CompileError::ComponentCoordinate {
                    component: index,
                    coordinate,
                });
            }
            FlatTerm::Constant(*value)
        }
        ComponentPattern::Variable(name) => {
            FlatTerm::Variable(scope.resolve(component, name.as_str())?)
        }
    };
    Ok((component, term))
}

#[verus_verify]
#[verus_spec(result => ensures result is Ok ==> forall|ts, rs|
    run_work::<E>(final(work)@, ts, rs) == run_work::<E>(old(work)@, ts,
        rs + regex_views::<E>(children@)),
    result is Ok ==> work_cost::<E>(final(work)@) == work_cost::<E>(old(work)@)
        + regex_forest_cost::<E>(regex_views::<E>(children@)),
    no_invariant_failure(result),
    !(result matches Err(HistoryError::InvalidPolicy { .. })),
    result matches Err(error) ==> crate::spec::semantics::resource_error(error),
    result is Ok ==> forall|head| work_scoped::<E>(old(work)@, head)
        && (forall|i: int| 0 <= i < children@.len()
            ==> crate::spec::semantics::regex_scoped(children@[i]@, head))
        ==> work_scoped::<E>(final(work)@, head),
    result is Ok ==> forall|tail| work_within::<E>(old(work)@, tail)
        && (forall|i: int| 0 <= i < children@.len() ==> regex_constants_within(children@[i]@, tail))
        ==> work_within::<E>(final(work)@, tail),
)]
fn schedule_regexes<'a, E: Event, L: Limits>(
    work: &mut Vec<Work<'a, E>>,
    children: &'a [RegexExpr<E>],
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<(), HistoryError> {
    proof_decl! { let ghost before = work@; }
    let mut index = children.len();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= children@.len(),
            forall|ts, rs| run_work::<E>(work@, ts, rs)
                == run_work::<E>(before, ts, rs + regex_views::<E>(children@.subrange(index as int, children@.len() as int))),
            work_cost::<E>(work@) == work_cost::<E>(before)
                + regex_forest_cost::<E>(regex_views::<E>(children@.subrange(index as int, children@.len() as int))),
            forall|head| work_scoped::<E>(before, head)
                && (forall|i: int| 0 <= i < children@.len()
                    ==> crate::spec::semantics::regex_scoped(children@[i]@, head))
                ==> work_scoped::<E>(work@, head),
            forall|tail| work_within::<E>(before, tail)
                && (forall|i: int| 0 <= i < children@.len() ==> regex_constants_within(children@[i]@, tail))
                ==> work_within::<E>(work@, tail),
        decreases index,
    ))]
    while index > 0 {
        limits.checkpoint()?;
        proof_decl! { let ghost previous = work@; }
        index -= 1;
        push(work, Work::Regex(&children[index]), limits, world)?;
        proof! {
            assert(work@.drop_last() =~= previous);
            assert forall|head| work_scoped::<E>(before, head)
                && (forall|i: int| 0 <= i < children@.len()
                    ==> crate::spec::semantics::regex_scoped(children@[i]@, head))
                implies work_scoped::<E>(work@, head) by {
                lemma_work_scoped_push::<E>(previous, Work::Regex(&children[index as int]), head);
            }
            assert forall|tail| work_within::<E>(before, tail)
                && (forall|i: int| 0 <= i < children@.len() ==> regex_constants_within(children@[i]@, tail))
                implies work_within::<E>(work@, tail) by {
                lemma_work_within_push::<E>(previous, Work::Regex(&children[index as int]), tail);
            }
            assert(match work@.last() { Work::Regex(source) => source@ == children@[index as int]@, _ => false });
            reveal_with_fuel(regex_forest_cost, 2);
            let suffix = regex_views::<E>(children@.subrange(index as int + 1, children@.len() as int));
            assert(regex_views::<E>(children@.subrange(index as int, children@.len() as int))
                =~= seq![children@[index as int]@] + suffix);
            lemma_regex_forest_cost_append::<E>(seq![children@[index as int]@], suffix);
            reveal_with_fuel(run_work, 2);
            reveal_with_fuel(work_cost, 2);
            assert forall|ts, rs| run_work::<E>(work@, ts, rs)
                == run_work::<E>(before, ts, rs + regex_views::<E>(children@.subrange(index as int, children@.len() as int))) by {
                assert(run_work::<E>(work@, ts, rs)
                    == run_work::<E>(previous, ts, rs.push(children@[index as int]@)));
                assert(rs.push(children@[index as int]@) + suffix
                    =~= rs + regex_views::<E>(children@.subrange(index as int, children@.len() as int)));
            }
            assert(work_cost::<E>(work@) == work_cost::<E>(previous) + regex_cost::<E>(children@[index as int]@));
        }
    }
    proof! { assert(children@.subrange(0, children@.len() as int) =~= children@); }
    Ok(())
}

#[verus_verify]
#[verus_spec(result => ensures result is Ok ==> forall|ts, rs|
    run_work::<E>(final(work)@, ts, rs) == run_work::<E>(old(work)@,
        ts + test_views::<E>(children@), rs),
    result is Ok ==> work_cost::<E>(final(work)@) == work_cost::<E>(old(work)@)
        + test_forest_cost::<E>(test_views::<E>(children@)),
    no_invariant_failure(result),
    !(result matches Err(HistoryError::InvalidPolicy { .. })),
    result matches Err(error) ==> crate::spec::semantics::resource_error(error),
    result is Ok ==> forall|head| work_scoped::<E>(old(work)@, head)
        && (forall|i: int| 0 <= i < children@.len()
            ==> crate::spec::semantics::test_scoped(children@[i]@, head))
        ==> work_scoped::<E>(final(work)@, head),
    result is Ok ==> forall|tail| work_within::<E>(old(work)@, tail)
        && (forall|i: int| 0 <= i < children@.len() ==> test_constants_within(children@[i]@, tail))
        ==> work_within::<E>(final(work)@, tail),
)]
fn schedule_tests<'a, E: Event, L: Limits>(
    work: &mut Vec<Work<'a, E>>,
    children: &'a [TestExpr<E>],
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<(), HistoryError> {
    proof_decl! { let ghost before = work@; }
    let mut index = children.len();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= children@.len(),
            forall|ts, rs| run_work::<E>(work@, ts, rs)
                == run_work::<E>(before, ts + test_views::<E>(children@.subrange(index as int, children@.len() as int)), rs),
            work_cost::<E>(work@) == work_cost::<E>(before)
                + test_forest_cost::<E>(test_views::<E>(children@.subrange(index as int, children@.len() as int))),
            forall|head| work_scoped::<E>(before, head)
                && (forall|i: int| 0 <= i < children@.len()
                    ==> crate::spec::semantics::test_scoped(children@[i]@, head))
                ==> work_scoped::<E>(work@, head),
            forall|tail| work_within::<E>(before, tail)
                && (forall|i: int| 0 <= i < children@.len() ==> test_constants_within(children@[i]@, tail))
                ==> work_within::<E>(work@, tail),
        decreases index,
    ))]
    while index > 0 {
        limits.checkpoint()?;
        proof_decl! { let ghost previous = work@; }
        index -= 1;
        push(work, Work::Test(&children[index]), limits, world)?;
        proof! {
            assert(work@.drop_last() =~= previous);
            assert forall|head| work_scoped::<E>(before, head)
                && (forall|i: int| 0 <= i < children@.len()
                    ==> crate::spec::semantics::test_scoped(children@[i]@, head))
                implies work_scoped::<E>(work@, head) by {
                lemma_work_scoped_push::<E>(previous, Work::Test(&children[index as int]), head);
            }
            assert forall|tail| work_within::<E>(before, tail)
                && (forall|i: int| 0 <= i < children@.len() ==> test_constants_within(children@[i]@, tail))
                implies work_within::<E>(work@, tail) by {
                lemma_work_within_push::<E>(previous, Work::Test(&children[index as int]), tail);
            }
            assert(match work@.last() { Work::Test(source) => source@ == children@[index as int]@, _ => false });
            reveal_with_fuel(test_forest_cost, 2);
            let suffix = test_views::<E>(children@.subrange(index as int + 1, children@.len() as int));
            assert(test_views::<E>(children@.subrange(index as int, children@.len() as int))
                =~= seq![children@[index as int]@] + suffix);
            lemma_test_forest_cost_append::<E>(seq![children@[index as int]@], suffix);
            reveal_with_fuel(run_work, 2);
            reveal_with_fuel(work_cost, 2);
            assert forall|ts, rs| run_work::<E>(work@, ts, rs)
                == run_work::<E>(before, ts + test_views::<E>(children@.subrange(index as int, children@.len() as int)), rs) by {
                assert(run_work::<E>(work@, ts, rs)
                    == run_work::<E>(previous, ts.push(children@[index as int]@), rs));
                assert(ts.push(children@[index as int]@) + suffix
                    =~= ts + test_views::<E>(children@.subrange(index as int, children@.len() as int)));
            }
            assert(work_cost::<E>(work@) == work_cost::<E>(previous) + test_cost::<E>(children@[index as int]@));
        }
    }
    proof! { assert(children@.subrange(0, children@.len() as int) =~= children@); }
    Ok(())
}

/// Lowers a rule through the borrowed-source flattener.
#[verus_verify]
#[verus_spec(result => ensures
    no_invariant_compile_failure(result),
    crate::spec::semantics::regex_scoped(rule.tail@, rule.head@) ==>
        !(result matches Err(CompileError::Runtime(HistoryError::InvalidPolicy { .. }))),
    crate::spec::semantics::head_scoped(rule.head@)
        && crate::spec::semantics::regex_scoped(rule.tail@, rule.head@)
        ==> !(result matches Err(CompileError::VariableComponentConflict { .. }))
            && !(result matches Err(CompileError::UnboundVariable { .. })),
    result matches Ok(flat) ==> flattened::<E>(*rule, flat)
        && (E::obeys_projection_spec() ==> crate::verify::encoding::constants_in_domain(flat.source, component_domain::<E>())),
    result matches Ok(flat) ==> flat.source.tests@.len() + flat.source.regexes@.len()
        <= regex_cost::<E>(rule.tail@),
    crate::spec::hypotheses::event_obligations::<E>() && crate::spec::semantics::rule_wf(rule@)
        && rule@.head.len() == arity::<E>() && crate::spec::semantics::rule_constants_tagged::<E>(rule@)
        ==> (result is Ok || (result matches Err(CompileError::Runtime(error)) && crate::spec::semantics::resource_error(error))),
)]
pub fn flatten_rule<E: Event, L: Limits>(
    rule: &Rule<E>,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<FlatRule<E::Component>, CompileError> {
    flatten_rule_parts(rule.mode, &rule.head, &rule.tail, limits, world)
}

/// Lowers borrowed syntax in source order without constructing an executable graph.
/// Resource failures propagate; well-scoped inputs cannot produce scope diagnostics.
/// The continuation invariant excludes internal stack and operand-guard failures.
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verifier::rlimit(90))]
#[verus_spec(result => ensures
    no_invariant_compile_failure(result),
    crate::spec::semantics::regex_scoped(source_tail@, source_head@) ==>
        !(result matches Err(CompileError::Runtime(HistoryError::InvalidPolicy { .. }))),
    crate::spec::semantics::head_scoped(source_head@)
        && crate::spec::semantics::regex_scoped(source_tail@, source_head@)
        ==> !(result matches Err(CompileError::VariableComponentConflict { .. }))
            && !(result matches Err(CompileError::UnboundVariable { .. })),
    result matches Ok(flat) ==> flattened::<E>(Rule { mode, head: *source_head, tail: *source_tail }, flat)
        && (E::obeys_projection_spec() ==> crate::verify::encoding::constants_in_domain(flat.source, component_domain::<E>())),
    result matches Ok(flat) ==> flat.source.tests@.len() + flat.source.regexes@.len()
        <= regex_cost::<E>(source_tail@),
    crate::spec::hypotheses::event_obligations::<E>()
        && crate::spec::semantics::rule_wf(Rule { mode, head: *source_head, tail: *source_tail }@)
        && source_head@.len() == arity::<E>()
        && crate::spec::semantics::rule_constants_tagged::<E>(Rule { mode, head: *source_head, tail: *source_tail }@)
        ==> (result is Ok || (result matches Err(CompileError::Runtime(error)) && crate::spec::semantics::resource_error(error))),
)]
pub fn flatten_rule_parts<E: Event, L: Limits>(
    mode: RuleMode,
    source_head: &Head<E>,
    source_tail: &RegexExpr<E>,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<FlatRule<E::Component>, CompileError> {
    proof_decl! { let ghost rule = Rule { mode, head: *source_head, tail: *source_tail }; }
    limits.checkpoint().map_err(HistoryError::from)?;
    let mut scope = VariableScope::new(E::Arity::value());
    proof! {
        if crate::spec::hypotheses::event_obligations::<E>() && crate::spec::semantics::rule_wf(rule@)
            && rule@.head.len() == arity::<E>() && crate::spec::semantics::rule_constants_tagged::<E>(rule@) {
            lemma_rule_head_coordinates::<E>(rule@);
        }
    }
    let head = flatten_head(source_head, &mut scope, limits, world)?;
    let mut builder = FlatBuilder::new(head);
    let mut work = Vec::new();
    let mut tests: Vec<u32> = Vec::new();
    let mut regexes: Vec<u32> = Vec::new();
    proof_decl! {
        let ghost mut test_sources = Seq::empty();
        let ghost mut regex_sources = Seq::empty();
    }
    push(&mut work, Work::Regex(source_tail), limits, world)?;
    proof! {
        reveal_with_fuel(work_cost, 2);
        assert(work_cost::<E>(work@) == regex_cost::<E>(rule.tail@));
        assert(run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@]))) by {
            reveal_with_fuel(run_work, 2);
        }
        if crate::spec::semantics::regex_scoped(rule.tail@, rule.head@) {
            assert(work_scoped::<E>(work@, rule.head@)) by { reveal(work_scoped); }
        }
        assert(work_within::<E>(work@, rule.tail@)) by { reveal(work_within); }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant builder.wf(),
            rule.head@ == source_head@, rule.tail@ == source_tail@,
            rule == (Rule { mode, head: *source_head, tail: *source_tail }),
            head_represents::<E>(builder.head_view(), rule.head@),
            crate::spec::semantics::head_scoped(rule.head@),
            scope_matches::<E>(scope, rule.head@),
            crate::spec::semantics::regex_scoped(rule.tail@, rule.head@)
                ==> work_scoped::<E>(work@, rule.head@),
            E::obeys_projection_spec() ==> forall|i: int| 0 <= i < builder.head_view().len()
                ==> crate::verify::encoding::head_in_domain(
                    builder.head_view()[i], crate::verify::encoding::field_at(i), component_domain::<E>()),
            E::obeys_projection_spec() ==> forall|i: int| 0 <= i < builder.tests_view().len()
                ==> crate::verify::encoding::test_in_domain(builder.tests_view()[i], component_domain::<E>()),
            work_within::<E>(work@, rule.tail@),
            forall|i: int| 0 <= i < builder.tests_view().len()
                ==> flat_test_within(#[trigger] builder.tests_view()[i], rule.tail@),
            result_stacks::<E>(builder.tests_view(), builder.regexes_view(), tests@, regexes@,
                test_sources, regex_sources, rule.head@),
            run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@])),
            builder.tests_view().len() + builder.regexes_view().len() + work_cost::<E>(work@)
                <= regex_cost::<E>(rule.tail@),
        decreases work_cost::<E>(work@),
    ))]
    while !work.is_empty() {
        limits.checkpoint().map_err(HistoryError::from)?;
        proof_decl! {
            let ghost old_tests = builder.tests_view();
            let ghost old_regexes = builder.regexes_view();
            let ghost old_work = work@;
            let ghost old_test_ids = tests@;
            let ghost old_regex_ids = regexes@;
            let ghost old_test_sources = test_sources;
            let ghost old_regex_sources = regex_sources;
        }
        let task = match work.pop() {
            Some(task) => task,
            None => return Err(HistoryError::invariant("missing source work").into()),
        };
        proof! {
            assert(old_work =~= work@.push(task));
            assert(old_work.drop_last() =~= work@);
            lemma_run_work_step::<E>(old_work, test_sources, regex_sources);
            if crate::spec::semantics::regex_scoped(rule.tail@, rule.head@) {
                lemma_work_scoped_pop::<E>(old_work, rule.head@);
                assert(work_scoped::<E>(work@, rule.head@));
            }
            lemma_work_within_pop::<E>(old_work, rule.tail@);
            reveal_with_fuel(work_cost, 2);
            reveal_with_fuel(history_syntax::spec::events::regex_view, 2);
            reveal_with_fuel(history_syntax::spec::events::test_view, 2);
            reveal(regex_cost);
            reveal(test_cost);
        }
        match task {
            Work::Regex(regex) => match regex {
                RegexExpr::Empty | RegexExpr::All | RegexExpr::Epsilon => {
                    let node = match regex {
                        RegexExpr::Empty => FlatRegex::Empty,
                        RegexExpr::All => FlatRegex::All,
                        _ => FlatRegex::Epsilon,
                    };
                    let id = builder.regex(node, limits, world)?;
                    proof! {
                        assert(builder.tests_view().take(old_tests.len() as int) =~= old_tests);
                        assert(builder.regexes_view().take(old_regexes.len() as int) =~= old_regexes);
                        lemma_stack_extension::<E>(old_tests, builder.tests_view(), old_regexes, builder.regexes_view(),
                            old_test_ids, old_regex_ids, old_test_sources, old_regex_sources, rule.head@);
                        assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), id as nat, regex@, rule.head@));
                    }
                    push(&mut regexes, id, limits, world)?;
                    proof! { regex_sources = regex_sources.push(regex@); }
                }
                RegexExpr::Test(test) => {
                    proof! {
                        lemma_visit_test_regex::<E>(work@, regex, test, tests.len(), test_sources, regex_sources, rule.head@, rule.tail@);
                        lemma_work_cost_push::<E>(work@, Work::FinishRegex(regex, tests.len()));
                        lemma_work_cost_push::<E>(work@.push(Work::FinishRegex(regex, tests.len())), Work::Test(test));
                    }
                    push(
                        &mut work,
                        Work::FinishRegex(regex, tests.len()),
                        limits,
                        world,
                    )?;
                    push(&mut work, Work::Test(test), limits, world)?;
                    proof! {
                        assert(run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@])));
                        assert(work_cost::<E>(work@) < work_cost::<E>(old_work));
                    }
                }
                RegexExpr::Star(child) | RegexExpr::Not(child) => {
                    proof! {
                        lemma_visit_unary_regex::<E>(work@, regex, child, regexes.len(), test_sources, regex_sources, rule.head@, rule.tail@);
                        lemma_work_cost_push::<E>(work@, Work::FinishRegex(regex, regexes.len()));
                        lemma_work_cost_push::<E>(work@.push(Work::FinishRegex(regex, regexes.len())), Work::Regex(child));
                    }
                    push(
                        &mut work,
                        Work::FinishRegex(regex, regexes.len()),
                        limits,
                        world,
                    )?;
                    push(&mut work, Work::Regex(child), limits, world)?;
                    proof! {
                        assert(run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@])));
                        assert(work_cost::<E>(work@) < work_cost::<E>(old_work));
                    }
                }
                RegexExpr::Concat(children)
                | RegexExpr::Union(children)
                | RegexExpr::Intersect(children) => {
                    proof! { match regex@ {
                        history_syntax::spec::events::RegexView::Concat(items) | history_syntax::spec::events::RegexView::Union(items)
                            | history_syntax::spec::events::RegexView::Intersect(items) => assert(items =~= regex_views::<E>(children@)),
                        _ => {},
                    } }
                    proof! {
                        lemma_finish_many_regex::<E>(work@, regex, regexes.len(), test_sources, regex_sources, regex_views::<E>(children@), rule.head@, rule.tail@);
                        if crate::spec::semantics::regex_scoped(rule.tail@, rule.head@) {
                            assert forall|i: int| 0 <= i < children@.len() implies
                                crate::spec::semantics::regex_scoped(children@[i]@, rule.head@) by {
                                assert(regex_views::<E>(children@)[i] == children@[i]@);
                            }
                        }
                        assert forall|i: int| 0 <= i < children@.len() implies
                            regex_constants_within(children@[i]@, rule.tail@) by {
                            assert(regex_views::<E>(children@)[i] == children@[i]@);
                        }
                        lemma_work_cost_push::<E>(work@, Work::FinishRegex(regex, regexes.len()));
                        assert(regex_cost::<E>(regex@) == 2 + regex_forest_cost::<E>(regex_views::<E>(children@)));
                    }
                    push(
                        &mut work,
                        Work::FinishRegex(regex, regexes.len()),
                        limits,
                        world,
                    )?;
                    schedule_regexes(&mut work, children, limits, world)?;
                    proof! {
                        assert(run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@])));
                        assert(work_cost::<E>(work@) < work_cost::<E>(old_work));
                    }
                }
            },
            Work::Test(test) => match test {
                TestExpr::True | TestExpr::False | TestExpr::Atom { .. } => {
                    let node = match test {
                        TestExpr::True => FlatTest::Bool(true),
                        TestExpr::False => FlatTest::Bool(false),
                        TestExpr::Atom {
                            comparison,
                            pattern,
                        } => {
                            proof! {
                                if crate::spec::semantics::regex_scoped(rule.tail@, rule.head@) {
                                    assert(crate::spec::semantics::atom_scoped(pattern@, rule.head@)) by {
                                        reveal_with_fuel(crate::spec::semantics::test_scoped, 1);
                                    }
                                }
                            }
                            proof! {
                                if crate::spec::hypotheses::event_obligations::<E>() && crate::spec::semantics::rule_wf(rule@)
                                    && rule@.head.len() == arity::<E>() && crate::spec::semantics::rule_constants_tagged::<E>(rule@) {
                                    assert(test_constants_within(test@, rule.tail@));
                                    assert(atom_coordinates_wf::<E>(pattern@)) by {
                                        if let history_syntax::spec::events::PatternView::Constant(value) = pattern@.pattern {
                                            let i = pattern@.component as int;
                                            assert(crate::spec::questions::test_constant_at(test@, i).contains(value));
                                            assert(crate::spec::questions::regex_constant_at(rule.tail@, i).contains(value));
                                            assert(crate::spec::questions::rule_constants(rule@)[i].contains(value));
                                        }
                                    }
                                }
                            }
                            let atom_result = flatten_atom(pattern, &scope);
                            proof! {
                                if crate::spec::hypotheses::event_obligations::<E>()
                                    && crate::spec::semantics::rule_wf(Rule { mode, head: *source_head, tail: *source_tail }@)
                                    && source_head@.len() == arity::<E>()
                                    && crate::spec::semantics::rule_constants_tagged::<E>(Rule { mode, head: *source_head, tail: *source_tail }@) {
                                    assert(scope_matches::<E>(scope, rule.head@));
                                    assert(crate::spec::semantics::atom_scoped(pattern@, rule.head@));
                                    assert(atom_result is Ok);
                                }
                            }
                            let (field, term) = atom_result?;
                            FlatTest::Atom {
                                field,
                                term,
                                positive: matches!(comparison, Comparison::Eq),
                            }
                        }
                        _ => return Err(HistoryError::invariant("invalid source test leaf").into()),
                    };
                    proof! {
                        assert(crate::flat::verify::test_wf(builder.head_view(), node, builder.tests_view().len()));
                        assert(E::obeys_projection_spec() ==> crate::verify::encoding::test_in_domain(node, component_domain::<E>()));
                        if let TestExpr::Atom { pattern, .. } = test {
                            if let FlatTest::Atom { field, term: FlatTerm::Constant(value), .. } = &node {
                                assert(atom_term_represents::<E>(*field, FlatTerm::Constant(*value), pattern@, rule.head@));
                                assert(crate::spec::questions::test_constant_at(test@, field.0 as int).contains(*value));
                            }
                        }
                        assert(flat_test_within(node, rule.tail@));
                    }
                    let id = builder.test(node, limits, world)?;
                    proof! {
                        assert(builder.tests_view().take(old_tests.len() as int) =~= old_tests);
                        assert(builder.regexes_view().take(old_regexes.len() as int) =~= old_regexes);
                        lemma_stack_extension::<E>(old_tests, builder.tests_view(), old_regexes, builder.regexes_view(),
                            old_test_ids, old_regex_ids, old_test_sources, old_regex_sources, rule.head@);
                        assert(test_represents::<E>(builder.tests_view(), id as nat, test@, rule.head@));
                    }
                    push(&mut tests, id, limits, world)?;
                    proof! { test_sources = test_sources.push(test@); }
                }
                TestExpr::And(children) | TestExpr::Or(children) => {
                    proof! { match test@ {
                        history_syntax::spec::events::TestView::And(items) | history_syntax::spec::events::TestView::Or(items) =>
                            assert(items =~= test_views::<E>(children@)),
                        _ => {},
                    } }
                    proof! {
                        assert(test@ == history_syntax::spec::events::TestView::And(test_views::<E>(children@))
                            || test@ == history_syntax::spec::events::TestView::Or(test_views::<E>(children@)));
                        lemma_finish_test::<E>(work@, test, tests.len(), test_sources, regex_sources, test_views::<E>(children@), rule.head@, rule.tail@);
                        if crate::spec::semantics::regex_scoped(rule.tail@, rule.head@) {
                            assert forall|i: int| 0 <= i < children@.len() implies
                                crate::spec::semantics::test_scoped(children@[i]@, rule.head@) by {
                                assert(test_views::<E>(children@)[i] == children@[i]@);
                            }
                        }
                        assert forall|i: int| 0 <= i < children@.len() implies
                            test_constants_within(children@[i]@, rule.tail@) by {
                            assert(test_views::<E>(children@)[i] == children@[i]@);
                        }
                        assert(test_cost::<E>(test@) == 2 + test_forest_cost::<E>(test_views::<E>(children@)));
                    }
                    proof_decl! { let ghost prefix = work@; }
                    proof! { lemma_work_cost_push::<E>(prefix, Work::FinishTest(test, tests.len())); }
                    proof! { assert(work_cost::<E>(old_work) == work_cost::<E>(prefix) + test_cost::<E>(test@)); }
                    push(
                        &mut work,
                        Work::FinishTest(test, tests.len()),
                        limits,
                        world,
                    )?;
                    proof_decl! { let ghost finish = work@; }
                    proof! {
                        assert(finish.drop_last() =~= prefix);
                        assert(finish.last() is FinishTest);
                        assert(work_cost::<E>(finish) == work_cost::<E>(prefix) + 1);
                    }
                    schedule_tests(&mut work, children, limits, world)?;
                    proof! {
                        assert(run_work::<E>(work@, test_sources, regex_sources) == Some((Seq::empty(), seq![rule.tail@])));
                        assert(work_cost::<E>(work@) == work_cost::<E>(finish)
                            + test_forest_cost::<E>(test_views::<E>(children@)));
                        assert(work_cost::<E>(work@) < work_cost::<E>(old_work));
                    }
                }
            },
            Work::FinishTest(test, start) => {
                proof! {
                    assert(test@ is And || test@ is Or);
                    assert(start <= test_sources.len());
                    assert(start <= tests@.len());
                }
                let children = take_children(&mut tests, start, limits, world)?;
                proof_decl! { let ghost child_ids = children@; }
                let node = match test {
                    TestExpr::And(_) => FlatTest::And(children),
                    TestExpr::Or(_) => FlatTest::Or(children),
                    _ => return Err(HistoryError::invariant("invalid source test finish").into()),
                };
                proof! {
                    assert forall|i: int| 0 <= i < child_ids.len() implies
                        child_ids[i] < builder.tests_view().len() by {
                        assert(child_ids[i] == old_test_ids[start as int + i]);
                        assert(test_represents::<E>(builder.tests_view(), child_ids[i] as nat,
                            old_test_sources[start as int + i], rule.head@));
                    }
                    assert(crate::flat::verify::references_before(child_ids, builder.tests_view().len()));
                    assert(crate::flat::verify::test_wf(builder.head_view(), node, builder.tests_view().len()));
                }
                let id = builder.test(node, limits, world)?;
                proof! {
                    lemma_test_operands(builder.tests_view()[id as int]);
                    assert(builder.tests_view().take(old_tests.len() as int) =~= old_tests);
                    assert(builder.regexes_view().take(old_regexes.len() as int) =~= old_regexes);
                    lemma_stack_extension::<E>(old_tests, builder.tests_view(), old_regexes, builder.regexes_view(),
                        old_test_ids, old_regex_ids, old_test_sources, old_regex_sources, rule.head@);
                    let sources = match test@ {
                        history_syntax::spec::events::TestView::And(items) | history_syntax::spec::events::TestView::Or(items) => items,
                        _ => arbitrary(),
                    };
                    assert(old_test_sources.subrange(start as int, old_test_sources.len() as int) == sources);
                    assert forall|i: int| 0 <= i < sources.len() implies
                        test_represents::<E>(builder.tests_view(), child_ids[i] as nat, sources[i], rule.head@) by {
                        assert(child_ids[i] == old_test_ids[start as int + i]);
                        assert(sources[i] == old_test_sources[start as int + i]);
                    }
                    assert forall|i: int| 0 <= i < sources.len() implies
                        crate::spec::semantics::test_scoped(sources[i], rule.head@) by {
                        assert(test_represents::<E>(builder.tests_view(), child_ids[i] as nat, sources[i], rule.head@));
                    }
                    reveal_with_fuel(crate::spec::semantics::test_scoped, 2);
                    assert(crate::spec::semantics::test_scoped(test@, rule.head@));
                    assert(child_ids.len() == sources.len());
                    assert(crate::flat::verify::references_before(child_ids, id as nat));
                    assert(test_represents::<E>(builder.tests_view(), id as nat, test@, rule.head@));
                }
                push(&mut tests, id, limits, world)?;
                proof! { test_sources = test_sources.subrange(0, start as int).push(test@); }
            }
            Work::FinishRegex(regex, start) => {
                proof! {
                    assert(match regex@ {
                        history_syntax::spec::events::RegexView::Test(_) => test_sources.len() == start + 1,
                        history_syntax::spec::events::RegexView::Star(_) | history_syntax::spec::events::RegexView::Not(_)
                            => regex_sources.len() == start + 1,
                        history_syntax::spec::events::RegexView::Concat(_) | history_syntax::spec::events::RegexView::Union(_)
                            | history_syntax::spec::events::RegexView::Intersect(_) => start <= regex_sources.len(),
                        _ => false,
                    });
                }
                let node = match regex {
                    RegexExpr::Test(_) => {
                        proof! { assert(tests@.len() == start + 1); }
                        let child = match tests.pop() {
                            Some(child) => child,
                            None => {
                                return Err(
                                    HistoryError::invariant("missing source test operand").into()
                                );
                            }
                        };
                        proof! { test_sources = test_sources.drop_last(); }
                        FlatRegex::Test(child)
                    }
                    RegexExpr::Star(_) | RegexExpr::Not(_) => {
                        proof! { assert(regexes@.len() == start + 1); }
                        let child = match regexes.pop() {
                            Some(child) => child,
                            None => {
                                return Err(HistoryError::invariant(
                                    "missing source regex operand",
                                )
                                .into());
                            }
                        };
                        proof! { regex_sources = regex_sources.drop_last(); }
                        match regex {
                            RegexExpr::Star(_) => FlatRegex::Star(child),
                            _ => FlatRegex::Complement(child),
                        }
                    }
                    RegexExpr::Concat(_) | RegexExpr::Union(_) | RegexExpr::Intersect(_) => {
                        proof! { assert(start <= regexes@.len()); }
                        let children = take_children(&mut regexes, start, limits, world)?;
                        proof! { regex_sources = regex_sources.subrange(0, start as int); }
                        match regex {
                            RegexExpr::Concat(_) => FlatRegex::Concat(children),
                            RegexExpr::Union(_) => FlatRegex::Union(children),
                            _ => FlatRegex::Intersect(children),
                        }
                    }
                    _ => return Err(HistoryError::invariant("invalid source regex finish").into()),
                };
                proof_decl! { let ghost finished = node; }
                proof! {
                    lemma_regex_operands(node);
                    match node {
                        FlatRegex::Test(child) => {
                            assert(child == old_test_ids.last());
                            assert(test_represents::<E>(builder.tests_view(), child as nat,
                                old_test_sources.last(), rule.head@));
                        },
                        FlatRegex::Star(child) | FlatRegex::Complement(child) => {
                            assert(child == old_regex_ids.last());
                            assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), child as nat,
                                old_regex_sources.last(), rule.head@));
                        },
                        FlatRegex::Concat(ref ids) | FlatRegex::Union(ref ids) | FlatRegex::Intersect(ref ids) => {
                            assert forall|i: int| 0 <= i < ids@.len() implies
                                ids@[i] < builder.regexes_view().len() by {
                                assert(ids@[i] == old_regex_ids[start as int + i]);
                                assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), ids@[i] as nat,
                                    old_regex_sources[start as int + i], rule.head@));
                            }
                        },
                        _ => {},
                    }
                    assert(crate::flat::verify::regex_wf(node, builder.regexes_view().len(), builder.tests_view().len()));
                }
                let id = builder.regex(node, limits, world)?;
                proof! {
                    lemma_regex_operands(builder.regexes_view()[id as int]);
                    assert(builder.tests_view().take(old_tests.len() as int) =~= old_tests);
                    assert(builder.regexes_view().take(old_regexes.len() as int) =~= old_regexes);
                    lemma_stack_extension::<E>(old_tests, builder.tests_view(), old_regexes, builder.regexes_view(),
                        old_test_ids, old_regex_ids, old_test_sources, old_regex_sources, rule.head@);
                    match regex@ {
                        history_syntax::spec::events::RegexView::Test(source) => {
                            let child = match finished { FlatRegex::Test(id) => id, _ => arbitrary() };
                            assert(test_represents::<E>(builder.tests_view(), child as nat, source, rule.head@));
                        },
                        history_syntax::spec::events::RegexView::Star(source) | history_syntax::spec::events::RegexView::Not(source) => {
                            let child = match finished { FlatRegex::Star(id) | FlatRegex::Complement(id) => id, _ => arbitrary() };
                            assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), child as nat, *source, rule.head@));
                        },
                        history_syntax::spec::events::RegexView::Concat(sources) | history_syntax::spec::events::RegexView::Union(sources)
                            | history_syntax::spec::events::RegexView::Intersect(sources) => {
                            let ids = match finished {
                                FlatRegex::Concat(ids) | FlatRegex::Union(ids) | FlatRegex::Intersect(ids) => ids@,
                                _ => arbitrary(),
                            };
                            assert(old_regex_sources.subrange(start as int, old_regex_sources.len() as int) == sources);
                            assert forall|i: int| 0 <= i < sources.len() implies
                                regex_represents::<E>(builder.tests_view(), builder.regexes_view(), ids[i] as nat, sources[i], rule.head@) by {
                                assert(ids[i] == old_regex_ids[start as int + i]);
                                assert(sources[i] == old_regex_sources[start as int + i]);
                            }
                            assert forall|i: int| 0 <= i < sources.len() implies
                                crate::spec::semantics::regex_scoped(sources[i], rule.head@) by {
                                assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), ids[i] as nat, sources[i], rule.head@));
                            }
                        },
                        _ => {},
                    }
                    reveal_with_fuel(crate::spec::semantics::regex_scoped, 2);
                    assert(crate::spec::semantics::regex_scoped(regex@, rule.head@));
                    assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), id as nat, regex@, rule.head@));
                }
                push(&mut regexes, id, limits, world)?;
                proof! { regex_sources = regex_sources.push(regex@); }
            }
        }
        proof! {
            reveal(result_stacks);
            reveal_with_fuel(work_cost, 2);
            assert(work_cost::<E>(work@) < work_cost::<E>(old_work));
            assert(builder.tests_view().len() + builder.regexes_view().len()
                <= old_tests.len() + old_regexes.len() + 1);
            assert(builder.tests_view().len() + builder.regexes_view().len()
                + work_cost::<E>(work@) <= regex_cost::<E>(rule.tail@));
            if E::obeys_projection_spec() {
                assert forall|i: int| 0 <= i < builder.tests_view().len() implies
                    crate::verify::encoding::test_in_domain(builder.tests_view()[i], component_domain::<E>()) by {
                    if i < old_tests.len() { assert(builder.tests_view()[i] == old_tests[i]); }
                }
            }
            assert forall|i: int| 0 <= i < builder.tests_view().len() implies
                flat_test_within(#[trigger] builder.tests_view()[i], rule.tail@) by {
                if i < old_tests.len() { assert(builder.tests_view()[i] == old_tests[i]); }
            }
        }
    }
    proof! {
        reveal(result_stacks);
        reveal_with_fuel(run_work, 1);
        assert(test_sources =~= Seq::empty());
        assert(regex_sources =~= seq![rule.tail@]);
        assert(tests@.len() == 0);
        assert(regexes@.len() == 1);
    }
    if regexes.len() != 1 || !tests.is_empty() {
        return Err(HistoryError::invariant("invalid source result stack").into());
    }
    proof_decl! { let ghost result_ids = regexes@; }
    let root = match regexes.pop() {
        Some(root) => root,
        None => return Err(HistoryError::invariant("missing source root").into()),
    };
    proof! {
        assert(result_ids =~= seq![root]);
        assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), result_ids[0] as nat, regex_sources[0], rule.head@));
        assert(regex_represents::<E>(builder.tests_view(), builder.regexes_view(), root as nat, rule.tail@, rule.head@));
    }
    limits.checkpoint().map_err(HistoryError::from)?;
    let source: FlatPair<E::Component> = builder.finish(root)?;
    proof! {
        assert(head_represents::<E>(source.head@, rule.head@));
        assert(regex_represents::<E>(source.tests@, source.regexes@, source.root as nat, rule.tail@, rule.head@));
        assert(E::obeys_projection_spec() ==> crate::verify::encoding::constants_in_domain(source, component_domain::<E>()));
        assert(forall|i: int| 0 <= i < source.tests@.len() ==> flat_test_within(#[trigger] source.tests@[i], rule.tail@));
    }
    Ok(FlatRule { mode, source })
}
