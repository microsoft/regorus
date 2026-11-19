//! Node counters and constructor/disposal proofs for the owned DSL; the views live in
//! `crate::spec::events`.

use crate::Event;
use crate::spec::events::{RegexView, regex_view};
use crate::syntax::{ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr};
use alloc::boxed::Box;
use vstd::prelude::*;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};


/// Remaining source nodes, used to prove that iterative disposal terminates.
pub open spec fn test_nodes<E: Event>(test: TestExpr<E>) -> nat
    decreases test,
{
    1 + match test {
        TestExpr::And(children) | TestExpr::Or(children) => test_forest_nodes(children@),
        _ => 0,
    }
}

pub open spec fn test_forest_nodes<E: Event>(tests: Seq<TestExpr<E>>) -> nat
    decreases tests,
{
    if tests.len() == 0 { 0 }
    else { test_forest_nodes(tests.drop_last()) + test_nodes(tests.last()) }
}

pub open spec fn regex_nodes<E: Event>(regex: RegexExpr<E>) -> nat
    decreases regex,
{
    1 + match regex {
        RegexExpr::Union(children) | RegexExpr::Concat(children) | RegexExpr::Intersect(children) =>
            regex_forest_nodes(children@),
        RegexExpr::Star(child) | RegexExpr::Not(child) => regex_nodes(*child),
        _ => 0,
    }
}

pub open spec fn regex_forest_nodes<E: Event>(regexes: Seq<RegexExpr<E>>) -> nat
    decreases regexes,
{
    if regexes.len() == 0 { 0 }
    else { regex_forest_nodes(regexes.drop_last()) + regex_nodes(regexes.last()) }
}

pub proof fn lemma_test_forest_append<E: Event>(left: Seq<TestExpr<E>>, right: Seq<TestExpr<E>>)
    ensures test_forest_nodes(left + right) == test_forest_nodes(left) + test_forest_nodes(right),
    decreases right.len(),
{
    if right.len() > 0 {
        lemma_test_forest_append(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
        assert((left + right).last() == right.last());
    } else {
        assert(left + right =~= left);
    }
}

pub proof fn lemma_regex_forest_append<E: Event>(left: Seq<RegexExpr<E>>, right: Seq<RegexExpr<E>>)
    ensures regex_forest_nodes(left + right) == regex_forest_nodes(left) + regex_forest_nodes(right),
    decreases right.len(),
{
    if right.len() > 0 {
        lemma_regex_forest_append(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
        assert((left + right).last() == right.last());
    } else {
        assert(left + right =~= left);
    }
}

/// A real constructor/projection proof client, without a projection-obedience assumption.
pub fn constructor_client<E: Event>(slots: alloc::vec::Vec<ComponentPattern<E::Component>>)
    -> (rule: Rule<E>)
    ensures
        rule@.mode == RuleMode::Require,
        rule@.head == slots@.map(|i: int, pattern: ComponentPattern<E::Component>| pattern@),
        rule@.tail == RegexView::Not(Box::new(RegexView::Epsilon)),
{
    proof! { reveal_with_fuel(regex_view, 2); }
    let iter = slots.into_iter();
    proof! { vstd::std_specs::iter::axiom_from_iterator_ensures(iter); }
    let head = Head::new(iter);
    let tail = RegexExpr::complement(RegexExpr::epsilon());
    Rule::new(RuleMode::Require, head, tail)
}
}
