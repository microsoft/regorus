//! Structural views and constructor/disposal proofs for the owned DSL.

use crate::Event;
use crate::syntax::{
    AtomPattern, Comparison, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use alloc::boxed::Box;
use vstd::prelude::*;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

pub enum PatternView<T> {
    Constant(T),
    Variable(Seq<char>),
}

pub struct HeadView<P, A, R> {
    pub principal: PatternView<P>,
    pub action: PatternView<A>,
    pub resource: PatternView<R>,
}

pub enum AtomView<P, A, R> {
    Principal(PatternView<P>),
    Action(PatternView<A>),
    Resource(PatternView<R>),
}

pub enum TestView<P, A, R> {
    True,
    False,
    Atom { comparison: Comparison, pattern: AtomView<P, A, R> },
    And(Seq<TestView<P, A, R>>),
    Or(Seq<TestView<P, A, R>>),
}

/// The same algebra as the numeric history model, over concrete component values.
pub enum RegexView<P, A, R> {
    Empty, All, Epsilon,
    Test(TestView<P, A, R>),
    Union(Seq<RegexView<P, A, R>>),
    Concat(Seq<RegexView<P, A, R>>),
    Star(Box<RegexView<P, A, R>>),
    Intersect(Seq<RegexView<P, A, R>>),
    Not(Box<RegexView<P, A, R>>),
}

pub struct RuleView<P, A, R> {
    pub mode: RuleMode,
    pub head: HeadView<P, A, R>,
    pub tail: RegexView<P, A, R>,
}
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

impl<T> View for ComponentPattern<T> {
    type V = PatternView<T>;
    open spec fn view(&self) -> Self::V {
        match self {
            ComponentPattern::Constant(value) => PatternView::Constant(*value),
            ComponentPattern::Variable(name) => PatternView::Variable(name@),
        }
    }
}

impl<E: Event> View for Head<E> {
    type V = HeadView<E::Principal, E::Action, E::Resource>;
    open spec fn view(&self) -> Self::V {
        HeadView { principal: self.principal@, action: self.action@, resource: self.resource@ }
    }
}

impl<E: Event> View for AtomPattern<E> {
    type V = AtomView<E::Principal, E::Action, E::Resource>;
    open spec fn view(&self) -> Self::V {
        match self {
            AtomPattern::Principal(pattern) => AtomView::Principal(pattern@),
            AtomPattern::Action(pattern) => AtomView::Action(pattern@),
            AtomPattern::Resource(pattern) => AtomView::Resource(pattern@),
        }
    }
}

pub open spec fn test_view<E: Event>(test: TestExpr<E>) -> TestView<E::Principal, E::Action, E::Resource>
    decreases test,
{
    match test {
        TestExpr::True => TestView::True,
        TestExpr::False => TestView::False,
        TestExpr::Atom { comparison, pattern } => TestView::Atom { comparison, pattern: pattern@ },
        TestExpr::And(children) => TestView::And(Seq::new(children@.len(), |i: int|
            if 0 <= i < children@.len() { test_view(children@[i]) } else { TestView::False })),
        TestExpr::Or(children) => TestView::Or(Seq::new(children@.len(), |i: int|
            if 0 <= i < children@.len() { test_view(children@[i]) } else { TestView::False })),
    }
}

impl<E: Event> View for TestExpr<E> {
    type V = TestView<E::Principal, E::Action, E::Resource>;
    open spec fn view(&self) -> Self::V { test_view(*self) }
}

pub open spec fn regex_view<E: Event>(regex: RegexExpr<E>) -> RegexView<E::Principal, E::Action, E::Resource>
    decreases regex,
{
    match regex {
        RegexExpr::Empty => RegexView::Empty,
        RegexExpr::All => RegexView::All,
        RegexExpr::Epsilon => RegexView::Epsilon,
        RegexExpr::Test(test) => RegexView::Test(test_view(test)),
        RegexExpr::Union(children) => RegexView::Union(Seq::new(children@.len(), |i: int|
            if 0 <= i < children@.len() { regex_view(children@[i]) } else { RegexView::Empty })),
        RegexExpr::Concat(children) => RegexView::Concat(Seq::new(children@.len(), |i: int|
            if 0 <= i < children@.len() { regex_view(children@[i]) } else { RegexView::Empty })),
        RegexExpr::Star(child) => RegexView::Star(Box::new(regex_view(*child))),
        RegexExpr::Intersect(children) => RegexView::Intersect(Seq::new(children@.len(), |i: int|
            if 0 <= i < children@.len() { regex_view(children@[i]) } else { RegexView::Empty })),
        RegexExpr::Not(child) => RegexView::Not(Box::new(regex_view(*child))),
    }
}

impl<E: Event> View for RegexExpr<E> {
    type V = RegexView<E::Principal, E::Action, E::Resource>;
    open spec fn view(&self) -> Self::V { regex_view(*self) }
}

impl<E: Event> View for Rule<E> {
    type V = RuleView<E::Principal, E::Action, E::Resource>;
    open spec fn view(&self) -> Self::V {
        RuleView { mode: self.mode, head: self.head@, tail: self.tail@ }
    }
}
/// A real constructor/projection proof client, without a projection-obedience assumption.
pub fn constructor_client<E: Event>(principal: E::Principal, action: E::Action, resource: E::Resource)
    -> (rule: Rule<E>)
    ensures
        rule@.mode == RuleMode::Require,
        rule@.head.principal == PatternView::Constant(principal),
        rule@.head.action == PatternView::Constant(action),
        rule@.head.resource == PatternView::Constant(resource),
        rule@.tail == RegexView::Not(Box::new(RegexView::Epsilon)),
{
    proof! { reveal_with_fuel(regex_view, 2); }
    let head = Head::new(ComponentPattern::Constant(principal), ComponentPattern::Constant(action),
        ComponentPattern::Constant(resource));
    let tail = RegexExpr::complement(RegexExpr::epsilon());
    Rule::new(RuleMode::Require, head, tail)
}
}
