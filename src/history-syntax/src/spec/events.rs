//! Events as tagged component tuples, and the views of the owned DSL (paper: `sec:events`,
//! `sec:rules`).

use crate::event::specs::{AritySpec, EventSpec};
use crate::syntax::{
    AtomPattern, Comparison, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use crate::{Event, MAX_ARITY};
use alloc::boxed::Box;
use vstd::prelude::*;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// The number of coordinates of an event type (paper: product events, `sec:events`).
pub open spec fn arity<E: Event>() -> nat { E::Arity::value_spec() }

/// Every projection of an event carries its own coordinate as tag (`sec:events`).
pub open spec fn projection_laws<E: Event>() -> bool {
    forall|e: E, i: int| 0 <= i < arity::<E>() ==>
        E::coordinate_spec(e.component_spec(i)) == i
}

/// An event as the tuple of its tagged components, coordinate by coordinate (`sec:events`).
pub open spec fn event_view<E: Event>(e: E) -> Seq<E::Component> {
    Seq::new(arity::<E>(), |i: int| e.component_spec(i))
}

/// `xs` has the shape of an event: arity-many components, the i-th tagged with coordinate i
/// (paper: product events, `sec:events`).
pub open spec fn well_tagged<E: Event>(xs: Seq<E::Component>) -> bool {
    xs.len() == arity::<E>()
        && forall|i: int| 0 <= i < xs.len() ==> E::coordinate_spec(#[trigger] xs[i]) == i
}

/// Every well-tagged tuple is the view of some event; makes the tagged component type
/// equivalent to the paper's product domain (`sec:events`).
pub open spec fn views_surjective<E: Event>() -> bool {
    forall|xs: Seq<E::Component>| #[trigger] well_tagged::<E>(xs) ==> exists|e: E| event_view(e) == xs
}

/// Everything the semantics assumes about an event type's projections (`sec:events`).
pub open spec fn event_laws<E: Event>() -> bool {
    &&& 1 <= arity::<E>() <= MAX_ARITY
    &&& E::obeys_projection_spec()
    &&& projection_laws::<E>()
    &&& views_surjective::<E>()
}

pub enum PatternView<T> {
    Constant(T),
    Variable(Seq<char>),
}

pub type HeadView<C> = Seq<PatternView<C>>;

pub struct AtomView<C> {
    pub component: nat,
    pub pattern: PatternView<C>,
}

pub enum TestView<C> {
    True,
    False,
    Atom { comparison: Comparison, pattern: AtomView<C> },
    And(Seq<TestView<C>>),
    Or(Seq<TestView<C>>),
}

/// The same algebra as the numeric history model, over concrete component values.
pub enum RegexView<C> {
    Empty, All, Epsilon,
    Test(TestView<C>),
    Union(Seq<RegexView<C>>),
    Concat(Seq<RegexView<C>>),
    Star(Box<RegexView<C>>),
    Intersect(Seq<RegexView<C>>),
    Not(Box<RegexView<C>>),
}

pub struct RuleView<C> {
    pub mode: RuleMode,
    pub head: HeadView<C>,
    pub tail: RegexView<C>,
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
    type V = HeadView<E::Component>;
    open spec fn view(&self) -> Self::V {
        self.0@.map(|i: int, pattern: ComponentPattern<E::Component>| pattern@)
    }
}

impl<E: Event> View for AtomPattern<E> {
    type V = AtomView<E::Component>;
    open spec fn view(&self) -> Self::V {
        AtomView { component: self.component.0 as nat, pattern: self.pattern@ }
    }
}

pub open spec fn test_view<E: Event>(test: TestExpr<E>) -> TestView<E::Component>
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
    type V = TestView<E::Component>;
    open spec fn view(&self) -> Self::V { test_view(*self) }
}

pub open spec fn regex_view<E: Event>(regex: RegexExpr<E>) -> RegexView<E::Component>
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
    type V = RegexView<E::Component>;
    open spec fn view(&self) -> Self::V { regex_view(*self) }
}

impl<E: Event> View for Rule<E> {
    type V = RuleView<E::Component>;
    open spec fn view(&self) -> Self::V {
        RuleView { mode: self.mode, head: self.head@, tail: self.tail@ }
    }
}

} // verus!
