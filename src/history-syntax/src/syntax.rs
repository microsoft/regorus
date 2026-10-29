//! Owned source language for declarative policy rules over one [`Event`] type.
//!
//! Constants retain the event's concrete associated component types. Variables are local names;
//! source expressions contain no arena references, compiler identities or store backreferences.

use crate::event::Event;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::iter::FromIterator;
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::verify::dsl::{
    lemma_regex_forest_append, lemma_test_forest_append, regex_forest_nodes, regex_nodes,
    test_forest_nodes, test_nodes,
};
#[cfg(verus_keep_ghost)]
use vstd::std_specs::convert::IntoSpec;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::into_iter_remaining;

/// Constant-or-variable pattern for one statically selected product component.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ComponentPattern<T, Variable = String> {
    /// Match one equal component value, using the component's equality relation.
    Constant(T),
    /// Bind or resolve a named component value.
    Variable(Variable),
}

#[verus_verify]
impl<T> ComponentPattern<T, String> {
    /// Creates a constant pattern from a value convertible to `T`.
    #[verus_spec(result => ensures
        result is Constant,
        I::obeys_into_spec() ==> result == Self::Constant(value.into_spec()),
    )]
    pub fn constant<I: Into<T>>(value: I) -> Self {
        Self::Constant(value.into())
    }

    /// Creates a named variable pattern.
    #[verus_spec(result => ensures
        result is Variable,
        I::obeys_into_spec() ==> result == Self::Variable(name.into_spec()),
    )]
    pub fn variable<I: Into<String>>(name: I) -> Self {
        Self::Variable(name.into())
    }
}

/// Candidate-only pattern over the capability product.
/// Variables declared here may be resolved only in the same tail coordinate.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Head<E: Event> {
    /// Principal constant or variable.
    pub principal: ComponentPattern<E::Principal>,
    /// Action constant or variable.
    pub action: ComponentPattern<E::Action>,
    /// Resource constant or variable.
    pub resource: ComponentPattern<E::Resource>,
}

#[verus_verify]
impl<E: Event> Head<E> {
    /// Creates a typed `(principal, action, resource)` head.
    #[verus_spec(result => ensures result.principal == principal,
        result.action == action, result.resource == resource)]
    pub fn new(
        principal: ComponentPattern<E::Principal>,
        action: ComponentPattern<E::Action>,
        resource: ComponentPattern<E::Resource>,
    ) -> Self {
        Self {
            principal,
            action,
            resource,
        }
    }
}

/// Coordinate of the capability product; order is part of the portable format.
#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(verus_keep_ghost, derive(Structural))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Component {
    /// Principal coordinate.
    Principal,
    /// Action coordinate.
    Action,
    /// Resource coordinate.
    Resource,
}

#[verus_verify]
impl Component {
    /// Returns the coordinate's position in a portable head.
    #[verus_spec(result => ensures result == match self {
        Self::Principal => 0usize, Self::Action => 1usize, Self::Resource => 2usize,
    })]
    pub const fn index(self) -> usize {
        match self {
            Self::Principal => 0,
            Self::Action => 1,
            Self::Resource => 2,
        }
    }
}

/// Comparison applied by a one-event atom.
#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(verus_keep_ghost, derive(Structural))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Comparison {
    /// Accept equal component values.
    Eq,
    /// Accept unequal component values.
    Neq,
}

#[verus_verify]
impl core::ops::Not for Comparison {
    type Output = Self;

    #[verus_spec(result => ensures result == match self {
        Self::Eq => Self::Neq, Self::Neq => Self::Eq,
    })]
    fn not(self) -> Self::Output {
        match self {
            Self::Eq => Self::Neq,
            Self::Neq => Self::Eq,
        }
    }
}

/// Owned one-event component pattern.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AtomPattern<E: Event> {
    /// Test the event principal.
    Principal(ComponentPattern<E::Principal>),
    /// Test the event action.
    Action(ComponentPattern<E::Action>),
    /// Test the event resource.
    Resource(ComponentPattern<E::Resource>),
}

#[verus_verify]
impl<E: Event> AtomPattern<E> {
    /// Returns the product coordinate selected by this atom.
    #[verus_spec(result => ensures result == match self {
        Self::Principal(_) => Component::Principal,
        Self::Action(_) => Component::Action,
        Self::Resource(_) => Component::Resource,
    })]
    pub fn component(&self) -> Component {
        match self {
            Self::Principal(_) => Component::Principal,
            Self::Action(_) => Component::Action,
            Self::Resource(_) => Component::Resource,
        }
    }
}

/// Owned boolean expression over one history event.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TestExpr<E: Event> {
    /// Predicate accepting every event.
    True,
    /// Predicate accepting no event.
    False,
    /// Component equality or disequality predicate.
    Atom {
        /// Comparison applied after resolving the component pattern.
        comparison: Comparison,
        /// Typed component pattern.
        pattern: AtomPattern<E>,
    },
    /// Conjunction. Empty input is true.
    And(Vec<TestExpr<E>>),
    /// Disjunction. Empty input is false.
    Or(Vec<TestExpr<E>>),
}

#[verus_verify]
impl<E: Event> TestExpr<E> {
    /// Returns the predicate accepting every event.
    #[verus_spec(result => ensures result is True)]
    pub const fn true_test() -> Self {
        Self::True
    }

    /// Returns the predicate accepting no event.
    #[verus_spec(result => ensures result is False)]
    pub const fn false_test() -> Self {
        Self::False
    }

    /// Creates a component equality or disequality predicate.
    #[verus_spec(result => ensures result == (Self::Atom { comparison, pattern }))]
    pub fn atom(comparison: Comparison, pattern: AtomPattern<E>) -> Self {
        Self::Atom {
            comparison,
            pattern,
        }
    }

    /// Conjoins source predicates in iterator order.
    #[verus_spec(result => ensures match result {
        Self::And(children) => children@ == into_iter_remaining(tests), _ => false,
    })]
    pub fn and<I: IntoIterator<Item = TestExpr<E>>>(tests: I) -> Self {
        Self::And(Vec::from_iter(tests))
    }

    /// Disjoins source predicates in iterator order.
    #[verus_spec(result => ensures match result {
        Self::Or(children) => children@ == into_iter_remaining(tests), _ => false,
    })]
    pub fn or<I: IntoIterator<Item = TestExpr<E>>>(tests: I) -> Self {
        Self::Or(Vec::from_iter(tests))
    }
}

/// Owned regular expression over complete event histories.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RegexExpr<E: Event> {
    /// Empty language.
    Empty,
    /// Universal language over complete histories.
    All,
    /// Language containing only the empty history.
    Epsilon,
    /// One-event language selected by a boolean source expression.
    Test(TestExpr<E>),
    /// Set union. Empty input is the empty language.
    Union(Vec<RegexExpr<E>>),
    /// Ordered language concatenation. Empty input is epsilon.
    Concat(Vec<RegexExpr<E>>),
    /// Kleene star.
    Star(Box<RegexExpr<E>>),
    /// Set intersection. Empty input is the universal language.
    Intersect(Vec<RegexExpr<E>>),
    /// Whole-language complement, not a one-event negation.
    Not(Box<RegexExpr<E>>),
}

#[verus_verify]
impl<E: Event> RegexExpr<E> {
    /// Returns the empty language.
    #[verus_spec(result => ensures result is Empty)]
    pub const fn empty() -> Self {
        Self::Empty
    }

    /// Returns the universal language.
    #[verus_spec(result => ensures result is All)]
    pub const fn all() -> Self {
        Self::All
    }

    /// Returns the language containing only the empty history.
    #[verus_spec(result => ensures result is Epsilon)]
    pub const fn epsilon() -> Self {
        Self::Epsilon
    }

    /// Lifts a one-event predicate into a one-event language.
    #[verus_spec(result => ensures result == Self::Test(test))]
    pub fn test(test: TestExpr<E>) -> Self {
        Self::Test(test)
    }

    /// Constructs set union in iterator order.
    #[verus_spec(result => ensures match result {
        Self::Union(children) => children@ == into_iter_remaining(regexes), _ => false,
    })]
    pub fn union<I: IntoIterator<Item = RegexExpr<E>>>(regexes: I) -> Self {
        Self::Union(Vec::from_iter(regexes))
    }

    /// Constructs ordered language concatenation.
    #[verus_spec(result => ensures match result {
        Self::Concat(children) => children@ == into_iter_remaining(regexes), _ => false,
    })]
    pub fn concat<I: IntoIterator<Item = RegexExpr<E>>>(regexes: I) -> Self {
        Self::Concat(Vec::from_iter(regexes))
    }

    /// Constructs Kleene star.
    #[verus_spec(result => ensures result == Self::Star(Box::new(regex)))]
    pub fn star(regex: RegexExpr<E>) -> Self {
        Self::Star(Box::new(regex))
    }

    /// Constructs set intersection in iterator order.
    #[verus_spec(result => ensures match result {
        Self::Intersect(children) => children@ == into_iter_remaining(regexes), _ => false,
    })]
    pub fn intersect<I: IntoIterator<Item = RegexExpr<E>>>(regexes: I) -> Self {
        Self::Intersect(Vec::from_iter(regexes))
    }

    /// Constructs whole-language complement.
    #[verus_spec(result => ensures result == Self::Not(Box::new(regex)))]
    pub fn complement(regex: RegexExpr<E>) -> Self {
        Self::Not(Box::new(regex))
    }
}

/// Relationship required between committed history and a matching rule tail.
#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(verus_keep_ghost, derive(Structural))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RuleMode {
    /// Deny when committed history is outside the tail language.
    Require,
    /// Deny when committed history is inside the tail language.
    Forbid,
}

/// Complete owned source rule.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rule<E: Event> {
    /// Required or forbidden relationship to the tail language.
    pub mode: RuleMode,
    /// Candidate-only pattern declaring the rule's variables.
    pub head: Head<E>,
    /// Complete-history language evaluated under candidate bindings.
    pub tail: RegexExpr<E>,
}

#[verus_verify]
impl<E: Event> Rule<E> {
    /// Creates a declarative rule with no compiler or validator backreferences.
    #[verus_spec(result => ensures result.mode == mode, result.head == head, result.tail == tail)]
    pub fn new(mode: RuleMode, head: Head<E>, tail: RegexExpr<E>) -> Self {
        Self { mode, head, tail }
    }

    /// Releases an owned rule without recursively dropping its expression tree.
    pub fn dispose(self) {
        let Self {
            mode: _,
            head: _,
            tail,
        } = self;
        let mut regexes = Vec::new();
        let mut tests = Vec::new();
        regexes.push(tail);
        #[cfg_attr(verus_keep_ghost, verus_spec(decreases regex_forest_nodes(regexes@)))]
        while !regexes.is_empty() {
            proof_decl! { let ghost pending_before = regexes@; }
            proof! { reveal_with_fuel(regex_forest_nodes, 2); reveal(regex_nodes); }
            if let Some(regex) = regexes.pop() {
                proof! {
                    assert(pending_before =~= regexes@.push(regex));
                    assert(regex_forest_nodes(pending_before)
                        == regex_forest_nodes(regexes@) + regex_nodes(regex));
                }
                match regex {
                    RegexExpr::Union(mut children)
                    | RegexExpr::Concat(mut children)
                    | RegexExpr::Intersect(mut children) => {
                        proof! { lemma_regex_forest_append(regexes@, children@); }
                        regexes.append(&mut children);
                        proof! { assert(regex_forest_nodes(regexes@) < regex_forest_nodes(pending_before)); }
                    }
                    RegexExpr::Star(child) | RegexExpr::Not(child) => {
                        proof_decl! { let ghost prefix = regexes@; let ghost next = *child; }
                        proof! { lemma_regex_forest_append(regexes@, seq![*child]); }
                        regexes.push(*child);
                        proof! {
                            assert(regexes@ =~= prefix + seq![next]);
                            assert(regex_forest_nodes(regexes@) == regex_forest_nodes(prefix) + regex_nodes(next));
                            assert(regex_forest_nodes(regexes@) < regex_forest_nodes(pending_before));
                        }
                    }
                    RegexExpr::Test(test) => {
                        tests.push(test);
                        proof! { assert(regex_forest_nodes(regexes@) < regex_forest_nodes(pending_before)); }
                    }
                    RegexExpr::Empty | RegexExpr::All | RegexExpr::Epsilon => {
                        proof! { assert(regex_forest_nodes(regexes@) < regex_forest_nodes(pending_before)); }
                    }
                }
            }
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(decreases test_forest_nodes(tests@)))]
        while !tests.is_empty() {
            proof_decl! { let ghost pending_before = tests@; }
            proof! { reveal_with_fuel(test_forest_nodes, 2); reveal(test_nodes); }
            if let Some(test) = tests.pop() {
                proof! {
                    assert(pending_before =~= tests@.push(test));
                    assert(test_forest_nodes(pending_before)
                        == test_forest_nodes(tests@) + test_nodes(test));
                }
                match test {
                    TestExpr::And(mut children) | TestExpr::Or(mut children) => {
                        proof! { lemma_test_forest_append(tests@, children@); }
                        tests.append(&mut children);
                    }
                    TestExpr::True | TestExpr::False | TestExpr::Atom { .. } => {}
                }
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl vstd::std_specs::ops::NotSpecImpl for Comparison {
    open spec fn obeys_not_spec() -> bool { true }
    open spec fn not_req(self) -> bool { true }
    open spec fn not_spec(self) -> Self {
        match self { Self::Eq => Self::Neq, Self::Neq => Self::Eq }
    }
}
}
