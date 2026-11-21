//! Owned source language for declarative policy rules over one [`Event`] type.
//!
//! Constants retain the event's tagged component type. Variables are local names;
//! source expressions contain no arena references, compiler identities or store backreferences.

use crate::event::{Event, MAX_ARITY};
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::iter::FromIterator;

/// Constant-or-variable pattern for one statically selected product component.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ComponentPattern<T, Variable = String> {
    /// Match one equal component value, using the component's equality relation.
    Constant(T),
    /// Bind or resolve a named component value.
    Variable(Variable),
}

impl<T> ComponentPattern<T, String> {
    /// Creates a constant pattern from a value convertible to `T`.
    pub fn constant<I: Into<T>>(value: I) -> Self {
        Self::Constant(value.into())
    }

    /// Creates a named variable pattern.
    pub fn variable<I: Into<String>>(name: I) -> Self {
        Self::Variable(name.into())
    }
}

/// Candidate-only pattern over the event coordinates.
/// Variables declared here may be resolved only in the same tail coordinate.
/// The compiler checks that the number of slots equals the event type's arity.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Head<E: Event>(pub Vec<ComponentPattern<E::Component>>);

impl<E: Event> Head<E> {
    /// Creates a head in coordinate order.
    pub fn new<I: IntoIterator<Item = ComponentPattern<E::Component>>>(slots: I) -> Self {
        Self(Vec::from_iter(slots))
    }

    /// Patterns in coordinate order.
    pub fn slots(&self) -> &[ComponentPattern<E::Component>] {
        self.0.as_slice()
    }
}

/// Coordinate of the event tuple; order is part of the portable format.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Component(pub u8);

impl Component {
    /// Returns the coordinate's position in a portable head.
    pub const fn index(self) -> usize {
        self.0 as usize
    }

    /// Creates a coordinate index, panicking if it exceeds the supported arity.
    pub const fn new(index: usize) -> Self {
        assert!(index < MAX_ARITY);
        Self(index as u8)
    }
}

/// Comparison applied by a one-event atom.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Comparison {
    /// Accept equal component values.
    Eq,
    /// Accept unequal component values.
    Neq,
}

impl core::ops::Not for Comparison {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Self::Eq => Self::Neq,
            Self::Neq => Self::Eq,
        }
    }
}

/// Owned one-event component pattern.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AtomPattern<E: Event> {
    /// Coordinate selected by this atom.
    pub component: Component,
    /// Constant or head-bound variable to compare.
    pub pattern: ComponentPattern<E::Component>,
}

impl<E: Event> AtomPattern<E> {
    /// Creates a pattern over a selected coordinate.
    pub fn new(component: Component, pattern: ComponentPattern<E::Component>) -> Self {
        Self { component, pattern }
    }

    /// Returns the coordinate selected by this atom.
    pub fn component(&self) -> Component {
        self.component
    }
}

/// Owned boolean expression over one history event.
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

impl<E: Event> TestExpr<E> {
    /// Returns the predicate accepting every event.
    pub const fn true_test() -> Self {
        Self::True
    }

    /// Returns the predicate accepting no event.
    pub const fn false_test() -> Self {
        Self::False
    }

    /// Creates a component equality or disequality predicate.
    pub fn atom(comparison: Comparison, pattern: AtomPattern<E>) -> Self {
        Self::Atom {
            comparison,
            pattern,
        }
    }

    /// Conjoins source predicates in iterator order.
    pub fn and<I: IntoIterator<Item = TestExpr<E>>>(tests: I) -> Self {
        Self::And(Vec::from_iter(tests))
    }

    /// Disjoins source predicates in iterator order.
    pub fn or<I: IntoIterator<Item = TestExpr<E>>>(tests: I) -> Self {
        Self::Or(Vec::from_iter(tests))
    }
}

/// Owned regular expression over complete event histories.
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

impl<E: Event> RegexExpr<E> {
    /// Returns the empty language.
    pub const fn empty() -> Self {
        Self::Empty
    }

    /// Returns the universal language.
    pub const fn all() -> Self {
        Self::All
    }

    /// Returns the language containing only the empty history.
    pub const fn epsilon() -> Self {
        Self::Epsilon
    }

    /// Lifts a one-event predicate into a one-event language.
    pub fn test(test: TestExpr<E>) -> Self {
        Self::Test(test)
    }

    /// Constructs set union in iterator order.
    pub fn union<I: IntoIterator<Item = RegexExpr<E>>>(regexes: I) -> Self {
        Self::Union(Vec::from_iter(regexes))
    }

    /// Constructs ordered language concatenation.
    pub fn concat<I: IntoIterator<Item = RegexExpr<E>>>(regexes: I) -> Self {
        Self::Concat(Vec::from_iter(regexes))
    }

    /// Constructs Kleene star.
    pub fn star(regex: RegexExpr<E>) -> Self {
        Self::Star(Box::new(regex))
    }

    /// Constructs set intersection in iterator order.
    pub fn intersect<I: IntoIterator<Item = RegexExpr<E>>>(regexes: I) -> Self {
        Self::Intersect(Vec::from_iter(regexes))
    }

    /// Constructs whole-language complement.
    pub fn complement(regex: RegexExpr<E>) -> Self {
        Self::Not(Box::new(regex))
    }
}

/// Relationship required between committed history and a matching rule tail.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RuleMode {
    /// Deny when committed history is outside the tail language.
    Require,
    /// Deny when committed history is inside the tail language.
    Forbid,
}

/// Complete owned source rule.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rule<E: Event> {
    /// Required or forbidden relationship to the tail language.
    pub mode: RuleMode,
    /// Candidate-only pattern declaring the rule's variables.
    pub head: Head<E>,
    /// Complete-history language evaluated under candidate bindings.
    pub tail: RegexExpr<E>,
}

impl<E: Event> Rule<E> {
    /// Creates a declarative rule with no compiler or validator backreferences.
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
        while !regexes.is_empty() {
            if let Some(regex) = regexes.pop() {
                match regex {
                    RegexExpr::Union(mut children)
                    | RegexExpr::Concat(mut children)
                    | RegexExpr::Intersect(mut children) => {
                        regexes.append(&mut children);
                    }
                    RegexExpr::Star(child) | RegexExpr::Not(child) => {
                        regexes.push(*child);
                    }
                    RegexExpr::Test(test) => {
                        tests.push(test);
                    }
                    RegexExpr::Empty | RegexExpr::All | RegexExpr::Epsilon => {}
                }
            }
        }
        while !tests.is_empty() {
            if let Some(test) = tests.pop() {
                match test {
                    TestExpr::And(mut children) | TestExpr::Or(mut children) => {
                        tests.append(&mut children);
                    }
                    TestExpr::True | TestExpr::False | TestExpr::Atom { .. } => {}
                }
            }
        }
    }
}
