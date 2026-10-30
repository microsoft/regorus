//! Structural views and independent, concrete-component semantics for the owned DSL.
//!
//! Component equality is `PartialEqSpec::eq_spec`, not representation equality. Connecting
//! native projections/equality to this model remains conditional on their respective contracts.

use alloc::boxed::Box;
use history_syntax::Event;
use history_syntax::event::specs::EventSpec;
use history_syntax::verify::dsl::{AtomView, HeadView, PatternView, RegexView, TestView};
use history_syntax::{Comparison, Component, Rule};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};


/// Values are deliberately not IDs or views of values.
pub struct EventView<P, A, R> {
    pub principal: P,
    pub action: A,
    pub resource: R,
}


pub open spec fn event_view<E: Event>(event: E) -> EventView<E::Principal, E::Action, E::Resource> {
    EventView { principal: event.principal_spec(), action: event.action_spec(), resource: event.resource_spec() }
}

pub open spec fn pattern_name<T>(pattern: PatternView<T>) -> Option<Seq<char>> {
    match pattern { PatternView::Constant(_) => None, PatternView::Variable(name) => Some(name) }
}

pub open spec fn distinct_names<T, U>(left: PatternView<T>, right: PatternView<U>) -> bool {
    match (pattern_name(left), pattern_name(right)) {
        (Some(a), Some(b)) => a != b,
        _ => true,
    }
}

pub open spec fn head_scoped<P, A, R>(head: HeadView<P, A, R>) -> bool {
    distinct_names(head.principal, head.action)
        && distinct_names(head.principal, head.resource)
        && distinct_names(head.action, head.resource)
}

pub open spec fn head_pattern_matches<T: PartialEq>(pattern: PatternView<T>, actual: T) -> bool {
    match pattern {
        PatternView::Constant(expected) => actual.eq_spec(&expected),
        PatternView::Variable(_) => true,
    }
}

pub open spec fn head_matches<P: PartialEq, A: PartialEq, R: PartialEq>(
    head: HeadView<P, A, R>, candidate: EventView<P, A, R>,
) -> bool {
    head_pattern_matches(head.principal, candidate.principal)
        && head_pattern_matches(head.action, candidate.action)
        && head_pattern_matches(head.resource, candidate.resource)
}

/// Substitution is coordinate-local: an identically spelled name in another coordinate is absent.
pub open spec fn resolve_pattern<T>(
    pattern: PatternView<T>, head: PatternView<T>, candidate: T,
) -> Option<T> {
    match pattern {
        PatternView::Constant(value) => Some(value),
        PatternView::Variable(name) => match head {
            PatternView::Variable(bound) => if name == bound { Some(candidate) } else { None },
            PatternView::Constant(_) => None,
        },
    }
}

pub open spec fn pattern_scoped<T>(pattern: PatternView<T>, head: PatternView<T>) -> bool {
    match pattern {
        PatternView::Constant(_) => true,
        PatternView::Variable(name) => pattern_name(head) == Some(name),
    }
}

pub open spec fn atom_scoped<P, A, R>(atom: AtomView<P, A, R>, head: HeadView<P, A, R>) -> bool {
    match atom {
        AtomView::Principal(pattern) => pattern_scoped(pattern, head.principal),
        AtomView::Action(pattern) => pattern_scoped(pattern, head.action),
        AtomView::Resource(pattern) => pattern_scoped(pattern, head.resource),
    }
}

pub open spec fn test_scoped<P, A, R>(test: TestView<P, A, R>, head: HeadView<P, A, R>) -> bool
    decreases test,
{
    match test {
        TestView::True | TestView::False => true,
        TestView::Atom { pattern, .. } => atom_scoped(pattern, head),
        TestView::And(children) | TestView::Or(children) =>
            forall|i: int| 0 <= i < children.len() ==> test_scoped(children[i], head),
    }
}

pub open spec fn regex_scoped<P, A, R>(regex: RegexView<P, A, R>, head: HeadView<P, A, R>) -> bool
    decreases regex,
{
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => true,
        RegexView::Test(test) => test_scoped(test, head),
        RegexView::Union(children) | RegexView::Concat(children) | RegexView::Intersect(children) =>
            forall|i: int| 0 <= i < children.len() ==> regex_scoped(children[i], head),
        RegexView::Star(child) | RegexView::Not(child) => regex_scoped(*child, head),
    }
}

pub open spec fn comparison_sem<T: PartialEq>(comparison: Comparison, actual: T, expected: Option<T>) -> bool {
    match expected {
        None => false,
        Some(value) => match comparison {
            Comparison::Eq => actual.eq_spec(&value),
            Comparison::Neq => !actual.eq_spec(&value),
        },
    }
}

pub open spec fn atom_sem<P: PartialEq, A: PartialEq, R: PartialEq>(
    comparison: Comparison, atom: AtomView<P, A, R>, head: HeadView<P, A, R>,
    candidate: EventView<P, A, R>, event: EventView<P, A, R>,
) -> bool {
    match atom {
        AtomView::Principal(pattern) => comparison_sem(comparison, event.principal,
            resolve_pattern(pattern, head.principal, candidate.principal)),
        AtomView::Action(pattern) => comparison_sem(comparison, event.action,
            resolve_pattern(pattern, head.action, candidate.action)),
        AtomView::Resource(pattern) => comparison_sem(comparison, event.resource,
            resolve_pattern(pattern, head.resource, candidate.resource)),
    }
}

pub open spec fn test_sem<P: PartialEq, A: PartialEq, R: PartialEq>(
    test: TestView<P, A, R>, head: HeadView<P, A, R>,
    candidate: EventView<P, A, R>, event: EventView<P, A, R>,
) -> bool
    decreases test,
{
    match test {
        TestView::True => true,
        TestView::False => false,
        TestView::Atom { comparison, pattern } => atom_sem(comparison, pattern, head, candidate, event),
        TestView::And(children) => forall|i: int| 0 <= i < children.len() ==>
            test_sem(children[i], head, candidate, event),
        TestView::Or(children) => exists|i: int| 0 <= i < children.len()
            && test_sem(children[i], head, candidate, event),
    }
}

/// Whole-word language semantics, in oldest-to-newest event order.
pub open spec fn lang<P: PartialEq, A: PartialEq, R: PartialEq>(
    regex: RegexView<P, A, R>, head: HeadView<P, A, R>, candidate: EventView<P, A, R>,
    word: Seq<EventView<P, A, R>>,
) -> bool
    decreases regex,
{
    match regex {
        RegexView::Empty => false,
        RegexView::All => true,
        RegexView::Epsilon => word.len() == 0,
        RegexView::Test(test) => word.len() == 1 && test_sem(test, head, candidate, word[0]),
        RegexView::Union(children) => exists|i: int| 0 <= i < children.len()
            && lang(children[i], head, candidate, word),
        RegexView::Intersect(children) => forall|i: int| 0 <= i < children.len() ==>
            lang(children[i], head, candidate, word),
        RegexView::Not(child) => !lang(*child, head, candidate, word),
        RegexView::Concat(children) => exists|parts: Seq<Seq<EventView<P, A, R>>>|
            parts.len() == children.len() && word == parts.flatten()
            && forall|i: int| 0 <= i < children.len() ==> lang(children[i], head, candidate, parts[i]),
        RegexView::Star(child) => exists|parts: Seq<Seq<EventView<P, A, R>>>|
            word == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> lang(*child, head, candidate, parts[i]),
    }
}

pub open spec fn rule_accepts<E: Event>(rule: Rule<E>, candidate: E, history: Seq<E>) -> bool {
    head_matches(rule.head@, event_view(candidate))
        && lang(rule.tail@, rule.head@, event_view(candidate), history.map(|i: int, e: E| event_view(e)))
}

/// Empty operators retain their different Boolean and language identities.
pub proof fn lemma_empty_operators<P: PartialEq, A: PartialEq, R: PartialEq>(
    head: HeadView<P, A, R>, candidate: EventView<P, A, R>, word: Seq<EventView<P, A, R>>,
)
    ensures
        test_sem(TestView::And(Seq::empty()), head, candidate, candidate),
        !test_sem(TestView::Or(Seq::empty()), head, candidate, candidate),
        !lang(RegexView::Union(Seq::empty()), head, candidate, word),
        lang(RegexView::Intersect(Seq::empty()), head, candidate, word),
        lang(RegexView::Concat(Seq::empty()), head, candidate, word) <==> word.len() == 0,
{
    if lang(RegexView::Concat(Seq::empty()), head, candidate, word) {
        let parts = choose|parts: Seq<Seq<EventView<P, A, R>>>|
            parts.len() == 0 && word == parts.flatten()
            && forall|i: int| 0 <= i < 0 ==> lang(RegexView::Empty, head, candidate, parts[i]);
        assert(parts =~= Seq::empty());
    }
    if word.len() == 0 {
        let parts: Seq<Seq<EventView<P, A, R>>> = Seq::empty();
        assert(word =~= parts.flatten());
        assert(lang(RegexView::Concat(Seq::empty()), head, candidate, word));
    }
}

pub proof fn lemma_complement_is_whole_word<P: PartialEq, A: PartialEq, R: PartialEq>(
    regex: RegexView<P, A, R>, head: HeadView<P, A, R>, candidate: EventView<P, A, R>,
    word: Seq<EventView<P, A, R>>,
)
    ensures lang(RegexView::Not(Box::new(regex)), head, candidate, word)
        <==> !lang(regex, head, candidate, word),
{}


/// The real scope bodies preserve declarations and reject a cross-coordinate use.
pub fn scope_client<'a>(name: &'a str) -> (result: Result<Component, crate::error::CompileError>)
    ensures result == Ok(Component::Principal),
{
    let mut scope = crate::scope::VariableScope::new();
    let bound = scope.bind(Component::Principal, name);
    proof! { assert(bound is Ok); }
    let conflict = scope.bind(Component::Resource, name);
    proof! { assert(conflict is Err); }
    scope.resolve(Component::Principal, name)
}

}
