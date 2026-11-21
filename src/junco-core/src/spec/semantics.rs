//! The typed semantics of rules (paper `sec:rules`, Definitions `def:violates` and
//! `def:policy-violates`), first over component tuples, then over events through `event_view`.
//!
//! Component equality is `PartialEqSpec::eq_spec`, not representation equality. Connecting
//! native projections/equality to this model remains conditional on their respective contracts.

use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::{
    AtomView, HeadView, PatternView, RegexView, RuleView, TestView, event_view,
};
use history_syntax::{Comparison, Event, Rule, RuleMode};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// Operational resource failures, never malformed input, ownership errors or invariant failures.
pub open spec fn resource_error(error: crate::errors::HistoryError) -> bool {
    matches!(error, crate::errors::HistoryError::GraphBudget { .. }
        | crate::errors::HistoryError::GraphIndex
        | crate::errors::HistoryError::AllocationFailed
        | crate::errors::HistoryError::ArenaExhausted
        | crate::errors::HistoryError::IdExhausted { .. }
        | crate::errors::HistoryError::RevisionExhausted
        | crate::errors::HistoryError::Limit(_))
}

/// Every source constant has the tag of the coordinate where it is compared.
pub open spec fn rule_constants_tagged<E: Event>(rule: RuleView<E::Component>) -> bool {
    forall|i: int, value: E::Component| 0 <= i < rule.head.len()
        && #[trigger] crate::spec::questions::rule_constants(rule)[i].contains(value)
        ==> E::coordinate_spec(value) == i
}

// ----- heads, scoping, and tails over component tuples -----

/// The variable name of a head or atom pattern, if it is a variable.
pub open spec fn pattern_name<T>(pattern: PatternView<T>) -> Option<Seq<char>> {
    match pattern { PatternView::Constant(_) => None, PatternView::Variable(name) => Some(name) }
}

/// Two patterns do not share a variable name.
pub open spec fn distinct_names<T, U>(left: PatternView<T>, right: PatternView<U>) -> bool {
    match (pattern_name(left), pattern_name(right)) {
        (Some(a), Some(b)) => a != b,
        _ => true,
    }
}

/// Head variables have pairwise distinct names (`sec:rules`).
pub open spec fn head_scoped<C>(head: HeadView<C>) -> bool {
    forall|i: int, j: int| 0 <= i < j < head.len() ==>
        distinct_names(#[trigger] head[i], #[trigger] head[j])
}

/// A head pattern matches a component: a constant up to `eq_spec`, a variable always.
pub open spec fn head_pattern_matches<T: PartialEq>(pattern: PatternView<T>, actual: T) -> bool {
    match pattern {
        PatternView::Constant(expected) => actual.eq_spec(&expected),
        PatternView::Variable(_) => true,
    }
}

/// The head unifies with the candidate tuple (`sec:rules`).
pub open spec fn head_matches<C: PartialEq>(head: HeadView<C>, candidate: Seq<C>) -> bool {
    head.len() == candidate.len()
        && forall|i: int| 0 <= i < head.len() ==>
            head_pattern_matches(#[trigger] head[i], candidate[i])
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

/// A tail pattern is a constant or the head variable of its own coordinate.
pub open spec fn pattern_scoped<T>(pattern: PatternView<T>, head: PatternView<T>) -> bool {
    match pattern {
        PatternView::Constant(_) => true,
        PatternView::Variable(name) => pattern_name(head) == Some(name),
    }
}

pub open spec fn atom_scoped<C>(atom: AtomView<C>, head: HeadView<C>) -> bool {
    atom.component < head.len() && pattern_scoped(atom.pattern, head[atom.component as int])
}

pub open spec fn test_scoped<C>(test: TestView<C>, head: HeadView<C>) -> bool
    decreases test,
{
    match test {
        TestView::True | TestView::False => true,
        TestView::Atom { pattern, .. } => atom_scoped(pattern, head),
        // Separate bindings keep conditional expressions out of the quantified index triggers.
        TestView::And(children) =>
            forall|i: int| 0 <= i < children.len() ==> test_scoped(#[trigger] children[i], head),
        TestView::Or(children) =>
            forall|i: int| 0 <= i < children.len() ==> test_scoped(#[trigger] children[i], head),
    }
}

/// Every variable of the tail is the head variable of its own coordinate (component-locality,
/// `sec:events`).
pub open spec fn regex_scoped<C>(regex: RegexView<C>, head: HeadView<C>) -> bool
    decreases regex,
{
    match regex {
        RegexView::Empty | RegexView::All | RegexView::Epsilon => true,
        RegexView::Test(test) => test_scoped(test, head),
        RegexView::Union(children) =>
            forall|i: int| 0 <= i < children.len() ==> regex_scoped(#[trigger] children[i], head),
        RegexView::Concat(children) =>
            forall|i: int| 0 <= i < children.len() ==> regex_scoped(#[trigger] children[i], head),
        RegexView::Intersect(children) =>
            forall|i: int| 0 <= i < children.len() ==> regex_scoped(#[trigger] children[i], head),
        RegexView::Star(child) | RegexView::Not(child) => regex_scoped(*child, head),
    }
}

/// An atom comparison against a resolved operand; an unresolved operand is false.
pub open spec fn comparison_sem<T: PartialEq>(comparison: Comparison, actual: T, expected: Option<T>) -> bool {
    match expected {
        None => false,
        Some(value) => match comparison {
            Comparison::Eq => actual.eq_spec(&value),
            Comparison::Neq => !actual.eq_spec(&value),
        },
    }
}

/// Component tests read one event coordinate and the candidate's binding of that coordinate.
pub open spec fn atom_sem<C: PartialEq>(
    comparison: Comparison, atom: AtomView<C>, head: HeadView<C>,
    candidate: Seq<C>, event: Seq<C>,
) -> bool {
    atom.component < head.len() && atom.component < candidate.len() && atom.component < event.len()
        && comparison_sem(comparison, event[atom.component as int],
            resolve_pattern(atom.pattern, head[atom.component as int], candidate[atom.component as int]))
}

/// Boolean combinations of component tests over one history event.
pub open spec fn test_sem<C: PartialEq>(
    test: TestView<C>, head: HeadView<C>,
    candidate: Seq<C>, event: Seq<C>,
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

/// Whole-word language semantics of a tail, in oldest-to-newest event order (`sec:rules`).
pub open spec fn lang<C: PartialEq>(
    regex: RegexView<C>, head: HeadView<C>, candidate: Seq<C>,
    word: Seq<Seq<C>>,
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
        RegexView::Concat(children) => exists|parts: Seq<Seq<Seq<C>>>|
            parts.len() == children.len() && word == parts.flatten()
            && forall|i: int| 0 <= i < children.len() ==> lang(children[i], head, candidate, parts[i]),
        RegexView::Star(child) => exists|parts: Seq<Seq<Seq<C>>>|
            word == parts.flatten()
            && forall|i: int| 0 <= i < parts.len() ==> lang(*child, head, candidate, parts[i]),
    }
}

// ----- rules -----

/// `mode = require` and the history is outside the tail, or `mode = forbid` and it is inside.
pub open spec fn violated_by(mode: RuleMode, inside: bool) -> bool {
    match mode { RuleMode::Require => !inside, RuleMode::Forbid => inside }
}

/// Head variables have distinct names and every tail variable is the head variable of its own
/// component (`sec:rules`, "a tail whose variables occur in h"; component-locality, `sec:events`).
pub open spec fn rule_wf<C>(rule: RuleView<C>) -> bool {
    1 <= rule.head.len() <= history_syntax::MAX_ARITY && head_scoped(rule.head) && regex_scoped(rule.tail, rule.head)
}

/// A head with two tails, both reading only the head's variables (the `tail_included` inputs).
pub open spec fn head_tails_wf<C>(head: HeadView<C>, left: RegexView<C>, right: RegexView<C>) -> bool {
    1 <= head.len() <= history_syntax::MAX_ARITY && head_scoped(head) && regex_scoped(left, head) && regex_scoped(right, head)
}

/// The matcher's answer on component tuples: `None` if the head does not match, else tail
/// membership of the history.
pub open spec fn rule_evaluation_view<C: PartialEq>(
    rule: RuleView<C>, candidate: Seq<C>, history: Seq<Seq<C>>,
) -> Option<bool> {
    if !head_matches(rule.head, candidate) { None }
    else { Some(lang(rule.tail, rule.head, candidate, history)) }
}

/// Rule violation on tuples: fired, and the mode disagrees with tail membership (`def:violates`).
pub open spec fn rule_violated_view<C: PartialEq>(
    rule: RuleView<C>, candidate: Seq<C>, history: Seq<Seq<C>>,
) -> bool {
    match rule_evaluation_view(rule, candidate, history) {
        None => false,
        Some(inside) => violated_by(rule.mode, inside),
    }
}

// ----- events -----

/// A history of events as the tuples the semantics reads (`event_view`, oldest first).
pub open spec fn history_view<E: Event>(history: Seq<E>) -> Seq<Seq<E::Component>> {
    history.map(|i: int, e: E| event_view(e))
}

/// The views of a sequence of source rules, in order.
pub open spec fn rule_views<E: Event>(rules: Seq<Rule<E>>) -> Seq<RuleView<E::Component>> {
    rules.map(|i: int, r: Rule<E>| r@)
}

/// Evaluates the tail over the committed history, excluding the candidate; a head mismatch is
/// `None`.
pub open spec fn rule_evaluation<E: Event>(
    rule: RuleView<E::Component>, candidate: E, history: Seq<E>,
) -> Option<bool> {
    rule_evaluation_view(rule, event_view(candidate), history_view(history))
}

/// Definition Rule violation (`def:violates`), over events.
pub open spec fn rule_violated<E: Event>(
    rule: RuleView<E::Component>, candidate: E, history: Seq<E>,
) -> bool {
    rule_violated_view(rule, event_view(candidate), history_view(history))
}

/// Definition Policy violation (`def:policy-violates`): some rule is violated.
pub open spec fn policy_denies<E: Event>(
    rules: Seq<RuleView<E::Component>>, candidate: E, history: Seq<E>,
) -> bool {
    exists|i: int| 0 <= i < rules.len() && #[trigger] rule_violated(rules[i], candidate, history)
}

/// The policy permits the candidate after the history: no rule is violated.
pub open spec fn policy_permits<E: Event>(
    rules: Seq<RuleView<E::Component>>, candidate: E, history: Seq<E>,
) -> bool {
    !policy_denies(rules, candidate, history)
}

/// `index` is the first violated rule in source order (the monitor's reported rule).
pub open spec fn least_violation<E: Event>(
    rules: Seq<RuleView<E::Component>>, candidate: E, history: Seq<E>, index: int,
) -> bool {
    0 <= index < rules.len() && rule_violated(rules[index], candidate, history)
        && forall|j: int| 0 <= j < index ==> !rule_violated(rules[j], candidate, history)
}

} // verus!
