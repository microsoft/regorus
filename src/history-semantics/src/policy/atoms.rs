//! One-event [`TestExpr`] building blocks over policy-selected coordinates.
//!
//! The named principal/action/resource helpers use the three-coordinate convention of
//! `LockPolicy` and `AgentPolicy`. Other event layouts use the indexed helpers.

use alloc::string::String;
#[cfg(verus_keep_ghost)]
use history_syntax::spec::events::{AtomView, PatternView, TestView};
use history_syntax::{AtomPattern, Comparison, Component, ComponentPattern, Event, TestExpr};
use vstd::prelude::*;

/// Name of a head variable.
pub type HeadVariable = &'static str;

verus! {
/// Head variable bound to the acting principal (`"p"`), coordinate 0 in the three-coordinate
/// convention.
pub const PRINCIPAL_VAR: HeadVariable = "p";
/// Head variable bound to the candidate's resource (`"r"`), coordinate 2 in the three-coordinate
/// convention.
pub const RESOURCE_VAR: HeadVariable = "r";
}

/// Compares a coordinate with its head-bound variable.
#[verus_verify]
#[verus_spec(result => ensures result@ == (TestView::Atom {
    comparison, pattern: AtomView {
        component: component.0 as nat, pattern: PatternView::Variable(variable@),
    },
}))]
pub fn component_is<E: Event>(
    component: Component,
    variable: &'static str,
    comparison: Comparison,
) -> TestExpr<E> {
    TestExpr::atom(
        comparison,
        AtomPattern::new(
            component,
            ComponentPattern::Variable(String::from_str(variable)),
        ),
    )
}

/// Compares a coordinate with a tagged constant from that coordinate.
#[verus_verify]
#[verus_spec(result => ensures result@ == (TestView::Atom {
    comparison, pattern: AtomView {
        component: component.0 as nat, pattern: PatternView::Constant(constant),
    },
}))]
pub fn component_equals<E: Event>(
    component: Component,
    constant: E::Component,
    comparison: Comparison,
) -> TestExpr<E> {
    TestExpr::atom(
        comparison,
        AtomPattern::new(component, ComponentPattern::Constant(constant)),
    )
}

/// Compares coordinate 0 with `p` in the three-ary `(principal, action, resource)` convention.
#[verus_verify]
#[verus_spec(result => requires history_syntax::spec::events::arity::<E>() == 3,
    ensures result@ == (TestView::Atom {
    comparison, pattern: AtomView { component: 0, pattern: PatternView::Variable(seq!['p']) },
}))]
pub fn principal_is<E: Event>(comparison: Comparison) -> TestExpr<E> {
    proof! { reveal_strlit("p"); assert(PRINCIPAL_VAR@ == seq!['p']); }
    component_is(Component(0), PRINCIPAL_VAR, comparison)
}

/// Compares coordinate 2 with `r` in the three-ary `(principal, action, resource)` convention.
#[verus_verify]
#[verus_spec(result => requires history_syntax::spec::events::arity::<E>() == 3,
    ensures result@ == (TestView::Atom {
    comparison, pattern: AtomView { component: 2, pattern: PatternView::Variable(seq!['r']) },
}))]
pub fn resource_is<E: Event>(comparison: Comparison) -> TestExpr<E> {
    proof! { reveal_strlit("r"); assert(RESOURCE_VAR@ == seq!['r']); }
    component_is(Component(2), RESOURCE_VAR, comparison)
}

/// Compares coordinate 1 with a tagged action in the three-ary `(principal, action, resource)` convention.
#[verus_verify]
#[verus_spec(result => ensures result@ == (TestView::Atom {
    comparison, pattern: AtomView { component: 1, pattern: PatternView::Constant(action) },
}))]
pub fn action_is<E: Event>(action: E::Component, comparison: Comparison) -> TestExpr<E> {
    component_equals(Component(1), action, comparison)
}
