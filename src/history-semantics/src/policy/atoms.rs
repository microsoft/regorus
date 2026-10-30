//! One-event [`TestExpr`] building blocks every policy's predicates are assembled from.
//!
//! Head variables are the string names [`PRINCIPAL_VAR`] and [`RESOURCE_VAR`]; a rule head binds
//! them and a tail atom refers back to them.

use history_syntax::{AtomPattern, Comparison, ComponentPattern, Event, TestExpr};

/// Head variable bound to the acting principal.
pub(super) const PRINCIPAL_VAR: &str = "p";
/// Head variable bound to the candidate's resource.
pub(super) const RESOURCE_VAR: &str = "r";

/// An event whose principal compares against the head-bound principal `p`.
pub fn principal_is<E: Event>(comparison: Comparison) -> TestExpr<E> {
    TestExpr::atom(
        comparison,
        AtomPattern::Principal(ComponentPattern::variable(PRINCIPAL_VAR)),
    )
}

/// An event whose resource compares against the head-bound resource `r`.
pub fn resource_is<E: Event>(comparison: Comparison) -> TestExpr<E> {
    TestExpr::atom(
        comparison,
        AtomPattern::Resource(ComponentPattern::variable(RESOURCE_VAR)),
    )
}

/// An event whose action compares against the constant `action`.
pub fn action_is<E: Event>(action: E::Action, comparison: Comparison) -> TestExpr<E> {
    TestExpr::atom(
        comparison,
        AtomPattern::Action(ComponentPattern::constant(action)),
    )
}
