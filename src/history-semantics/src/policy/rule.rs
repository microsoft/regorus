//! The rule/diagnostic pairing a policy table is built from, generalized over the per-policy
//! context a denial renders from.

use alloc::{boxed::Box, string::String, vec::Vec};

#[cfg(verus_keep_ghost)]
use self::verify::{diagnostic_identity, policy_rule_diagnostic, policy_rule_source};
use super::atoms::{PRINCIPAL_VAR, RESOURCE_VAR};
#[cfg(verus_keep_ghost)]
use history_syntax::spec::events::PatternView;
use history_syntax::{ComponentPattern, Event, Head, RegexExpr, Rule, RuleMode};
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::DeepView;

/// Renders a violated rule's `(failed_precondition, allowed_fixes)` from the policy's context.
#[cfg(not(verus_keep_ghost))]
pub type Diagnostic<C> = Box<dyn Fn(&C) -> (String, Vec<String>)>;
#[cfg(verus_keep_ghost)]
pub type Diagnostic<C> = NativeDiagnostic<C>;

/// One trace-policy rule paired with the diagnostic its violation surfaces.
#[verus_verify(external_body)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(E))]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(C))]
pub struct PolicyRule<E: Event, C> {
    pub rule: Rule<E>,
    pub diagnostic: Diagnostic<C>,
}

type DiagnosticRenderer<C> = dyn Fn(&C) -> (String, Vec<String>);

// Only callback storage is opaque; the raw payload avoids a recursive ghost alias.
#[doc(hidden)]
#[verus_verify(external_body)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(C))]
pub struct NativeDiagnostic<C> {
    pub(crate) inner: Box<DiagnosticRenderer<C>>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<C> NativeDiagnostic<C> {
    // Equality witness only: no freshness or uniqueness is assumed.
    pub uninterp spec fn id(&self) -> int;
}

pub mod verify {
    use super::*;

    pub uninterp spec fn policy_rule_source<E: Event, C>(item: PolicyRule<E, C>) -> Rule<E>;
    pub uninterp spec fn policy_rule_diagnostic<E: Event, C>(item: PolicyRule<E, C>) -> int;

    // Identity of the supplied native Box only; no freshness or output law.
    pub open spec fn diagnostic_identity<C>(diagnostic: Diagnostic<C>) -> int {
        diagnostic.id()
    }

    pub uninterp spec fn diagnostic_output<C>(id: int, context: C,
        failed: Seq<char>, fixes: Seq<Seq<char>>) -> bool;
}
}

/// Stores the supplied callback in the same single Box used by native diagnostics.
#[doc(hidden)]
#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => requires
    forall|argument: &C| call_requires(diagnostic, (argument,)),
    ensures forall|value: C, output: (String, Vec<String>)|
        verify::diagnostic_output(diagnostic_identity(result), value,
            output.0@, output.1.deep_view()) ==>
            exists|argument: &C| *argument == value
                && call_ensures(diagnostic, (argument,), output))]
pub fn diagnostic_from_fn<C, F: Fn(&C) -> (String, Vec<String>) + 'static>(
    diagnostic: F,
) -> Diagnostic<C> {
    #[cfg(verus_keep_ghost)]
    {
        NativeDiagnostic {
            inner: Box::new(diagnostic),
        }
    }
    #[cfg(not(verus_keep_ghost))]
    {
        Box::new(diagnostic)
    }
}

// The sole trusted constructor operation is native source/callback field storage.
#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => ensures policy_rule_source(result) == rule,
    policy_rule_diagnostic(result) == diagnostic_identity(diagnostic))]
pub(crate) fn pack_policy_rule<E: Event, C>(
    rule: Rule<E>,
    diagnostic: Diagnostic<C>,
) -> PolicyRule<E, C> {
    PolicyRule { rule, diagnostic }
}

/// Builds a `Forbid` rule using the three-ary `(principal, action, resource)` convention.
#[verus_verify]
#[verus_spec(result => requires history_syntax::spec::events::arity::<E>() == 3,
    ensures
    policy_rule_source(result).mode == RuleMode::Forbid,
    policy_rule_source(result).head@ == seq![
        PatternView::Variable(seq!['p']), PatternView::Constant(action), PatternView::Variable(seq!['r']),
    ],
    policy_rule_source(result).tail == tail,
    policy_rule_diagnostic(result) == diagnostic_identity(diagnostic),
)]
// The iterator proof below needs a Vec built by pushes, not vec!.
#[allow(clippy::vec_init_then_push)]
pub fn forbid<E: Event, C>(
    action: E::Component,
    tail: RegexExpr<E>,
    diagnostic: Diagnostic<C>,
) -> PolicyRule<E, C> {
    proof! {
        reveal_strlit("p");
        reveal_strlit("r");
        assert(PRINCIPAL_VAR@ == seq!['p']);
        assert(RESOURCE_VAR@ == seq!['r']);
    }
    let mut slots = Vec::with_capacity(3);
    slots.push(ComponentPattern::Variable(String::from_str(PRINCIPAL_VAR)));
    slots.push(ComponentPattern::Constant(action));
    slots.push(ComponentPattern::Variable(String::from_str(RESOURCE_VAR)));
    let iter = slots.into_iter();
    proof! { vstd::std_specs::iter::axiom_from_iterator_ensures(iter); }
    let head = Head::new(iter);
    let rule = Rule::new(RuleMode::Forbid, head, tail);
    pack_policy_rule(rule, diagnostic)
}
