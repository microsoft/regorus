//! The rule/diagnostic pairing a policy table is built from, generalized over the per-policy
//! context a denial renders from.

use alloc::{boxed::Box, string::String, vec::Vec};

use super::atoms::{PRINCIPAL_VAR, RESOURCE_VAR};
use history_syntax::{ComponentPattern, Event, Head, RegexExpr, Rule, RuleMode};

/// Renders a violated rule's `(failed_precondition, allowed_fixes)` from the policy's context.
pub type Diagnostic<C> = Box<dyn Fn(&C) -> (String, Vec<String>)>;

/// One trace-policy rule paired with the diagnostic its violation surfaces.
pub struct PolicyRule<E: Event, C> {
    pub rule: Rule<E>,
    pub diagnostic: Diagnostic<C>,
}

/// Builds a `Forbid` rule with an action-constant head over the acting principal and resource.
pub fn forbid<E: Event, C>(
    action: E::Action,
    tail: RegexExpr<E>,
    diagnostic: Diagnostic<C>,
) -> PolicyRule<E, C> {
    PolicyRule {
        rule: Rule::new(
            RuleMode::Forbid,
            Head::new(
                ComponentPattern::variable(PRINCIPAL_VAR),
                ComponentPattern::constant(action),
                ComponentPattern::variable(RESOURCE_VAR),
            ),
            tail,
        ),
        diagnostic,
    }
}
