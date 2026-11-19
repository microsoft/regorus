//! Ordered declarative trace policies over externally owned histories.
//!
//! Checked construction preserves source/diagnostic order; checked selection uses the
//! shared compiled-rule contracts. Field unpacking and context/diagnostic invocation
//! are native leaves. Arbitrary callbacks need not be pure, deterministic, or terminating.

mod atoms;
mod decision;
pub mod evaluate;
mod language;
pub mod rule;
pub mod trace;

pub use atoms::{
    PRINCIPAL_VAR, RESOURCE_VAR, action_is, component_equals, component_is, principal_is,
    resource_is,
};
pub use decision::PolicyDecision;
pub use evaluate::CompiledPolicy;
pub use language::last_state_change;
pub use rule::{Diagnostic, PolicyRule, forbid};
pub use trace::{TraceDiagnostic, TracePolicy, TraceRule};

#[cfg(test)]
mod tests;
