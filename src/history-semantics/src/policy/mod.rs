//! Ordered declarative trace policies over externally owned histories.
//!
//! Rule evaluation uses the shared compiled-rule backend. Native diagnostic callbacks and their
//! packaging are a consumer boundary, not a claim about arbitrary callback implementations.

mod atoms;
mod decision;
mod evaluate;
mod language;
mod rule;
mod trace;

pub use atoms::{action_is, principal_is, resource_is};
pub use decision::PolicyDecision;
pub use evaluate::CompiledPolicy;
pub use language::last_state_change;
pub use rule::{Diagnostic, PolicyRule, forbid};
pub use trace::{TraceDiagnostic, TracePolicy, TraceRule};

#[cfg(test)]
mod tests;
