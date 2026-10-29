//! The verdict a policy's entry point returns.

use alloc::{string::String, vec::Vec};

/// The verdict a policy returns for one candidate event: grant, or a single collapsed soft-error
/// carrying the precondition it failed and the fixes that would unblock it.
#[derive(Debug, PartialEq, Eq)]
pub enum PolicyDecision {
    /// Request is legal under the policy.
    Grant,
    /// Request is denied with the precondition it violated and the fixes that would unblock it.
    Deny {
        /// Human-readable precondition the request failed.
        failed_precondition: String,
        /// Ordered list of state-changing fixes that would make the request legal.
        allowed_fixes: Vec<String>,
    },
}
