//! Request and grant records at the authorization boundary.

use history_syntax::Event;
use vstd::prelude::*;

/// Capability request with opaque caller metadata.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request<E: Event, M> {
    /// Product event evaluated by the policy.
    pub event: E,
    /// Opaque value passed through unchanged on grant.
    pub metadata: M,
}

#[verus_verify]
impl<E: Event, M> Request<E, M> {
    /// Creates a request from an event and opaque metadata.
    #[verus_spec(result => ensures result.event == event, result.metadata == metadata)]
    pub fn new(event: E, metadata: M) -> Self {
        Self { event, metadata }
    }
}

/// Accepted request echoed at the authorization boundary.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Grant<E: Event, M> {
    /// Accepted event, also appended to committed history.
    pub event: E,
    /// Original request metadata, preserved unchanged.
    pub metadata: M,
}
