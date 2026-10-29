//! Compact, statically dispatched capability-product events.

use core::fmt::Debug;
use core::hash::Hash;
use frunk_core::coproduct::{CNil, Coproduct};
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use self::specs::EventSpec;

/// Capability-product event matched by heads and tail atoms.
///
/// Equality and hashing describe the full event, including its variant and payload.
/// Projections, equality and hashing must remain stable while values are used by a policy.
pub trait Event: Copy + Debug + Eq + Hash {
    /// Identity of the actor requesting a capability.
    type Principal: Copy + Debug + Eq + Hash;
    /// Requested operation.
    type Action: Copy + Debug + Eq + Hash;
    /// Protected resource.
    type Resource: Copy + Debug + Eq + Hash;

    /// Returns the actor requesting the capability.
    fn principal(self) -> Self::Principal;
    /// Returns the requested operation.
    fn action(self) -> Self::Action;
    /// Returns the protected resource.
    fn resource(self) -> Self::Resource;
}

// The pinned verifier rejects zero-arm matches; this leaf eliminates only Frunk's empty CNil.
#[verus_verify]
#[verus_verify(external_body)]
#[verus_spec(result => ensures false)]
fn absurd_nil<T>(nil: CNil) -> T {
    match nil {}
}

/// Final variant of a Frunk event union.
#[verus_verify]
impl<H: Event> Event for Coproduct<H, CNil> {
    type Principal = H::Principal;
    type Action = H::Action;
    type Resource = H::Resource;

    fn principal(self) -> Self::Principal {
        match self {
            Coproduct::Inl(head) => head.principal(),
            Coproduct::Inr(nil) => absurd_nil(nil),
        }
    }

    fn action(self) -> Self::Action {
        match self {
            Coproduct::Inl(head) => head.action(),
            Coproduct::Inr(nil) => absurd_nil(nil),
        }
    }

    fn resource(self) -> Self::Resource {
        match self {
            Coproduct::Inl(head) => head.resource(),
            Coproduct::Inr(nil) => absurd_nil(nil),
        }
    }
}

/// Head variant of a Frunk event union whose tail shares its component types.
#[verus_verify]
impl<H, T, Rest> Event for Coproduct<H, Coproduct<T, Rest>>
where
    H: Event,
    Coproduct<T, Rest>: Event<Principal = H::Principal, Action = H::Action, Resource = H::Resource>,
{
    type Principal = H::Principal;
    type Action = H::Action;
    type Resource = H::Resource;

    fn principal(self) -> Self::Principal {
        match self {
            Coproduct::Inl(head) => head.principal(),
            Coproduct::Inr(tail) => tail.principal(),
        }
    }

    fn action(self) -> Self::Action {
        match self {
            Coproduct::Inl(head) => head.action(),
            Coproduct::Inr(tail) => tail.action(),
        }
    }

    fn resource(self) -> Self::Resource {
        match self {
            Coproduct::Inl(head) => head.resource(),
            Coproduct::Inr(tail) => tail.resource(),
        }
    }
}

/// Conditional native projection boundary; implementations need not opt in.
#[cfg(verus_keep_ghost)]
pub mod specs {
    use super::*;
    verus! {

    // Transparent specifications expose exactly the Frunk enum variants to body proofs.
    #[verifier::external_type_specification]
    #[verifier::accept_recursive_types(H)]
    #[verifier::reject_recursive_types_in_ground_variants(T)]
    pub struct ExCoproduct<H, T>(Coproduct<H, T>);

    #[verifier::external_type_specification]
    // Like vstd's Infallible: the pinned verifier cannot represent a zero-variant datatype.
    #[verifier::external_body]
    pub struct ExCNil(CNil);

    #[verifier::external_trait_specification]
    #[verifier::external_trait_extension(EventSpec via EventSpecImpl)]
    pub trait ExEvent: Copy + Debug + Eq + Hash {
        type ExternalTraitSpecificationFor: Event;
        type Principal: Copy + Debug + Eq + Hash;
        type Action: Copy + Debug + Eq + Hash;
        type Resource: Copy + Debug + Eq + Hash;

        spec fn obeys_projection_spec() -> bool;
        spec fn principal_spec(self) -> Self::Principal;
        spec fn action_spec(self) -> Self::Action;
        spec fn resource_spec(self) -> Self::Resource;

        fn principal(self) -> (result: Self::Principal)
            ensures Self::obeys_projection_spec() ==> result == self.principal_spec();
        fn action(self) -> (result: Self::Action)
            ensures Self::obeys_projection_spec() ==> result == self.action_spec();
        fn resource(self) -> (result: Self::Resource)
            ensures Self::obeys_projection_spec() ==> result == self.resource_spec();
    }

    impl<H: Event> EventSpecImpl for Coproduct<H, CNil> {
        open spec fn obeys_projection_spec() -> bool { H::obeys_projection_spec() }
        // CNil has no native values; its opaque logical extension is deliberately unconstrained.
        open spec fn principal_spec(self) -> Self::Principal {
            match self { Coproduct::Inl(head) => head.principal_spec(), Coproduct::Inr(_) => arbitrary() }
        }
        open spec fn action_spec(self) -> Self::Action {
            match self { Coproduct::Inl(head) => head.action_spec(), Coproduct::Inr(_) => arbitrary() }
        }
        open spec fn resource_spec(self) -> Self::Resource {
            match self { Coproduct::Inl(head) => head.resource_spec(), Coproduct::Inr(_) => arbitrary() }
        }
    }

    impl<H, T, Rest> EventSpecImpl for Coproduct<H, Coproduct<T, Rest>>
    where
        H: Event,
        Coproduct<T, Rest>: Event<Principal = H::Principal, Action = H::Action, Resource = H::Resource>,
    {
        open spec fn obeys_projection_spec() -> bool {
            H::obeys_projection_spec() && <Coproduct<T, Rest> as EventSpec>::obeys_projection_spec()
        }
        open spec fn principal_spec(self) -> Self::Principal {
            match self { Coproduct::Inl(head) => head.principal_spec(), Coproduct::Inr(tail) => tail.principal_spec() }
        }
        open spec fn action_spec(self) -> Self::Action {
            match self { Coproduct::Inl(head) => head.action_spec(), Coproduct::Inr(tail) => tail.action_spec() }
        }
        open spec fn resource_spec(self) -> Self::Resource {
            match self { Coproduct::Inl(head) => head.resource_spec(), Coproduct::Inr(tail) => tail.resource_spec() }
        }
    }
    }
}
