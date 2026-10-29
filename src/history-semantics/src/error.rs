use junco_core::error::{CompileError, HistoryError};
use vstd::prelude::*;

/// Compilation or execution failure from a one-shot policy decision.
#[cfg(feature = "runtime")]
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum PolicyError {
    /// The policy source could not be compiled.
    #[error(transparent)]
    Compile(CompileError),
    /// The compiled policy could not complete its decision.
    #[error(transparent)]
    Runtime(HistoryError),
}

#[cfg(feature = "runtime")]
#[verus_verify]
impl From<CompileError> for PolicyError {
    #[verus_spec(result => ensures result == Self::Compile(error))]
    fn from(error: CompileError) -> Self {
        Self::Compile(error)
    }
}

#[cfg(feature = "runtime")]
#[verus_verify]
impl From<HistoryError> for PolicyError {
    #[verus_spec(result => ensures result == Self::Runtime(error))]
    fn from(error: HistoryError) -> Self {
        Self::Runtime(error)
    }
}

#[cfg(verus_keep_ghost)]
verus! {
#[cfg(feature = "runtime")]
impl vstd::std_specs::convert::FromSpecImpl<CompileError> for PolicyError {
    open spec fn obeys_from_spec() -> bool { true }
    open spec fn from_spec(error: CompileError) -> Self { Self::Compile(error) }
}

#[cfg(feature = "runtime")]
impl vstd::std_specs::convert::FromSpecImpl<HistoryError> for PolicyError {
    open spec fn obeys_from_spec() -> bool { true }
    open spec fn from_spec(error: HistoryError) -> Self { Self::Runtime(error) }
}
}
