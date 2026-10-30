// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

use crate::limits::LimitError;
use alloc::borrow::ToOwned;
use alloc::string::String;
use vstd::prelude::*;

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum HistoryError {
    #[error("invalid history policy at {path}: {message}")]
    InvalidPolicy { path: String, message: &'static str },
    #[error("history variable {name:?} is not bound by request pattern")]
    UnboundVariable { name: String },
    #[error("history symbolic graph payload exceeds {limit} bytes")]
    GraphLimit { limit: usize },
    #[error("history allocation failed")]
    AllocationFailed,
    #[error("history arena exhausted")]
    ArenaExhausted,
    #[error("history invariant violated: {message}")]
    Invariant { message: &'static str },
    #[error("history {domain} identity exhausted")]
    IdExhausted { domain: &'static str },
    #[error("unknown history {domain} identity {id}")]
    UnknownId { domain: &'static str, id: u64 },
    #[error("history belongs to another store")]
    WrongHistoryOwner,
    #[error("checkpoint does not belong to this history")]
    WrongCheckpointOwner,
    #[error("checkpoint is beyond the current history")]
    CheckpointBeyondHistory,
    #[error("history revision exhausted")]
    RevisionExhausted,
    #[error("history changed from revision {expected} to {actual}")]
    HistoryChanged { expected: u64, actual: u64 },
    #[error(transparent)]
    Limit(LimitError),
}

#[verus_verify]
impl From<LimitError> for HistoryError {
    #[verus_spec(result => ensures result == Self::Limit(error))]
    fn from(error: LimitError) -> Self {
        Self::Limit(error)
    }
}

#[verus_verify]
impl HistoryError {
    #[verus_verify]
    #[verus_spec(result => ensures match result {
        Self::InvalidPolicy { path: owned, message: actual } => owned@ == path@ && actual == message,
        _ => false,
    })]
    pub fn invalid_policy(path: &str, message: &'static str) -> Self {
        Self::InvalidPolicy {
            path: path.to_owned(),
            message,
        }
    }
    #[verus_verify]
    #[verus_spec(result => ensures result == (HistoryError::Invariant { message }))]
    pub const fn invariant(message: &'static str) -> HistoryError {
        HistoryError::Invariant { message }
    }

    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[inline]
    pub const fn normalization_invariant() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid normalization work stack",
        }
    }
    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[inline]
    pub const fn symbolic_invariant() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid symbolic work stack",
        }
    }
    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[inline]
    pub const fn invalid_truth_assignment() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid truth assignment",
        }
    }
    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[verus_spec(result => ensures result is Invariant)]
    #[inline]
    pub const fn graph_id_overflow() -> HistoryError {
        HistoryError::Invariant {
            message: "graph ID does not fit usize",
        }
    }
    #[verus_verify]
    #[verus_spec(result => ensures result is GraphLimit)]
    #[inline]
    pub const fn graph_index_overflow() -> HistoryError {
        HistoryError::GraphLimit {
            limit: crate::limits::MAX_GRAPH_BYTES,
        }
    }
    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[inline]
    pub const fn invalid_atom_set() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid primitive atom set",
        }
    }
    #[cfg(feature = "runtime")]
    #[verus_verify]
    #[inline]
    pub const fn missing_transition_atom() -> HistoryError {
        HistoryError::Invariant {
            message: "transition primitive missing from atom set",
        }
    }
}

/// Rule-compilation failure detected before a validator can execute.
#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CompileError {
    /// One variable name occurs in different product components in the same rule.
    #[error("variable {name:?} occurs in different product components")]
    VariableComponentConflict { name: String },
    /// A tail references a variable that its head does not bind.
    #[error("tail variable {name:?} is not bound by the head")]
    UnboundVariable { name: String },
    #[error(transparent)]
    Runtime(HistoryError),
}

#[verus_verify]
impl From<HistoryError> for CompileError {
    #[verus_spec(result => ensures result == Self::Runtime(error))]
    fn from(error: HistoryError) -> Self {
        Self::Runtime(error)
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl vstd::std_specs::convert::FromSpecImpl<LimitError> for HistoryError {
    open spec fn obeys_from_spec() -> bool { true }
    open spec fn from_spec(error: LimitError) -> Self { Self::Limit(error) }
}

impl vstd::std_specs::convert::FromSpecImpl<HistoryError> for CompileError {
    open spec fn obeys_from_spec() -> bool { true }
    open spec fn from_spec(error: HistoryError) -> Self { Self::Runtime(error) }
}

}
