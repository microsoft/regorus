// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

use crate::utils::limits::LimitError;
use alloc::string::String;
use vstd::prelude::{verus_spec, verus_verify};

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
    #[error("history revision exhausted")]
    RevisionExhausted,
    #[error("history changed from revision {expected} to {actual}")]
    HistoryChanged { expected: u64, actual: u64 },
    #[error(transparent)]
    Limit(#[from] LimitError),
}

#[verus_verify]
impl HistoryError {
    #[verus_verify(external)]
    pub(crate) fn invalid_policy(path: &str, message: &'static str) -> Self {
        Self::InvalidPolicy {
            path: String::from(path),
            message,
        }
    }
    #[verus_verify]
    #[verus_spec(result => ensures result == (HistoryError::Invariant { message }))]
    pub(crate) const fn invariant(message: &'static str) -> HistoryError {
        HistoryError::Invariant { message }
    }

    #[verus_verify]
    #[inline]
    pub(crate) const fn normalization_invariant() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid normalization work stack",
        }
    }
    #[verus_verify]
    #[inline]
    pub(crate) const fn symbolic_invariant() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid symbolic work stack",
        }
    }
    #[verus_verify]
    #[inline]
    pub(crate) const fn invalid_truth_assignment() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid truth assignment",
        }
    }
    #[verus_verify]
    #[verus_spec(result => ensures result is Invariant)]
    #[inline]
    pub(crate) const fn graph_id_overflow() -> HistoryError {
        HistoryError::Invariant {
            message: "graph ID does not fit usize",
        }
    }
    #[verus_verify]
    #[verus_spec(result => ensures result is GraphLimit)]
    #[inline]
    pub(crate) const fn graph_index_overflow() -> HistoryError {
        HistoryError::GraphLimit {
            limit: super::kernel::MAX_GRAPH_BYTES,
        }
    }
    #[verus_verify]
    #[inline]
    pub(crate) const fn invalid_atom_set() -> HistoryError {
        HistoryError::Invariant {
            message: "invalid primitive atom set",
        }
    }
    #[verus_verify]
    #[inline]
    pub(crate) const fn missing_transition_atom() -> HistoryError {
        HistoryError::Invariant {
            message: "transition primitive missing from atom set",
        }
    }
}
