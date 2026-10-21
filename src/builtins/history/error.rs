// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

use crate::utils::limits::LimitError;
use alloc::string::String;
#[cfg(verus_keep_ghost)]
use vstd::prelude::verus_spec;
use vstd::prelude::verus_verify;

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Debug, thiserror::Error)]
pub(crate) enum HistoryError {
    #[error("invalid history policy at {path}: {message}")]
    InvalidPolicy { path: String, message: &'static str },
    #[error("history variable {name:?} is not bound by request pattern")]
    UnboundVariable { name: String },
    #[error("history.match symbolic graph payload exceeds {limit} bytes")]
    GraphLimit { limit: usize },
    #[error("history.match allocation failed")]
    AllocationFailed,
    #[error("history.match arena exhausted")]
    ArenaExhausted,
    #[error("history.match invariant violated: {message}")]
    Invariant { message: &'static str },
    #[error(transparent)]
    Limit(#[from] LimitError),
}

#[verus_verify]
impl HistoryError {
    pub(crate) const fn is_fatal(&self) -> bool {
        matches!(
            self,
            Self::GraphLimit { .. }
                | Self::AllocationFailed
                | Self::ArenaExhausted
                | Self::Invariant { .. }
                | Self::Limit(_)
        )
    }
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
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result is Invariant))]
#[inline]
pub(crate) const fn graph_id_overflow() -> HistoryError {
    HistoryError::Invariant {
        message: "graph ID does not fit usize",
    }
}
#[verus_verify]
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result is GraphLimit))]
#[inline]
pub(crate) const fn graph_index_overflow() -> HistoryError {
    HistoryError::GraphLimit { limit: 100 * 1024 }
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
