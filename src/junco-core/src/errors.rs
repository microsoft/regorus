// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.

use crate::limits::LimitError;
use alloc::borrow::ToOwned;
use alloc::string::String;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum HistoryError {
    #[error("invalid history policy at {path}: {message}")]
    InvalidPolicy { path: String, message: &'static str },
    #[error("history variable {name:?} is not bound by request pattern")]
    UnboundVariable { name: String },
    #[error("history symbolic graph payload exceeds {limit} bytes")]
    GraphBudget { limit: usize },
    #[error("history graph index or size computation overflowed")]
    GraphIndex,
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

impl From<LimitError> for HistoryError {
    fn from(error: LimitError) -> Self {
        Self::Limit(error)
    }
}

impl HistoryError {
    pub fn invalid_policy(path: &str, message: &'static str) -> Self {
        Self::InvalidPolicy {
            path: path.to_owned(),
            message,
        }
    }
    pub const fn invariant(message: &'static str) -> HistoryError {
        HistoryError::Invariant { message }
    }

    #[inline]
    pub const fn graph_index_overflow() -> HistoryError {
        HistoryError::GraphIndex
    }
}

/// Rule-compilation failure detected before a validator can execute.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CompileError {
    /// The head must have exactly the event type's number of coordinates.
    #[error("head has {found} slots but the event type has {expected}")]
    HeadArity { expected: usize, found: usize },
    /// Tagged constants may only be used in their own coordinate.
    #[error("constant of coordinate {coordinate} used in coordinate {component}")]
    ComponentCoordinate { component: usize, coordinate: usize },
    /// One variable name occurs in different product components in the same rule.
    #[error("variable {name:?} occurs in different product components")]
    VariableComponentConflict { name: String },
    /// A tail references a variable that its head does not bind.
    #[error("tail variable {name:?} is not bound by the head")]
    UnboundVariable { name: String },
    #[error(transparent)]
    Runtime(HistoryError),
}

impl From<HistoryError> for CompileError {
    fn from(error: HistoryError) -> Self {
        Self::Runtime(error)
    }
}
