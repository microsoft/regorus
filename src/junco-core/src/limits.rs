// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(dead_code)]

use core::fmt;
use core::time::Duration;
use vstd::prelude::{verus_spec, verus_verify};

/// Errors reported when execution time or memory ceilings are enforced.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LimitError {
    /// Reported when the execution timer observes elapsed time beyond the configured limit.
    TimeLimitExceeded {
        /// Elapsed work duration when the threshold was exceeded.
        elapsed: Duration,
        /// Configured time limit.
        limit: Duration,
    },
    /// Reported when the memory tracker estimates usage beyond the configured limit.
    MemoryLimitExceeded {
        /// Estimated bytes in use when the limit was detected.
        usage: u64,
        /// Configured memory ceiling in bytes.
        limit: u64,
    },
    /// Reported when a compiled regex NFA exceeds the configured size limit.
    RegexSizeLimitExceeded {
        /// Configured compiled-NFA size ceiling in bytes.
        limit: usize,
    },
}

impl fmt::Debug for LimitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TimeLimitExceeded { elapsed, limit } => f
                .debug_struct("TimeLimitExceeded")
                .field("elapsed", elapsed)
                .field("limit", limit)
                .finish(),
            Self::MemoryLimitExceeded { usage, limit } => f
                .debug_struct("MemoryLimitExceeded")
                .field("usage", usage)
                .field("limit", limit)
                .finish(),
            Self::RegexSizeLimitExceeded { limit } => f
                .debug_struct("RegexSizeLimitExceeded")
                .field("limit", limit)
                .finish(),
        }
    }
}

impl fmt::Display for LimitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TimeLimitExceeded { elapsed, limit } => {
                let elapsed_ns = elapsed.as_nanos();
                let limit_ns = limit.as_nanos();
                write!(
                    f,
                    "execution exceeded time limit (elapsed={}ns, limit={}ns)",
                    elapsed_ns, limit_ns
                )
            }
            Self::MemoryLimitExceeded { usage, limit } => {
                write!(
                    f,
                    "execution exceeded memory limit (usage={} bytes, limit={} bytes)",
                    usage, limit
                )
            }
            Self::RegexSizeLimitExceeded { limit } => {
                write!(f, "compiled regex exceeded size limit ({} bytes)", limit)
            }
        }
    }
}

impl core::error::Error for LimitError {}

#[cfg(verus_keep_ghost)]
vstd::prelude::verus! {
    #[verifier::external_type_specification]
    #[verifier::external_body]
    pub struct ExLimitError(LimitError);
}

/// Maximum retained symbolic graph payload in bytes.
#[verus_verify]
pub const MAX_GRAPH_BYTES: usize = 100 * 1024;

/// Host resource observations used by the shared history engine.
#[verus_verify]
pub trait Limits {
    fn checkpoint(&mut self) -> Result<(), LimitError>;
    fn publication_checkpoint(&mut self) -> Result<(), LimitError>;
    fn enforce_memory(&mut self) -> Result<(), LimitError>;
}

/// No configured host budget; allocation and structural bounds still apply.
#[verus_verify]
pub struct Unmetered;

#[verus_verify]
impl Limits for Unmetered {
    #[verus_spec(result => ensures result == Ok(()))]
    fn checkpoint(&mut self) -> Result<(), LimitError> {
        Ok(())
    }

    #[verus_spec(result => ensures result == Ok(()))]
    fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
        Ok(())
    }

    #[verus_spec(result => ensures result == Ok(()))]
    fn enforce_memory(&mut self) -> Result<(), LimitError> {
        Ok(())
    }
}
