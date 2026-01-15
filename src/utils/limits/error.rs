// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(dead_code)]

use core::fmt;
use core::time::Duration;

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
        }
    }
}

impl core::error::Error for LimitError {}
