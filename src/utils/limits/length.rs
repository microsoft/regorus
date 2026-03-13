// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::num::{NonZeroU32, NonZeroUsize};

/// Policy source length limits enforced when loading policy files.
///
/// These limits reject pathological or generated inputs early, before parsing begins.
/// Use [`Default::default`] for the built-in thresholds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolicyLengthConfig {
    /// Maximum column width per line (default: 1024).
    pub max_col: NonZeroU32,
    /// Maximum policy file size in bytes (default: 1 MiB).
    pub max_file_bytes: NonZeroUsize,
    /// Maximum number of lines per policy file (default: 20 000).
    pub max_lines: NonZeroUsize,
}

// Maximum column width to prevent overflow and catch pathological input.
// Lines exceeding this are likely minified/generated code or attack attempts.
pub const DEFAULT_MAX_COL: NonZeroU32 = NonZeroU32::new(1024).unwrap();
// Maximum allowed policy file size in bytes (1 MiB) to reject pathological inputs early.
pub const DEFAULT_MAX_FILE_BYTES: NonZeroUsize = NonZeroUsize::new(1_048_576).unwrap();
// Maximum allowed number of lines to avoid pathological or minified inputs.
pub const DEFAULT_MAX_LINES: NonZeroUsize = NonZeroUsize::new(20_000).unwrap();

impl Default for PolicyLengthConfig {
    fn default() -> Self {
        Self {
            max_col: DEFAULT_MAX_COL,
            max_file_bytes: DEFAULT_MAX_FILE_BYTES,
            max_lines: DEFAULT_MAX_LINES,
        }
    }
}
