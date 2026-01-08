// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Helpers for cooperative execution time limits.

#![allow(dead_code)]

mod error;
mod time;

#[allow(unused_imports)]
pub use error::LimitError;
#[allow(unused_imports)]
pub use time::{
    global_execution_timer_config, monotonic_now, set_global_execution_timer_config,
    ExecutionTimer, ExecutionTimerConfig, TimeSource,
};

#[cfg(test)]
pub use time::acquire_limits_test_lock;

#[cfg(any(test, not(feature = "std")))]
#[allow(unused_imports)]
pub use time::{set_time_source, TimeSourceRegistrationError};
