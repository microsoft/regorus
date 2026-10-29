// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::utils::limits::{
    check_memory_limit_if_needed, enforce_memory_limit, monotonic_now, ExecutionTimer, LimitError,
};
use junco_core::limits::Limits;
use vstd::prelude::*;

#[verus_verify]
pub struct RegorusLimits<'a> {
    pub(crate) timer: &'a mut ExecutionTimer,
}

#[verus_verify]
impl RegorusLimits<'_> {
    #[cold]
    #[inline(never)]
    fn deadline_check(&mut self) -> Result<(), LimitError> {
        if let Some(now) = monotonic_now() {
            self.timer.check_now(now)?;
        }
        Ok(())
    }
}

#[verus_verify]
impl Limits for RegorusLimits<'_> {
    #[inline(always)]
    fn checkpoint(&mut self) -> Result<(), LimitError> {
        if self.timer.accumulate(1) {
            self.deadline_check()?;
        }
        check_memory_limit_if_needed()?;
        Ok(())
    }

    fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
        if self.timer.config().is_some() {
            if let Some(now) = monotonic_now() {
                self.timer.check_now(now)?;
            }
        }
        self.checkpoint()
    }

    fn enforce_memory(&mut self) -> Result<(), LimitError> {
        enforce_memory_limit()
    }
}
