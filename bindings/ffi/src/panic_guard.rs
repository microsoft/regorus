// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Minimal helpers for catching panics inside the FFI layer.
//!
//! These are not yet wired into the exported functions; they will
//! be used once the integration work is complete.

extern crate alloc;

use crate::common::{RegorusResult, RegorusStatus};

use alloc::string::String;
use core::sync::atomic::{AtomicBool, Ordering};
#[cfg(feature = "std")]
use std::{
    backtrace::Backtrace,
    cell::RefCell,
    panic::{self, AssertUnwindSafe},
};

#[cfg(feature = "std")]
thread_local! {
    // Stashes the formatted panic + backtrace for whichever call last panicked on this thread.
    static PANIC_BACKTRACE: RefCell<Option<String>> = const { RefCell::new(None) };
}

#[cfg(feature = "std")]
type PanicHook = dyn Fn(&panic::PanicHookInfo<'_>) + Sync + Send + 'static;

#[cfg(feature = "std")]
/// RAII helper that installs a per-call panic hook and restores the prior hook on drop.
struct PanicHookGuard {
    previous: Option<Box<PanicHook>>,
}

#[cfg(feature = "std")]
impl PanicHookGuard {
    fn install() -> Self {
        // Remember whatever hook the embedding application already registered.
        let previous = panic::take_hook();
        PANIC_BACKTRACE.with(|slot| {
            slot.replace(None);
        });
        // Install our temporary hook so we can capture a backtrace for this invocation.
        panic::set_hook(Box::new(|info| {
            let backtrace = Backtrace::force_capture();
            PANIC_BACKTRACE.with(|slot| {
                slot.replace(Some(format!(
                    "panic hook observed: {}\nbacktrace:\n{:#?}",
                    info, backtrace
                )));
            });
        }));
        Self {
            previous: Some(previous),
        }
    }
}

#[cfg(feature = "std")]
impl Drop for PanicHookGuard {
    fn drop(&mut self) {
        if let Some(previous) = self.previous.take() {
            // Restore the original panic hook before we return control to the host.
            panic::set_hook(previous);
        }
    }
}

static POISONED: AtomicBool = AtomicBool::new(false);

/// Result of attempting to run `f` while guarding against unwinding.
pub(crate) enum GuardResult<T> {
    /// Closure completed successfully.
    Success(T),
    /// Closure panicked; contains a best-effort string payload.
    Panic(String),
}

pub(crate) fn with_unwind_guard<F>(f: F) -> RegorusResult
where
    F: FnOnce() -> RegorusResult,
{
    if is_poisoned() {
        return poisoned_result();
    }

    // The closure passed across this boundary closes over raw pointers and lock guards.
    // These types are not unwind safe by default and may become poisoned if a panic occurs.
    // We therefore use AssertUnwindSafe to get the compiler to accept the closure.
    // Upon unwind, we mark regorus as poisoned and disallow further use.
    #[cfg(feature = "std")]
    {
        let outcome = {
            let _hook_guard = PanicHookGuard::install();
            match panic::catch_unwind(AssertUnwindSafe(f)) {
                Ok(value) => GuardResult::Success(value),
                Err(payload) => GuardResult::Panic(panic_message_to_string(payload)),
            }
        };
        finalize(outcome)
    }

    #[cfg(not(feature = "std"))]
    return finalize(GuardResult::Success(f()));
}

fn finalize(outcome: GuardResult<RegorusResult>) -> RegorusResult {
    match outcome {
        GuardResult::Success(result) => result,
        GuardResult::Panic(message) => {
            trip_poison();
            RegorusResult::err_with_message(RegorusStatus::Panic, message)
        }
    }
}

#[cfg(feature = "std")]
fn panic_message_to_string(payload: Box<dyn core::any::Any + Send + 'static>) -> String {
    let mut message = if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).into()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        String::from("regorus encountered panic")
    };

    if let Some(backtrace) = take_panic_backtrace() {
        message.push('\n');
        message.push_str(&backtrace);
    }

    message
}

#[cfg(feature = "std")]
fn take_panic_backtrace() -> Option<String> {
    PANIC_BACKTRACE.with(|slot| slot.borrow_mut().take())
}

fn poisoned_result() -> RegorusResult {
    RegorusResult::err_with_message(
        RegorusStatus::Poisoned,
        String::from("regorus is poisoned after a previous panic"),
    )
}

fn trip_poison() {
    POISONED.store(true, Ordering::Release);
}

pub(crate) fn is_poisoned() -> bool {
    POISONED.load(Ordering::Acquire)
}

pub(crate) fn reset_poison() {
    POISONED.store(false, Ordering::Release);
}
