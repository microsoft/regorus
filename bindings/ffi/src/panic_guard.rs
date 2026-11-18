// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Minimal helpers for catching panics inside the FFI layer.
//!
//! A panic inside a guarded call is caught, marks regorus as poisoned, and is
//! returned as a `Panic` result whose message includes the panic location and a
//! backtrace. The process-global panic hook is never swapped per call, because
//! concurrent calls would race on it and could leave a stale hook installed.
//! Instead, the first guarded call installs one hook that records panics on
//! threads inside a guarded call and forwards every other panic to the hook
//! that was installed before it. A hook the host installs afterwards replaces
//! it: guarded panics are then still caught, but also reach that hook and lose
//! the extra details. Swapping hooks is not atomic on stable Rust, so a hook the
//! host sets concurrently with the first guarded call can be lost.

extern crate alloc;

use crate::common::{RegorusResult, RegorusStatus};

use alloc::string::String;
use core::sync::atomic::{AtomicBool, Ordering};
#[cfg(feature = "std")]
use std::panic::{self, AssertUnwindSafe};

#[cfg(feature = "std")]
mod hook {
    use alloc::boxed::Box;
    use alloc::string::String;
    use core::cell::{Cell, RefCell};
    use core::sync::atomic::{AtomicBool, Ordering};
    use std::backtrace::Backtrace;
    use std::panic::{self, PanicHookInfo};
    use std::sync::{Mutex, PoisonError};

    static INSTALLED: AtomicBool = AtomicBool::new(false);
    static INSTALL_LOCK: Mutex<()> = Mutex::new(());

    std::thread_local! {
        // Number of guarded calls active on this thread (guards can nest).
        static GUARD_DEPTH: Cell<usize> = const { Cell::new(0) };
        // Formatted panic + backtrace for whichever guarded call last panicked on this thread.
        static PANIC_BACKTRACE: RefCell<Option<String>> = const { RefCell::new(None) };
    }

    /// Installs the recording hook once per process, chaining to the current hook.
    fn ensure_installed() {
        // The hook cannot be changed while this thread is unwinding.
        if INSTALLED.load(Ordering::Acquire) || std::thread::panicking() {
            return;
        }
        let _install = INSTALL_LOCK.lock().unwrap_or_else(PoisonError::into_inner);
        if INSTALLED.load(Ordering::Acquire) {
            return;
        }
        let previous = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            if !record(info) {
                previous(info);
            }
        }));
        INSTALLED.store(true, Ordering::Release);
    }

    #[cfg(test)]
    type Hook = Box<dyn Fn(&PanicHookInfo<'_>) + Sync + Send + 'static>;

    /// Swaps the process hook without racing an install; the next guarded call reinstalls.
    #[cfg(test)]
    pub(super) fn replace_process_hook(new: Hook) -> Hook {
        let _install = INSTALL_LOCK.lock().unwrap_or_else(PoisonError::into_inner);
        let previous = panic::take_hook();
        panic::set_hook(new);
        INSTALLED.store(false, Ordering::Release);
        previous
    }

    /// Records a panic raised inside a guarded call; returns false for any other panic.
    fn record(info: &PanicHookInfo<'_>) -> bool {
        // `try_with`: thread-locals may already be destroyed on this thread.
        if !GUARD_DEPTH
            .try_with(|depth| depth.get() > 0)
            .unwrap_or(false)
        {
            return false;
        }
        let backtrace = Backtrace::force_capture();
        store_details(Some(alloc::format!(
            "panic hook observed: {info}\nbacktrace:\n{backtrace:#?}"
        )));
        true
    }

    fn store_details(details: Option<String>) {
        let _ = PANIC_BACKTRACE.try_with(|slot| {
            if let Ok(mut slot) = slot.try_borrow_mut() {
                *slot = details;
            }
        });
    }

    pub(super) fn take_panic_backtrace() -> Option<String> {
        PANIC_BACKTRACE
            .try_with(|slot| slot.try_borrow_mut().ok().and_then(|mut slot| slot.take()))
            .ok()
            .flatten()
    }

    /// Marks the current thread as inside a guarded call for the scope's lifetime.
    pub(super) struct GuardScope(());

    impl GuardScope {
        pub(super) fn enter() -> Self {
            ensure_installed();
            let _ = GUARD_DEPTH.try_with(|depth| depth.set(depth.get().saturating_add(1)));
            store_details(None);
            GuardScope(())
        }
    }

    impl Drop for GuardScope {
        fn drop(&mut self) {
            let _ = GUARD_DEPTH.try_with(|depth| depth.set(depth.get().saturating_sub(1)));
        }
    }
}

static POISONED: AtomicBool = AtomicBool::new(false);

#[cfg(all(test, feature = "std"))]
static POISON_TEST_GATE: std::sync::RwLock<()> = std::sync::RwLock::new(());

#[cfg(all(test, feature = "std"))]
std::thread_local! {
    static POISON_TEST_GATE_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(all(test, feature = "std"))]
pub(crate) struct PoisonTestLock {
    lock: Option<std::sync::RwLockWriteGuard<'static, ()>>,
}

#[cfg(all(test, feature = "std"))]
impl Drop for PoisonTestLock {
    fn drop(&mut self) {
        self.lock.take();
        decrement_poison_test_gate_depth();
    }
}

#[cfg(all(test, feature = "std"))]
pub(crate) fn lock_poison_test_state() -> PoisonTestLock {
    debug_assert!(
        !poison_test_gate_is_held(),
        "the poison test gate cannot be upgraded from a nested guarded call"
    );
    let lock = POISON_TEST_GATE
        .write()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    increment_poison_test_gate_depth();
    PoisonTestLock { lock: Some(lock) }
}

#[cfg(all(test, feature = "std"))]
struct PoisonTestCallLock {
    lock: Option<std::sync::RwLockReadGuard<'static, ()>>,
}

#[cfg(all(test, feature = "std"))]
impl Drop for PoisonTestCallLock {
    fn drop(&mut self) {
        self.lock.take();
        decrement_poison_test_gate_depth();
    }
}

#[cfg(all(test, feature = "std"))]
fn poison_test_call_lock() -> PoisonTestCallLock {
    let nested = poison_test_gate_is_held();
    increment_poison_test_gate_depth();
    if nested {
        PoisonTestCallLock { lock: None }
    } else {
        let lock = POISON_TEST_GATE
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        PoisonTestCallLock { lock: Some(lock) }
    }
}

#[cfg(all(test, feature = "std"))]
fn poison_test_gate_is_held() -> bool {
    POISON_TEST_GATE_DEPTH.with(|depth| depth.get() > 0)
}

#[cfg(all(test, feature = "std"))]
fn increment_poison_test_gate_depth() {
    POISON_TEST_GATE_DEPTH.with(|depth| depth.set(depth.get().saturating_add(1)));
}

#[cfg(all(test, feature = "std"))]
fn decrement_poison_test_gate_depth() {
    POISON_TEST_GATE_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
}

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
    #[cfg(all(test, feature = "std"))]
    let _poison_test_call_lock = poison_test_call_lock();

    if is_poisoned() {
        return poisoned_result();
    }

    // Upon unwind, we mark regorus as poisoned and disallow further use.
    #[cfg(feature = "std")]
    return finalize(catch_panic(f));

    #[cfg(not(feature = "std"))]
    return finalize(GuardResult::Success(f()));
}

#[cfg(feature = "std")]
fn catch_panic<F>(f: F) -> GuardResult<RegorusResult>
where
    F: FnOnce() -> RegorusResult,
{
    let _guard_scope = hook::GuardScope::enter();
    // The closure passed across this boundary closes over raw pointers and lock guards.
    // These types are not unwind safe by default and may become poisoned if a panic occurs.
    // We therefore use AssertUnwindSafe to get the compiler to accept the closure.
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(value) => GuardResult::Success(value),
        Err(payload) => GuardResult::Panic(panic_message_to_string(payload)),
    }
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

    if let Some(backtrace) = hook::take_panic_backtrace() {
        message.push('\n');
        message.push_str(&backtrace);
    }

    message
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

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::{catch_panic, hook, with_unwind_guard, GuardResult};
    use crate::common::{regorus_result_drop, RegorusResult, RegorusStatus};
    use std::panic;
    use std::sync::{mpsc, Mutex};
    use std::time::Duration;

    const TEST_PANIC_PREFIX: &str = "panic_guard_test:";
    static HOST_HOOK_PANICS: Mutex<Vec<String>> = Mutex::new(Vec::new());

    fn host_hook(info: &panic::PanicHookInfo<'_>) {
        let payload = info
            .payload()
            .downcast_ref::<&str>()
            .map(|s| s.to_string())
            .or_else(|| info.payload().downcast_ref::<String>().cloned())
            .unwrap_or_default();
        if payload.starts_with(TEST_PANIC_PREFIX) {
            HOST_HOOK_PANICS
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .push(payload);
        }
    }

    #[test]
    fn concurrent_guarded_panics_keep_their_messages_and_the_host_hook() {
        const THREADS: usize = 8;
        const ITERATIONS: usize = 40;

        // `catch_panic` never touches the poison flag, so this test does not take the
        // poison test gate; it is the only test that replaces the process hook.
        HOST_HOOK_PANICS
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clear();
        let previous_hook = hook::replace_process_hook(Box::new(host_hook));

        let workers: Vec<_> = (0..THREADS)
            .map(|thread| {
                std::thread::spawn(move || {
                    let mut problems = Vec::new();
                    for iteration in 0..ITERATIONS {
                        let payload = format!("{TEST_PANIC_PREFIX} t{thread} i{iteration}");
                        let panics = (thread + iteration) % 2 == 0;
                        let expected = payload.clone();
                        let outcome = catch_panic(move || {
                            if panics {
                                panic!("{expected}");
                            }
                            RegorusResult::ok_void()
                        });
                        match (panics, outcome) {
                            (true, GuardResult::Panic(message)) => {
                                let observed = message.split_once("panic hook observed: ");
                                let own_location = observed.is_some_and(|(head, hook)| {
                                    head.starts_with(&payload)
                                        && hook.contains(&payload)
                                        && hook.contains(file!())
                                });
                                if !own_location {
                                    problems.push(format!("{payload}: message {message:?}"));
                                }
                            }
                            (false, GuardResult::Success(result)) => regorus_result_drop(result),
                            (true, GuardResult::Success(result)) => {
                                regorus_result_drop(result);
                                problems.push(format!("{payload}: panic not caught"));
                            }
                            (false, GuardResult::Panic(message)) => {
                                problems.push(format!("{payload}: unexpected panic {message:?}"));
                            }
                        }
                    }
                    problems
                })
            })
            .collect();
        let mut problems: Vec<String> = workers
            .into_iter()
            .flat_map(|worker| {
                worker
                    .join()
                    .unwrap_or_else(|_| vec!["worker panicked".into()])
            })
            .collect();

        // An unguarded panic on another thread while a guarded call is in progress.
        let (entered_sender, entered_receiver) = mpsc::channel();
        let (release_sender, release_receiver) = mpsc::channel::<()>();
        let holder = std::thread::spawn(move || {
            let outcome = catch_panic(move || {
                let _ = entered_sender.send(());
                let _ = release_receiver.recv_timeout(Duration::from_secs(5));
                RegorusResult::ok_void()
            });
            if let GuardResult::Success(result) = outcome {
                regorus_result_drop(result);
            }
        });
        if entered_receiver
            .recv_timeout(Duration::from_secs(5))
            .is_err()
        {
            problems.push("guarded call on the holder thread did not start".into());
        }
        let during = format!("{TEST_PANIC_PREFIX} during a guarded call");
        let expected = during.clone();
        let _ = std::thread::spawn(move || panic!("{expected}")).join();
        let _ = release_sender.send(());
        let _ = holder.join();

        // Nested and earlier guarded calls on a thread, then an unguarded panic on it.
        let after = format!("{TEST_PANIC_PREFIX} after guarded calls");
        let expected = after.clone();
        let same_thread = std::thread::spawn(move || {
            let mut problems = Vec::new();
            let nested = catch_panic(|| {
                if let GuardResult::Success(result) = catch_panic(RegorusResult::ok_void) {
                    regorus_result_drop(result);
                }
                panic!("{TEST_PANIC_PREFIX} outer after inner")
            });
            match nested {
                GuardResult::Panic(message) if message.contains("panic hook observed: ") => {}
                _ => problems.push("panic after a nested guarded call lost its details".into()),
            }
            let inner_caught = catch_panic(|| {
                let _ = panic::catch_unwind(|| panic!("{TEST_PANIC_PREFIX} caught inside"));
                RegorusResult::ok_void()
            });
            if let GuardResult::Success(result) = inner_caught {
                regorus_result_drop(result);
            }
            // `resume_unwind` skips the hook, so this call has no details of its own.
            let resumed = catch_panic(|| panic::resume_unwind(Box::new(String::from("resumed"))));
            match resumed {
                GuardResult::Panic(message) if message == "resumed" => {}
                _ => problems.push("a later guarded call showed stale panic details".into()),
            }
            let _ = panic::catch_unwind(|| panic!("{expected}"));
            problems
        });
        problems.extend(
            same_thread
                .join()
                .unwrap_or_else(|_| vec!["same-thread checks panicked".into()]),
        );

        let host_panics = core::mem::take(
            &mut *HOST_HOOK_PANICS
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner()),
        );
        if host_panics != [during, after] {
            problems.push(format!(
                "host hook must see only the unguarded panics, saw {} panics: {:?}",
                host_panics.len(),
                host_panics.iter().take(5).collect::<Vec<_>>()
            ));
        }

        // Restore before asserting: the hook cannot be changed while unwinding.
        drop(hook::replace_process_hook(previous_hook));
        assert!(
            problems.is_empty(),
            "{} problems: {:#?}",
            problems.len(),
            &problems[..problems.len().min(10)]
        );
    }

    #[test]
    fn ordinary_guarded_calls_are_not_serialized_by_the_poison_test_gate() {
        let (first_entered_sender, first_entered_receiver) = mpsc::channel();
        let (second_entered_sender, second_entered_receiver) = mpsc::channel();

        let first = std::thread::spawn(move || {
            let result = with_unwind_guard(|| {
                let _ = first_entered_sender.send(());
                let second_entered = second_entered_receiver
                    .recv_timeout(Duration::from_secs(1))
                    .is_ok();
                RegorusResult::ok_bool(second_entered)
            });
            let success = matches!(result.status, RegorusStatus::Ok) && result.bool_value;
            regorus_result_drop(result);
            success
        });

        assert!(
            first_entered_receiver
                .recv_timeout(Duration::from_secs(1))
                .is_ok(),
            "first guarded call did not start"
        );

        let second = std::thread::spawn(move || {
            let result = with_unwind_guard(|| {
                let _ = second_entered_sender.send(());
                RegorusResult::ok_void()
            });
            let success = matches!(result.status, RegorusStatus::Ok);
            regorus_result_drop(result);
            success
        });

        let first_success = first.join().unwrap_or(false);
        let second_success = second.join().unwrap_or(false);
        assert!(second_success, "second guarded call did not complete");
        assert!(
            first_success,
            "ordinary guarded calls were serialized by the poison test gate"
        );
    }
}
