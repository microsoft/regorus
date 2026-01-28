// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

/*
ExecutionTimer provides cooperative wall-clock enforcement for long-running
policy evaluations. The timer tracks three pieces of state:
- ExecutionTimerConfig, which holds the optional wall-clock budget and the
    interval (in work units) between time checks.
- The monotonic start instant recorded via start(now), expressed as a
    Duration from whatever time source the engine uses.
- An accumulator that counts work units so callers can amortize expensive
    time queries; once the counter reaches the configured interval, tick()
    performs a check and preserves any remainder.

The timer never calls into a clock directly. Instead, callers pass the
current monotonic Duration to start(), tick(), check_now(), or elapsed().
Helper monotonic_now() returns that Duration by selecting a TimeSource
implementation:
- On std builds we use StdTimeSource, which anchors a std::time::Instant via
    OnceLock and reports elapsed() for stable, monotonic measurements.
- In tests and truly no_std builds we allow integrators to inject a global
    &'static dyn TimeSource using set_time_source(). This override lives behind
    a spin::Mutex<Option<...>> so the critical section stays small (just a
    pointer read) while remaining usable in bare-metal environments.

With this design the interpreter can cheaply interleave work with periodic
limit checks. Std builds automatically use the Instant-backed source, while
embedded users configure both their ExecutionTimerConfig and a single global
time source without paying for per-interpreter callbacks or unsafe code.
*/

use core::num::NonZeroU32;
use core::time::Duration;

use spin::Mutex;

use super::LimitError;

#[cfg(test)]
use std::sync::{Mutex as StdMutex, MutexGuard as StdMutexGuard};

/// Public configuration for the cooperative execution time limiter.
///
/// The limiter reads this struct to determine how often it should check for wall-clock overruns and
/// what deadline to enforce. Engines without a configuration skip time checks; when a configuration
/// is present, it normally pairs a concrete deadline with a small [`NonZeroU32`] interval so
/// interpreter loops amortize their clock reads without skipping checks for long stretches of
/// repetitive work. The process-wide fallback installed via [`set_fallback_execution_timer_config`]
/// supplies this configuration when an engine lacks its own override.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecutionTimerConfig {
    /// Maximum allowed wall-clock duration.
    pub limit: Duration,
    /// Number of work units between time checks (minimum 1).
    pub check_interval: NonZeroU32,
}

/// Cooperative time-limit tracker shared across interpreter and VM loops.
#[derive(Debug)]
pub struct ExecutionTimer {
    config: Option<ExecutionTimerConfig>,
    start: Option<Duration>,
    accumulated_units: u32,
    last_elapsed: Duration,
}

/// Monotonic time provider.
pub trait TimeSource: Send + Sync {
    /// Returns a non-decreasing duration since an arbitrary anchor.
    fn now(&self) -> Option<Duration>;
}

#[cfg(feature = "std")]
#[derive(Debug)]
struct StdTimeSource;

#[cfg(feature = "std")]
impl StdTimeSource {
    const fn new() -> Self {
        Self
    }
}

#[cfg(feature = "std")]
impl TimeSource for StdTimeSource {
    fn now(&self) -> Option<Duration> {
        use std::sync::OnceLock;

        static ANCHOR: OnceLock<std::time::Instant> = OnceLock::new();
        let anchor = ANCHOR.get_or_init(std::time::Instant::now);
        Some(anchor.elapsed())
    }
}

#[cfg(feature = "std")]
static STD_TIME_SOURCE: StdTimeSource = StdTimeSource::new();

#[cfg(any(test, not(feature = "std")))]
static TIME_SOURCE_OVERRIDE: Mutex<Option<&'static dyn TimeSource>> = Mutex::new(None);

#[cfg(any(test, not(feature = "std")))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimeSourceRegistrationError {
    AlreadySet,
}

#[cfg(any(test, not(feature = "std")))]
impl core::fmt::Display for TimeSourceRegistrationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::AlreadySet => f.write_str("time source already configured"),
        }
    }
}

#[cfg(any(test, not(feature = "std")))]
impl core::error::Error for TimeSourceRegistrationError {}

static FALLBACK_EXECUTION_TIMER_CONFIG: Mutex<Option<ExecutionTimerConfig>> = Mutex::new(None);

#[cfg(test)]
static LIMITS_TEST_LOCK: StdMutex<()> = StdMutex::new(());

#[cfg(test)]
pub fn acquire_limits_test_lock() -> StdMutexGuard<'static, ()> {
    LIMITS_TEST_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Returns the duration supplied by the chosen source for this build.
pub fn monotonic_now() -> Option<Duration> {
    #[cfg(any(test, not(feature = "std")))]
    // Spin mutex acquisition incurs only a few atomic ops; the critical section
    // is a single pointer read, so uncontended overhead stays tiny.
    if let Some(source) = {
        let guard = TIME_SOURCE_OVERRIDE.lock();
        *guard
    } {
        if let Some(duration) = source.now() {
            return Some(duration);
        }
    }

    #[cfg(feature = "std")]
    {
        STD_TIME_SOURCE.now()
    }

    #[cfg(not(feature = "std"))]
    {
        None
    }
}

#[cfg(any(test, not(feature = "std")))]
pub fn set_time_source(source: &'static dyn TimeSource) -> Result<(), TimeSourceRegistrationError> {
    let mut slot = TIME_SOURCE_OVERRIDE.lock();
    if slot.is_some() {
        Err(TimeSourceRegistrationError::AlreadySet)
    } else {
        *slot = Some(source);
        Ok(())
    }
}

/// Sets the process-wide fallback configuration for the execution time limiter. Engine instances can
/// override this fallback via [`Engine::set_execution_timer_config`](crate::Engine::set_execution_timer_config).
///
/// # Examples
///
/// ```
/// use std::num::NonZeroU32;
/// use std::time::Duration;
/// use regorus::utils::limits::{
///     fallback_execution_timer_config,
///     set_fallback_execution_timer_config,
///     ExecutionTimerConfig,
/// };
///
/// let config = ExecutionTimerConfig {
///     limit: Duration::from_secs(1),
///     check_interval: NonZeroU32::new(10).unwrap(),
/// };
/// set_fallback_execution_timer_config(Some(config));
/// assert_eq!(fallback_execution_timer_config(), Some(config));
/// ```
pub fn set_fallback_execution_timer_config(config: Option<ExecutionTimerConfig>) {
    *FALLBACK_EXECUTION_TIMER_CONFIG.lock() = config;
}

/// Returns the process-wide fallback configuration for the execution time limiter, if any.
///
/// # Examples
///
/// ```
/// use regorus::utils::limits::fallback_execution_timer_config;
///
/// // By default no fallback execution timer is configured.
/// assert!(fallback_execution_timer_config().is_none());
/// ```
pub fn fallback_execution_timer_config() -> Option<ExecutionTimerConfig> {
    let guard = FALLBACK_EXECUTION_TIMER_CONFIG.lock();
    guard.as_ref().copied()
}

impl ExecutionTimer {
    /// Construct a new timer with the provided configuration.
    pub const fn new(config: Option<ExecutionTimerConfig>) -> Self {
        Self {
            config,
            start: None,
            accumulated_units: 0,
            last_elapsed: Duration::ZERO,
        }
    }

    /// Reset the timer state to its initial configuration without recording a start instant.
    pub const fn reset(&mut self) {
        self.start = None;
        self.accumulated_units = 0;
        self.last_elapsed = Duration::ZERO;
    }

    /// Reset any prior state and record the start instant.
    pub const fn start(&mut self, now: Duration) {
        self.start = Some(now);
        self.accumulated_units = 0;
        self.last_elapsed = Duration::ZERO;
    }

    /// Returns the timer configuration.
    pub const fn config(&self) -> Option<ExecutionTimerConfig> {
        self.config
    }

    /// Returns the configured limit.
    pub const fn limit(&self) -> Option<Duration> {
        match self.config {
            Some(config) => Some(config.limit),
            None => None,
        }
    }

    /// Returns the last elapsed duration recorded by a check.
    pub const fn last_elapsed(&self) -> Duration {
        self.last_elapsed
    }

    /// Increment work units and run the periodic limit check when necessary.
    pub fn tick(&mut self, work_units: u32, now: Duration) -> Result<(), LimitError> {
        let Some(config) = self.config else {
            return Ok(());
        };
        self.accumulated_units = self.accumulated_units.saturating_add(work_units);
        if self.accumulated_units < config.check_interval.get() {
            return Ok(());
        }

        // Preserve the remainder so that callers do not lose fractional work.
        let interval = config.check_interval.get();
        self.accumulated_units %= interval;
        self.check_now(now)
    }

    /// Force an immediate check against the configured deadline.
    pub fn check_now(&mut self, now: Duration) -> Result<(), LimitError> {
        let Some(config) = self.config else {
            return Ok(());
        };
        let Some(start) = self.start else {
            return Ok(());
        };

        let elapsed = now.checked_sub(start).unwrap_or(Duration::ZERO);
        self.last_elapsed = elapsed;
        if elapsed > config.limit {
            return Err(LimitError::TimeLimitExceeded {
                elapsed,
                limit: config.limit,
            });
        }
        Ok(())
    }

    /// Compute elapsed time relative to the recorded start, if available.
    pub fn elapsed(&self, now: Duration) -> Option<Duration> {
        let start = self.start?;
        Some(now.checked_sub(start).unwrap_or(Duration::ZERO))
    }

    /// Realign the timer start so that a previously consumed `elapsed` duration is preserved while
    /// ignoring any wall-clock time that passed during a suspension window.
    pub const fn resume_from_elapsed(&mut self, now: Duration, elapsed: Duration) {
        if self.config.is_none() {
            return;
        }

        self.start = Some(now.saturating_sub(elapsed));
        self.last_elapsed = elapsed;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroU32;
    use core::sync::atomic::{AtomicU64, Ordering};
    use core::time::Duration;

    fn nz(value: u32) -> NonZeroU32 {
        NonZeroU32::new(value).unwrap_or(NonZeroU32::MIN)
    }

    #[test]
    fn tick_defers_checks_until_interval_is_reached() {
        let mut timer = ExecutionTimer::new(Some(ExecutionTimerConfig {
            limit: Duration::from_millis(100),
            check_interval: nz(4),
        }));

        timer.start(Duration::from_millis(0));

        for step in 1..4 {
            let now = Duration::from_millis((step * 10) as u64);
            let result = timer.tick(1, now);
            assert_eq!(result, Ok(()), "tick before reaching interval must succeed");
            assert_eq!(timer.last_elapsed(), Duration::ZERO);
        }

        let result = timer.tick(1, Duration::from_millis(40));
        assert_eq!(result, Ok(()), "tick at interval boundary must succeed");
        assert_eq!(timer.last_elapsed(), Duration::from_millis(40));
    }

    #[test]
    fn check_now_reports_limit_exceeded() {
        let mut timer = ExecutionTimer::new(Some(ExecutionTimerConfig {
            limit: Duration::from_millis(25),
            check_interval: nz(1),
        }));

        timer.start(Duration::from_millis(0));
        assert_eq!(
            timer.tick(1, Duration::from_millis(10)),
            Ok(()),
            "tick before limit breach must succeed"
        );

        let result = timer.check_now(Duration::from_millis(30));
        assert!(matches!(&result, Err(LimitError::TimeLimitExceeded { .. })));

        if let Err(LimitError::TimeLimitExceeded { elapsed, limit }) = result {
            assert!(elapsed > limit);
            assert_eq!(limit, Duration::from_millis(25));
        }
    }

    #[test]
    fn tick_reports_limit_exceeded() {
        let mut timer = ExecutionTimer::new(Some(ExecutionTimerConfig {
            limit: Duration::from_millis(30),
            check_interval: nz(2),
        }));

        timer.start(Duration::from_millis(0));
        assert_eq!(
            timer.tick(1, Duration::from_millis(10)),
            Ok(()),
            "initial tick must succeed"
        );

        let result = timer.tick(1, Duration::from_millis(35));
        assert!(matches!(&result, Err(LimitError::TimeLimitExceeded { .. })));

        if let Err(LimitError::TimeLimitExceeded { elapsed, limit }) = result {
            assert!(elapsed > limit);
            assert_eq!(limit, Duration::from_millis(30));
            assert_eq!(timer.last_elapsed(), elapsed);
        }
    }

    #[test]
    fn tick_before_start_is_noop() {
        let mut timer = ExecutionTimer::new(Some(ExecutionTimerConfig {
            limit: Duration::from_secs(1),
            check_interval: nz(1),
        }));

        let result = timer.tick(1, Duration::from_millis(100));
        assert_eq!(result, Ok(()), "tick before start should be ignored");
        assert_eq!(timer.last_elapsed(), Duration::ZERO);
        assert!(timer.elapsed(Duration::from_millis(200)).is_none());
    }

    #[test]
    fn check_now_allows_elapsed_equal_to_limit() {
        let mut timer = ExecutionTimer::new(Some(ExecutionTimerConfig {
            limit: Duration::from_millis(50),
            check_interval: nz(1),
        }));

        timer.start(Duration::from_millis(0));
        assert_eq!(
            timer.tick(1, Duration::from_millis(30)),
            Ok(()),
            "tick prior to equality check must succeed"
        );
        let result = timer.check_now(Duration::from_millis(50));
        assert_eq!(result, Ok(()), "elapsed equal to limit must not fail");
        assert_eq!(timer.last_elapsed(), Duration::from_millis(50));
    }

    #[test]
    fn tick_is_noop_when_limit_disabled() {
        let mut timer = ExecutionTimer::new(None);

        timer.start(Duration::from_millis(0));

        for step in 0..8 {
            let now = Duration::from_millis((step + 1) as u64);
            assert_eq!(
                timer.tick(1, now),
                Ok(()),
                "ticks with disabled limit must succeed"
            );
        }

        assert_eq!(timer.last_elapsed(), Duration::ZERO);
    }

    #[test]
    fn check_now_is_noop_before_start() {
        let mut timer = ExecutionTimer::new(None);
        let result = timer.check_now(Duration::from_secs(1));
        assert_eq!(result, Ok(()), "check before start must be ignored");
        assert!(timer.elapsed(Duration::from_secs(2)).is_none());
    }

    #[test]
    fn elapsed_reports_offset_from_start() {
        let mut timer = ExecutionTimer::new(None);
        timer.start(Duration::from_millis(5));
        let elapsed = timer.elapsed(Duration::from_millis(20));
        assert_eq!(elapsed, Some(Duration::from_millis(15)));
    }

    #[test]
    fn monotonic_now_uses_override_when_present() {
        static TEST_TIME: AtomicU64 = AtomicU64::new(0);

        struct TestSource;

        impl TimeSource for TestSource {
            fn now(&self) -> Option<Duration> {
                Some(Duration::from_nanos(TEST_TIME.load(Ordering::Relaxed)))
            }
        }

        static SOURCE: TestSource = TestSource;

        let _suite_guard = super::acquire_limits_test_lock();

        let mut slot = super::TIME_SOURCE_OVERRIDE.lock();
        let previous = (*slot).replace(&SOURCE);
        drop(slot);

        TEST_TIME.store(123_000_000, Ordering::Relaxed);
        assert_eq!(monotonic_now(), Some(Duration::from_nanos(123_000_000)));

        let mut slot = super::TIME_SOURCE_OVERRIDE.lock();
        *slot = previous;
    }
}
