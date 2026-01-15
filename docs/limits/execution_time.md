# Execution Time Limiting Design

## Goal

Introduce configurable execution-time limits so every evaluation stays bounded.
Policy service can configure these limits to ensure that a single runaway policy never degrades overall availability.

## Design Goals

- Support execution limits per engine. Also support configuring a global fallback execution limit.
- Use best time sources automatically in std builds but provide ability to set the time source in no-std builds and for deterministic testing.
- Since computing elapsed time is relatively expensive, provide ability to control how often it is computed during evaluation.

## Approaches

The following approaches are used by various execution engines.

### Cooperative Tick Budgets
Evaluations burn through a configurable “fuel” counter one work unit at a time.
When fuel hits zero the engine raises an error, forcing callers to top up or abandon the run.
- **Examples**: Wasmtime fuel, Wasmer metering, Lua debug hooks
- **Pros**: Precise control over work units; compatible with no_std targets
- **Cons**: Requires instrumentation at every checkpoint; budget choice affects responsiveness

### Wall-Clock Watchdogs
Hosts schedule a real-time deadline alongside the policy evaluation.
When a timer fires, the engine aborts or interrupts, guaranteeing a hard wall-clock cap.
- **Examples**: V8 termination handler, SpiderMonkey interrupt callback, PostgreSQL statement_timeout
- **Pros**: Tracks real elapsed time; easy to reason about deadlines
- **Cons**: Needs host timers or threads; harder to support in no_std environments, and Rust threads cannot be force-cancelled so watchdogs must coordinate cooperative shutdown

### Scheduler Time-Slicing
Policies run inside a cooperative scheduler that yields after fixed work slices.
The host can deprioritize or cancel long tasks while allowing others to continue.
- **Examples**: Erlang BEAM reductions, .NET ThreadPool throttling
- **Pros**: Isolates runaway workloads by design; integrates with host schedulers
- **Cons**: Significant state bookkeeping; higher overhead for frequent yields, and feasible for VM control loops but practically impossible for the interpreter without a deep rewrite



## Configuration Model

### ExecutionTimerConfig

`ExecutionTimerConfig` lives in `utils::limits::time` and contains:

- `limit: Option<Duration>` — optional wall-clock deadline (None disables checks).
- `check_interval: NonZeroU32` — number of work units between timer checks.

### Work Units

The timer does not prescribe what constitutes a single “work unit.” Instead, each caller chooses a
granularity that matches its execution model:

- The interpreter treats each scheduling step (e.g., evaluating a single statement or expression in
   a rule) as a unit.
- The VM typically reports one instruction per unit.

This abstraction keeps the timer flexible while still guaranteeing that, regardless of the unit
definition, the timer observes elapsed wall-clock time at predictable checkpoints controlled by
`check_interval`.

The struct defaults to `limit = None` and `check_interval = 1`, providing the minimal instrumentation when limits are turned on. Consumers can choose larger intervals to amortize the cost of frequent checks.

### Global Fallback vs Engine Overrides

- `set_global_execution_timer_config` installs a process-wide fallback stored behind a spin mutex. Engines without an explicit override consult this value before every evaluation.
- Each engine holds an optional `execution_timer_config`. When `Engine::set_execution_timer_config` is invoked, the engine stores the provided configuration and applies it to the interpreter immediately. Clearing the override via `Engine::clear_execution_timer_config` restores reliance on the global fallback.
- Engines default to no time limit. Newly created engines apply the effective configuration (engine override or global fallback or default) during construction so that any first evaluation honors the expected budget.

### Effective Configuration Lifecycle

Before any evaluation entry point (query, rule, compilation), the engine:

1. Computes the effective configuration via `execution_timer_config.or_else(global_execution_timer_config).unwrap_or_default()`.
2. Applies it to the interpreter using `apply_effective_execution_timer_config`, which resets the timer to ensure a fresh window.
3. Proceeds with evaluation, relying on interpreter checkpoints to enforce the deadline.

This approach guarantees that changing the global fallback impacts both new and existing engines on their next evaluation, while engine overrides remain isolated.

## ExecutionTimer Behavior

`ExecutionTimer` maintains four fields:

- `config`: the active `ExecutionTimerConfig`.
- `start`: optional start instant.
- `accumulated_units`: tracks work units until the next check.
- `last_elapsed`: caches the most recent elapsed duration.

### Key Operations

- `start(now)` records the baseline instant and clears accumulated counters.
- `tick(work_units, now)` increments the accumulator and triggers `check_now` when the accumulator reaches `check_interval`. If `limit` is `None`, the function returns early with `Ok(())`.
- `check_now(now)` computes elapsed time, updates `last_elapsed`, and returns `LimitError::TimeLimitExceeded` when elapsed > limit.
- `elapsed(now)` reports elapsed time without mutating state, enabling diagnostics and tests.

Because ticks only perform the expensive comparison after the configured interval, callers can tune `check_interval` to their workloads.

## Time Sources

To avoid direct dependencies on `Instant`, the timer expects callers to supply a monotonic `Duration` via `monotonic_now()` or custom sources.

- On `std` builds, `StdTimeSource` captures a single `Instant` per process (via `OnceLock`) and reports elapsed durations. This keeps time monotonic and stable across threads.
- Tests and `no_std` builds can install overrides through `set_time_source`, which stores an `&'static dyn TimeSource` in a spin mutex. YAML tests use this hook to provide deterministic timestamps, ensuring repeatable limit violations.

If no source is available (e.g., `no_std` without an override), `monotonic_now` returns `None`; the interpreter treats this as “time limiting unavailable,” effectively disabling checks.

## Interpreter Integration

The interpreter carries an `ExecutionTimer`. Evaluation steps integrate with the timer as follows:

1. `prepare_for_eval` applies the effective configuration and calls `reset` on internal state.
2. At key checkpoints (rule scheduling, loop iterations, query evaluation steps) the interpreter:
   - Calls `monotonic_now` to fetch the current time (when available).
   - Invokes `tick(1, now)` to check for limit violations.
3. When `LimitError::TimeLimitExceeded` is returned, the interpreter converts it into an error surface consistent with existing APIs (e.g., `anyhow::Error` on Rust, host-specific exceptions on bindings).

Because the interpreter amortizes clock reads via `check_interval`, the overhead remains low even with many evaluation steps.

## Compiled Policy Integration

Compiled policies (VM paths) share the interpreter’s timer via `apply_effective_execution_timer_config`. Before VM execution begins, the engine ensures the VM’s interpreter state reflects the current timer configuration and resets any per-evaluation state.

- VM loops call `tick` with the number of instructions executed since the last check (commonly `1`).
- Helper functions responsible for longer-running host interactions (e.g., print gathering) may call `check_now` to enforce the deadline before crossing the FFI boundary.

This shared timer model avoids duplicate configuration state and maintains consistent semantics across evaluation modes.

## Public API Surface

The design exposes these primary methods:

- `Engine::set_execution_timer_config(config: ExecutionTimerConfig)` stores a per-engine override and reapplies it immediately, ensuring the next evaluation enforces the new limits.
- `Engine::clear_execution_timer_config()` removes the override and reverts to the global fallback.
- `set_global_execution_timer_config(config: Option<ExecutionTimerConfig>)` installs an optional global default. Passing `None` clears the fallback.
- `global_execution_timer_config() -> Option<ExecutionTimerConfig>` returns the currently active global fallback for diagnostics.

Documentation highlights that engines default to no time limit, global settings provide a quick way to protect all engines, and overrides preempt the global value until cleared.

## Testing Strategy

- **Unit Tests** in `utils::limits::time` verify configuration defaults, `tick` behavior, limit enforcement, and custom time sources.
- **Integration Tests (YAML)** configure deterministic time sources and assert that engine-level and global configurations interact correctly (override precedence, clearing behavior, fresh windows per evaluation).
- **Binding Tests** (planned) will demonstrate that FFI surfaces propagate timer errors.

Each test resets global configuration and time sources via RAII guards to avoid cross-test interference.

## Operational Guidance

- Choose conservative `check_interval` values (e.g., 1–10) for latency-sensitive workloads to catch runaway loops quickly. Larger intervals reduce overhead but increase the window between checks.
- When applying global limits in multi-tenant services, consider setting per-engine overrides for trusted workloads that need higher budgets.
- Combine with monitoring of `last_elapsed` to understand how close evaluations come to their deadlines.

## Future Work

- Expose per-evaluation overrides (e.g., request-scoped budgets) to complement global and engine-level configuration.
- Surface telemetry events whenever limits are hit, providing elapsed time at breach for observability pipelines.
- Investigate dynamic adjustment of `check_interval` based on observed evaluation patterns to balance overhead and responsiveness.
