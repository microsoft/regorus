# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

- [**breaking**] Append the required `arg_count` field to `RegorusHostAwaitBuiltin`. Non-empty registrations using the old name-only layout now fail ABI size validation; larger aligned caller strides remain supported.

### Added

- Extend per-VM memory budgets configured through `regorus_rvm_set_memory_budget_config` to
  suspendable RVM executions. One requested-byte account and its initial budget span all resumes;
  the account is retained for the execution lifetime and cleared on completion, terminal failure,
  or abandonment. Native resume JSON parsing plus immediate result JSON/C-string production are
  included, and malformed JSON syntax/EOF remains retryable without changing the active budget.
  Run-to-completion thread-baseline behavior is unchanged. Status 10 reports budget exhaustion;
  status 11 remains reserved. Existing C ABI signatures, C# budget APIs, and
  `RegorusMemoryBudgetExceededException` mapping remain unchanged.

### Fixed

- Concurrent FFI calls no longer race on the process-global panic hook. The first guarded call
  installs one hook that records panic details for guarded calls and forwards all other panics to
  the hook installed before it, instead of swapping the hook on every call, which could drop panic
  details or leave a stale hook installed in place of the host's hook. The hook is never removed:
  if other Rust code shares this library's copy of std (for example when both link std
  dynamically), don't unload the library after its first call.

## [0.1.0](https://github.com/microsoft/regorus/releases/tag/regorus-ffi-v0.1.0) - 2024-02-08

### Other
- C++ binding ([#129](https://github.com/microsoft/regorus/pull/129))
- Bindings for C, C#, Golang ([#124](https://github.com/microsoft/regorus/pull/124))
