# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

- [**breaking**] Append the required `arg_count` field to `RegorusHostAwaitBuiltin`. Non-empty registrations using the old name-only layout now fail ABI size validation; larger aligned caller strides remain supported.

### Added

- Compile dynamic RVM defaults as runtime fallback entry points for complete rules and functions. Default expressions execute only after ordinary definitions and `else` branches do not produce a value, and may suspend on registered HostAwait calls in suspendable mode or consume configured responses in run-to-completion mode.
- Support indexed RVM defaults as missing-key object merges while preserving ordinary object values. Programs containing runtime or indexed defaults use binary version 7 and versioned JSON.
- Preserve artifact compatibility for programs without runtime or indexed defaults: they continue to serialize as binary version 6 and legacy flat JSON. Programs containing runtime or indexed defaults serialize as binary version 7 and versioned JSON; recompile policy source with a version-7-capable runtime to produce artifacts that include runtime-default behavior.
- Extend per-VM memory budgets configured through `regorus_rvm_set_memory_budget_config` to
  suspendable RVM executions. One requested-byte account and its initial budget span all resumes;
  the account is retained for the execution lifetime and cleared on completion, terminal failure,
  or abandonment. Native resume JSON parsing plus immediate result JSON/C-string production are
  included, and malformed JSON syntax/EOF remains retryable without changing the active budget.
  Run-to-completion thread-baseline behavior is unchanged. Status 10 reports budget exhaustion;
  status 11 remains reserved. Existing C ABI signatures, C# budget APIs, and
  `RegorusMemoryBudgetExceededException` mapping remain unchanged.

## [0.1.0](https://github.com/microsoft/regorus/releases/tag/regorus-ffi-v0.1.0) - 2024-02-08

### Other
- C++ binding ([#129](https://github.com/microsoft/regorus/pull/129))
- Bindings for C, C#, Golang ([#124](https://github.com/microsoft/regorus/pull/124))
