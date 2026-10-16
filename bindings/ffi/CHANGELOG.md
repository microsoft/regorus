# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- Extend per-VM memory budgets configured through `regorus_rvm_set_memory_budget_config` to
  suspendable RVM executions. One requested-byte account and its initial budget span all resumes;
  the account outlives the VM while attributed blocks remain live. Native resume JSON parsing plus
  immediate result JSON/C-string production are included, and malformed JSON syntax/EOF remains
  retryable without changing the active budget. Run-to-completion thread-baseline behavior is
  unchanged. Status 10 reports budget exhaustion; status 11 remains reserved. Existing C ABI
  signatures, C# budget APIs, and `RegorusMemoryBudgetExceededException` mapping remain unchanged.

## [0.1.0](https://github.com/microsoft/regorus/releases/tag/regorus-ffi-v0.1.0) - 2024-02-08

### Other
- C++ binding ([#129](https://github.com/microsoft/regorus/pull/129))
- Bindings for C, C#, Golang ([#124](https://github.com/microsoft/regorus/pull/124))
