<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Regorus — Copilot Instructions

> If these instructions conflict with the actual codebase, the code is the
> source of truth. Flag any discrepancy you notice.

## Identity

Regorus is a **multi-policy-language evaluation engine** written in Rust. Its
primary language is [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
(Open Policy Agent), with extensible support for additional policy languages via
`src/languages/`. It is used in **production at scale** where **correctness is
security-critical** — a bug in policy evaluation can mean `allow` when the
answer should be `deny`.

**Key properties:**
- 10 language targets: Rust (core), C, C (no_std), C++, C#, Go, Java, Python, Ruby, WASM
- `#![no_std]` by default (`extern crate alloc`), `#![forbid(unsafe_code)]`
- Two execution paths: tree-walking interpreter and **RVM** (bytecode VM)
- 80+ deny lints in `src/lib.rs` — restricts panics, unchecked indexing, and unchecked arithmetic
  (some modules like `value.rs` locally `#![allow(...)]` specific lints for performance)

**Strategic direction:**
- **RVM is the strategic execution path** — new optimization work focuses there
- **Isolated / daemon execution** — long-lived process, clean resource lifecycle
- **Error migration** — `anyhow` → `thiserror` strongly typed errors (RVM leads)
- **Formal verification** — Miri (active CI), Z3 and Verus (planned)
- **Multi-policy-language** — extensible via `src/languages/`, don't disclose specifics

## Deep Knowledge

For complex subsystems, read the knowledge files in `docs/knowledge/` before
making changes. These capture invariants, edge cases, and institutional
knowledge that isn't obvious from the code alone:

| File | Covers |
|------|--------|
| `value-semantics.md` | Value type, Undefined propagation, three-valued logic |
| `rvm-architecture.md` | VM execution modes, frame stack, serialization, register pooling |
| `builtin-system.md` | Builtin registration, feature gating, OPA conformance |
| `ffi-boundary.md` | Safety across 9 bindings, handles, panic containment, poisoning |
| `feature-composition.md` | Feature flag interactions, no_std boundary, testing matrix |
| `error-handling-migration.md` | anyhow → thiserror migration strategy, VmError pattern |
| `policy-evaluation-security.md` | DoS protection, resource limits, input validation |
| `rego-semantics.md` | Evaluation model, undefined propagation, backtracking, `with` |
| `interpreter-architecture.md` | Context stack, scope management, rule lifecycle |
| `compilation-pipeline.md` | Scheduler, loop hoisting, destructuring planner |
| `azure-policy-language.md` | Azure Policy evaluation model, effects, alias normalization |
| `azure-rbac-language.md` | RBAC condition interpreter, ABAC builtins, context model |
| `engine-api.md` | Public API surface, add_policy → compile → eval flow |
| `time-builtins-compat.md` | Go time.Parse compatibility, timezone handling |
| `language-extension-guide.md` | Adding new policy languages, LSP/tooling vision |
| `tooling-architecture.md` | Language server, linter, analyzer design patterns |
| `causality-and-partial-eval.md` | Causality tracking and partial evaluation design |
| `rego-compiler.md` | Worklist algorithm, expression codegen, register allocation |
| `azure-policy-aliases.md` | Alias registry, ARM normalization/denormalization pipeline |
| `telemetry-and-diagnostics.md` | Error traceability, structured diagnostics, cloud-scale telemetry |
| `workflow-security.md` | GitHub Actions security patterns, expression injection, token handling |

Also see `docs/rvm/architecture.md`, `docs/rvm/instruction-set.md`,
`docs/rvm/vm-runtime.md` for RVM internals.

## Essential Coding Rules

**No panics — ever** (deny lints enforce this):
```rust
// Use typed errors for new code
let v = map.get("key").ok_or(MyError::MissingKey("key"))?;
// Or anyhow in existing modules
let v = map.get("key").ok_or_else(|| anyhow!("missing key"))?;
```

**Prefer safe indexing** — use `.get()` + `?` or iterate where possible.
`clippy::indexing_slicing` is denied crate-wide but locally allowed in some
performance-critical modules (e.g., `value.rs`).

**No unchecked arithmetic** — use `checked_add()`, `saturating_add()`, etc.

**no_std discipline** — `use core::` and `alloc::` by default. Only `std::`
behind `#[cfg(feature = "std")]`.

**Unsafe forbidden** — `#![forbid(unsafe_code)]` in the core crate. Only FFI
binding crates may use unsafe.

**Error handling** — new modules: `thiserror` enums (see `src/rvm/vm/errors.rs`).
Existing modules: `anyhow` is acceptable for consistency within the module.

**Feature gating** — gate modules, registrations, and public API. Add `docsrs`
annotation. Verify non-default combinations compile.

## Build & Test

```bash
cargo xtask ci-debug          # Full debug CI suite
cargo xtask ci-release        # Full release CI suite (superset)
cargo xtask test-all-bindings # All 9 language binding smoke tests
cargo xtask test-no-std       # Verify no_std builds (thumbv7m-none-eabi)
cargo xtask fmt               # Format workspace + bindings
cargo xtask clippy            # Lint workspace + bindings
cargo test --test opa         # OPA conformance (needs opa-testutil feature)
```

Git hooks auto-installed by `build.rs`: pre-commit (build+format+clippy),
pre-push (+ doc tests + no_std + OPA conformance).

## Repository Layout

```
src/                    Core library (no_std, forbid(unsafe_code))
  rvm/                  Rego Virtual Machine ← strategic focus
  languages/            Policy language extensions
  builtins/             Builtin functions (~19 modules)
  value.rs              Value type (Null, Bool, Number, String, Array, Set, Object, Undefined)
  interpreter.rs        Tree-walking interpreter (legacy path)
  engine.rs             Public API
bindings/               9 language bindings + ffi layer (c/, c-nostd/, cpp/, csharp/, go/, java/, python/, ruby/, wasm/)
tests/                  Integration, conformance, domain-specific tests
docs/                   Grammar, builtins, RVM docs, knowledge base
xtask/                  Development automation CLI
benches/                Criterion benchmarks
```

## Supply Chain Security

- `dependency-audit.yml` — cargo-audit + cargo-deny across all Cargo.lock files
- Dependabot — weekly updates for Cargo, Actions, Maven, NuGet, pip, npm, bundler, Go
- New GitHub Actions references added in this config use pinned commit SHAs
- `cargo fetch --locked` / `--frozen` in CI for reproducible builds

## When Making Changes

1. **Read relevant knowledge files** in `docs/knowledge/` first
2. **Consider all 9 binding targets** — API changes affect every language
3. **Both execution paths** — features must work in interpreter AND RVM
4. **Test Undefined propagation** — `Undefined ≠ false`, test both paths
5. **Run `cargo xtask ci-debug`** before submitting
6. **Update docs** — `docs/builtins.md`, `docs/rvm/`, knowledge files as needed
