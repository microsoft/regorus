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
- 9 language bindings: C, C (no_std), C++, C#, Go, Java, Python, Ruby, WASM (via `bindings/ffi/`)
- Core crate: `#![no_std]` + `extern crate alloc`; `#![forbid(unsafe_code)]`
  (default Cargo features include `std` — the crate is no_std-*capable*, not no_std-only)
- Two execution paths: tree-walking interpreter and **RVM** (bytecode VM)
- ~53 deny lints in `src/lib.rs` — restricts panics, unchecked indexing, and unchecked arithmetic
  (some modules like `value.rs` locally `#![allow(...)]` specific lints for performance)

**Strategic direction** (aspirational — not all implemented yet):
- **RVM is the preferred execution path** — new optimization work focuses there;
  interpreter remains fully supported and is the default today
- **Error migration** — `anyhow` → `thiserror` strongly typed errors (RVM leads)
- **Formal verification** — Miri (active CI), Z3 and Verus (planned)
- **Multi-policy-language** — extensible via `src/languages/`

## Key Invariants

These are the most important rules that are not obvious from the code alone:

- **Undefined ≠ false** — Rego uses three-valued logic. Undefined propagates
  silently; forgetting this causes wrong allow/deny decisions.
- **Panics in FFI = permanent poisoning** — the engine uses `with_unwind_guard()`
  and a process-global poisoned flag. Any panic across FFI makes *all* engine
  instances in the process permanently unusable.
- **Dual execution paths** — interpreter (tree-walking) and RVM (bytecode VM)
  must produce identical results for all inputs. Both must be tested.
  (Exception: some language extensions like Azure RBAC are interpreter-only.)
- **Resource limits** — `enforce_limit()` must be called in accumulation loops
  to bound memory/CPU from adversarial policies.
- **Error migration** — new modules use `thiserror` enums; existing modules use
  `anyhow`. Don't mix within a module.
- **Feature gating** — new public modules need `#[cfg(feature = "...")]` gates.
  Verify builds with `--all-features` and `--no-default-features`.

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

**no_std discipline** (applies to `src/` core crate) — `use core::` and `alloc::`
by default. Only `std::` behind `#[cfg(feature = "std")]`.

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
cargo test --test opa --features opa-testutil  # OPA conformance
```

Git hooks auto-installed by `build.rs`: pre-commit (build+format+clippy),
pre-push (+ doc tests + no_std + OPA conformance).

## Repository Layout

```
src/                    Core library (no_std, forbid(unsafe_code))
  rvm/                  Rego Virtual Machine ← strategic focus
  languages/            Policy language extensions
  builtins/             Builtin functions (~23 modules)
  value.rs              Value type (Null, Bool, Number, String, Array, Set, Object, Undefined)
  interpreter.rs        Tree-walking interpreter
  engine.rs             Engine API (public surface also includes lib.rs re-exports)
bindings/               9 language bindings + ffi layer (c/, c-nostd/, cpp/, csharp/, go/, java/, python/, ruby/, wasm/)
tests/                  Integration, conformance, domain-specific tests
docs/                   Grammar, builtins, RVM docs
xtask/                  Development automation CLI
benches/                Criterion benchmarks
```

## Supply Chain Security

- `dependency-audit.yml` — cargo-audit + cargo-deny across all Cargo.lock files
- Dependabot — weekly updates for Cargo, Actions, Maven, NuGet, pip, bundler, Go
- New GitHub Actions references use pinned commit SHAs where possible
- `cargo fetch --locked` in CI for reproducible builds

## When Making Changes

1. **Consider all 9 binding targets** — API changes affect every language
2. **Both execution paths** — features must work in interpreter AND RVM
3. **Test Undefined propagation** — `Undefined ≠ false`, test both paths
4. **Run `cargo xtask ci-debug`** before submitting
5. **Update docs** — `docs/builtins.md`, `docs/rvm/` as needed
