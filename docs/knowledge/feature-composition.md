<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Feature Composition

Deep knowledge about regorus's feature flag system and the risks of
non-default feature combinations. Read this before adding features or
modifying feature-gated code.

## Feature Architecture

### Default Features

```toml
default = ["full-opa", "arc", "rvm"]
```

- **`full-opa`**: All OPA-compatible builtins. Implies `std`.
- **`arc`**: `Arc` instead of `Rc` for thread safety.
- **`rvm`**: Rego Virtual Machine compilation and execution.

### Composite Features

**`full-opa`** includes: base64, base64url, coverage, glob, graph, hex, http,
jsonschema, net, opa-runtime, regex, cache, semver, std, time, uuid, urlquery,
yaml.

**`opa-no-std`** includes: arc, base64, base64url, coverage, graph, hex,
no_std, opa-runtime, regex, semver, lazy_static/spin_no_std. Note this
**excludes** builtins that require `std` (glob, time, jsonschema, yaml, etc).

### The no_std / std Boundary

The crate is `#![no_std]` by default with `extern crate alloc`.

- **`std`** feature: enables `std` library, parking_lot, filesystem, threading
- **`no_std`** feature: enables `lazy_static/spin_no_std` for spinlock-based lazy statics

**These are NOT mutually exclusive in Cargo.** If both are enabled, `std` wins.
But `no_std` should be tested alone:

```bash
cargo xtask test-no-std  # Builds for thumbv7m-none-eabi
```

### The arc Feature

Controls whether shared data uses `Rc` or `Arc`:

```rust
// In src/lib.rs (conditional type alias)
#[cfg(feature = "arc")]
type Rc<T> = alloc::sync::Arc<T>;
#[cfg(not(feature = "arc"))]
type Rc<T> = alloc::rc::Rc<T>;
```

**`arc` is default.** Disabling it gives single-threaded performance but breaks
thread safety. The FFI crate's contention detection (`contention_checks`)
requires `arc`.

## Known Pitfalls

### Issue #595 Pattern

Feature combinations that compile individually may fail together. Example:
a feature adds a dependency that conflicts with `no_std`, or a feature-gated
module uses `std` types without a feature gate.

**Prevention:**
- Always test with `--no-default-features` plus minimal feature sets
- CI checks key combinations explicitly

### Compilation Verification Matrix

When adding or modifying features, verify these combinations compile:

```bash
# Minimal (no_std, no arc, no rvm)
cargo check --no-default-features

# no_std with arc
cargo check --no-default-features --features arc,opa-no-std

# std with arc and rvm (common production config)
cargo check --no-default-features --features std,arc,rvm

# Everything
cargo check --all-features

# The full CI suite checks more combinations
cargo xtask ci-debug
```

### Feature-Gated Code Correctness

Common mistakes:

**1. Using std types without gate:**
```rust
// ✗ Bad — breaks no_std
use std::collections::HashMap;

// ✓ Good — available in no_std via alloc
use alloc::collections::BTreeMap;

// ✓ Good — gated when std is required
#[cfg(feature = "std")]
use std::path::Path;
```

**2. Feature implies another but not declared:**
```rust
// ✗ Bad — regex module uses std but doesn't declare dependency
[features]
regex = ["dep:regex"]  # regex crate needs std!

// ✓ Good — declare the implication
regex = ["dep:regex"]  # regex default-features=false works in no_std
```

**3. Conditional compilation in wrong direction:**
```rust
// ✗ Bad — dead code when feature absent, no compile error
#[cfg(feature = "myfeature")]
fn helper() { ... }

fn caller() {
    helper();  // ERROR: `helper` doesn't exist without myfeature
}

// ✓ Good — gate the caller too
#[cfg(feature = "myfeature")]
fn caller() {
    helper();
}
```

### docsrs Annotation

Public feature-gated APIs must have the docsrs annotation so docs.rs shows
which feature is required:

```rust
#[cfg(feature = "myfeature")]
#[cfg_attr(docsrs, doc(cfg(feature = "myfeature")))]
pub fn my_function() -> Result<()> { .. }
```

## Adding a New Feature: Checklist

1. Add to `[features]` in `Cargo.toml` with optional dependency
2. Gate the module: `#[cfg(feature = "myfeature")] mod myfeature;`
3. Gate registration (builtins, languages, etc.)
4. Gate public API with docsrs annotation
5. Add to `full-opa` if it's an OPA-standard feature
6. Add to `opa-no-std` if it works without std
7. Verify compilation with the matrix above
8. Run `cargo xtask ci-debug` for the full suite
9. Consider adding the combination to CI if it's a common configuration

## Dependencies and no_std

When adding dependencies:
- Check if the crate supports `no_std` (look for `default-features = false`)
- Use `default-features = false` and enable only needed features
- If the crate requires `std`, the feature must imply `std`
- Prefer `core`/`alloc` over external crates where feasible

Current dependency pattern:
```toml
serde = { version = "1.0", default-features = false, features = ["derive", "rc", "alloc"] }
regex = { version = "1.12", optional = true, default-features = false }
```

## The Rc Type Alias

The crate defines a type alias `Rc` that maps to either `alloc::rc::Rc` or
`alloc::sync::Arc` based on the `arc` feature. This alias is used throughout
the codebase — in `Value`, `Number`, and everywhere shared ownership is needed.

**Never use `alloc::rc::Rc` or `alloc::sync::Arc` directly in the core crate.**
Always use the type alias `Rc` to ensure the `arc` feature works correctly.
