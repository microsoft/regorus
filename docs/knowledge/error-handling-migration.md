<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Error Handling Migration

Deep knowledge about regorus's error handling patterns and the ongoing
migration from `anyhow` to `thiserror`. Read this before adding error
handling to new code or modifying existing error paths.

## Current State

The codebase has two error handling approaches coexisting:

### Legacy: anyhow (widespread)

Most of the codebase uses `anyhow::Result` with `bail!()` and `anyhow!()`:

```rust
use anyhow::{anyhow, bail, Result};

fn eval_something(&mut self) -> Result<Value> {
    let v = map.get("key").ok_or_else(|| anyhow!("missing key"))?;
    if condition_fails {
        bail!("evaluation failed: {reason}");
    }
    Ok(value)
}
```

Found in: `src/interpreter.rs`, `src/engine.rs`, `src/parser.rs`,
`src/lexer.rs`, `src/value.rs`, `src/number.rs`, `src/builtins/`, and most
other modules.

### Target: thiserror (RVM leads)

The RVM uses strongly typed error enums:

```rust
use thiserror::Error;

#[derive(Error, Debug, Clone, PartialEq)]
pub enum VmError {
    #[error("Execution stopped: exceeded maximum instruction limit of {limit} after {executed} instructions (pc={pc})")]
    InstructionLimitExceeded { limit: usize, executed: usize, pc: usize },

    #[error("Register index {index} out of bounds (pc={pc}, register_count={register_count})")]
    RegisterIndexOutOfBounds { index: u8, pc: usize, register_count: usize },

    // ... 30+ variants covering every VM error case
}

pub type Result<T> = core::result::Result<T, VmError>;
```

Found in: `src/rvm/vm/errors.rs`

## The VmError Pattern (Reference Implementation)

Key design principles visible in `VmError`:

**1. Every variant carries context:**
```rust
InstructionLimitExceeded { limit: usize, executed: usize, pc: usize }
```
Not just "limit exceeded" — includes the limit, actual count, and program counter.

**2. Program counter in every variant:**
```rust
// Every single variant includes `pc: usize`
RegisterNotObject { register: u8, value: Value, pc: usize },
LiteralIndexOutOfBounds { index: u16, pc: usize },
```
This is a debugging aid — every error can be traced to the exact instruction.

**3. Exhaustive coverage:**
30+ variants covering every known error case. No catch-all "Other(String)".

**4. Derives Clone and PartialEq:**
```rust
#[derive(Error, Debug, Clone, PartialEq)]
```
Clone enables error propagation without ownership transfer. PartialEq enables
testing error conditions precisely.

**5. Type alias for ergonomics:**
```rust
pub type Result<T> = core::result::Result<T, VmError>;
```

**6. Bridge from anyhow:**
```rust
impl From<anyhow::Error> for VmError {
    fn from(err: anyhow::Error) -> Self {
        VmError::ArithmeticError { message: format!("{}", err), pc: 0 }
    }
}
```
This allows the RVM to call into legacy code that returns `anyhow::Result`.

## Migration Strategy

### For New Code

**Always use thiserror.** Define a module-specific error enum:

```rust
use thiserror::Error;

#[derive(Error, Debug, Clone, PartialEq)]
pub enum MySubsystemError {
    #[error("invalid input: {0}")]
    InvalidInput(String),

    #[error("resource limit exceeded: {current} > {limit}")]
    ResourceLimitExceeded { current: usize, limit: usize },
}

pub type Result<T> = core::result::Result<T, MySubsystemError>;
```

### For Existing Code

When modifying existing functions that use `anyhow`:
- **Within the same module**: continue with `anyhow` for consistency
- **At module boundaries**: consider wrapping `anyhow::Error` in a typed variant
- **Incremental migration**: converting a whole module at once is better than
  mixing styles within a single module

### Bridge Pattern

When typed-error code calls anyhow code (or vice versa):

```rust
// Typed → anyhow (automatic via anyhow's From impl)
fn caller() -> anyhow::Result<Value> {
    typed_function()?;  // VmError auto-converts to anyhow::Error
    Ok(value)
}

// Anyhow → typed (explicit conversion needed)
fn caller() -> Result<Value, VmError> {
    anyhow_function().map_err(|e| VmError::Internal {
        message: format!("{}", e),
        pc: current_pc,
    })?;
    Ok(value)
}
```

## Error Message Guidelines

### For OPA Conformance

Builtin error messages **must match OPA exactly** — the conformance test suite
compares literally. When implementing builtins, check the OPA Go source.

### For Internal Errors

- Include enough context to diagnose without a debugger
- Include identifiers (register index, PC, rule name, etc.)
- Don't include sensitive data (user input, policy content)
- Use structured fields, not string formatting:

```rust
// ✗ Bad
#[error("register {0} out of bounds at pc {1}")]
RegisterOutOfBounds(u8, usize),

// ✓ Good — named fields are self-documenting
#[error("register index {index} out of bounds (pc={pc}, register_count={register_count})")]
RegisterIndexOutOfBounds { index: u8, pc: usize, register_count: usize },
```

## Panic Safety Connection

Error handling is the front line of panic safety. The deny lints forbid
`unwrap()`, `expect()`, `panic!()`, etc. Every fallible operation must return
`Result`. This is not just style — in daemon mode, a panic crashes the service.

The error migration makes this stronger: with typed errors, every failure mode
is enumerated and the compiler ensures all are handled. With `anyhow`, errors
are opaque and may be accidentally swallowed.

## no_std Compatibility

Both `anyhow` and `thiserror` support `no_std` with `default-features = false`:

```toml
anyhow = { version = "1.0", default-features = false }
thiserror = { version = "2.0", default-features = false }
```

Error types must use `alloc::string::String` instead of `std::string::String`
and avoid `std::io::Error` without a feature gate.
