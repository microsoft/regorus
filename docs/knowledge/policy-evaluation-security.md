<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Policy Evaluation Security

Deep knowledge about security properties, DoS protection, resource limits,
and input validation in regorus. Read this before modifying evaluation paths,
parsers, or resource management.

## Threat Model

Regorus evaluates **untrusted policy code** against **untrusted data**. Both
may be adversarial. The engine must:

1. **Always terminate** — no infinite loops, no unbounded recursion
2. **Bound resource usage** — memory, CPU time, instruction count
3. **Return correct results** — a wrong result is a security vulnerability
4. **Never crash** — panics in daemon mode crash the service
5. **Not leak information** — error messages must not expose sensitive data

## Resource Limit Enforcement

### Instruction Budget (RVM)

The primary defense against computation-based DoS:

- **Default**: 25,000 instructions (`src/rvm/vm/machine.rs`)
- **Enforcement**: checked every iteration in the execution loop
- **Error**: `VmError::InstructionLimitExceeded`
- **Configurable**: `set_max_instructions(limit)`

### Execution Time Limits

Wall-clock enforcement via `ExecutionTimer` (`src/utils/limits/time.rs`):

- **Cooperative checking** — the timer is checked periodically, not preemptively
- **Amortized overhead** — accumulates work units before reading the clock
  to avoid syscall overhead
- **Suspended time excluded** — `resume_from_elapsed()` preserves elapsed time
  across VM suspensions, so only active computation counts
- **Per-instance override** — each VM can set its own timer config
- **Error**: `VmError::TimeLimitExceeded`

### Memory Limits

Global memory tracking via `src/utils/limits/memory.rs`:

- **Global atomic limit** — `GLOBAL_MEMORY_LIMIT: AtomicU64`
- **Throttled checking** — dual strategy to avoid contention:
  - Stride-based: check every 16 iterations
  - Delta-based: check when 32 KiB has been allocated since last check
- **Per-thread flushing** — auto-flush at 1 MiB threshold
- **Enforcement points**: Value construction, deserialization, parsing
- **Error**: `VmError::MemoryLimitExceeded`

The `allocator-memory-limits` feature uses mimalloc to enforce at the allocator
level.

## Input Validation

### Policy Source (`src/lexer.rs`)

Rego source is validated during lexing with configurable limits:

| Limit | Default | Purpose |
|-------|---------|---------|
| `max_col` | 1,024 chars | Lines exceeding this are likely minified/attack code |
| `max_file_bytes` | 1 MiB | Prevents memory exhaustion from huge files |
| `max_lines` | 20,000 | Prevents excessive parsing time |

Memory limit is also checked after each logical chunk during lexing.

### Parser Depth

The parser enforces expression nesting depth:

- **Default**: `MAX_EXPR_DEPTH = 32` (`src/parser.rs`)
- Prevents stack overflow from deeply nested expressions like `(((((...)))))`
- Returns error, not panic

### JSON/YAML Data

Data added via `add_data()` must be an object (checked by `engine.rs`).
Value construction during deserialization checks memory limits at each node.

### RVM Programs

Compiled programs validated by `validate_limits()` (`src/rvm/program/core.rs`):

| Resource | Limit |
|----------|-------|
| Instructions | 65,535 |
| Literals | 65,535 |
| Rules | 4,000 |
| Entry points | 1,000 |
| Source files | 256 |
| Builtins | 512 |
| Path depth | 32 |

These prevent adversarial serialized programs from consuming excessive resources
during deserialization or execution.

## Recursion Protection

- **Parser**: `MAX_EXPR_DEPTH = 32` for expression nesting
- **RVM**: `MAX_PATH_DEPTH = 32` for rule path depth
- **Virtual documents**: `needs_runtime_recursion_check` flag enables detection
  when `VirtualDataDocumentLookup` instructions are present
- **Rule evaluation**: processed rules tracked in `self.processed` set to
  prevent re-evaluation cycles

## DoS via Regular Expressions

Regorus uses the `regex` crate which compiles to a DFA — **no catastrophic
backtracking**. Protection is layered:

1. DFA-based regex engine (no exponential blowup)
2. Instruction budget limits total work
3. Execution time limits bound wall-clock
4. LRU cache prevents repeated compilation (256 patterns, hard cap 2^16)

## Undefined vs False

**This is a security-critical distinction.** In policy evaluation:

```rego
allow { input.role == "admin" }
```

If `input.role` is missing:
- `input.role == "admin"` → `Undefined` (not `false`)
- `allow` → `Undefined` (rule body didn't succeed)
- `not allow` → `true` (because `not Undefined = true`)

A bug that treats `Undefined` as `false` (or vice versa) can change policy
decisions. Every evaluation path must handle the three-valued logic correctly.

See `docs/knowledge/value-semantics.md` for detailed Undefined propagation rules.

## Supply Chain Security

### Dependency Auditing

The `dependency-audit.yml` workflow runs:
- **cargo-audit**: checks 6 Cargo.lock files (main + 5 bindings) against
  RustSec advisories
- **cargo-deny**: checks 9 manifests for CVEs (advisories) and problematic
  dependencies (bans)
- **Schedule**: PRs, main pushes, weekly (Mondays 6 AM), manual dispatch

### Dependency Management

- **Pinned action SHAs**: most GitHub Actions references use full commit SHAs
  rather than mutable tags — prevents supply chain attacks via tag mutation.
  Some workflows (e.g., `dependency-audit.yml`, `miri.yml`) still use tag-based
  refs; prefer SHA pins when adding or updating action references
- **Locked dependencies**: `Cargo.lock` committed, `cargo fetch --locked` /
  `--frozen` in CI ensures reproducible builds
- **Dependabot**: automated weekly updates for Cargo, GitHub Actions, Maven,
  NuGet, pip, npm, bundler, Go
- **Minimal dependency surface**: prefer `core`/`alloc` over external crates

### Spectre Mitigation

On Windows (MSVC), the optional `msvc_spectre_libs` dependency links with
Spectre-mitigated CRT and libraries.

## Panic Safety

The 80+ deny lints in `src/lib.rs` exist not just for style — they prevent
panics at compile time:

| Denied | Why |
|--------|-----|
| `clippy::unwrap_used` | `.unwrap()` panics on `None`/`Err` |
| `clippy::expect_used` | `.expect()` panics on `None`/`Err` |
| `clippy::indexing_slicing` | `vec[i]` panics on out-of-bounds |
| `clippy::arithmetic_side_effects` | `a + b` can overflow and panic |
| `clippy::panic` | Explicit `panic!()` |
| `clippy::unreachable` | Explicit `unreachable!()` |
| `clippy::todo` | Explicit `todo!()` |

In daemon mode, **any panic is a service crash**. The deny lints are the first
line of defense. The FFI layer's `with_unwind_guard()` is the second — it
catches panics and poisons the engine (see `docs/knowledge/ffi-boundary.md`).

But panic containment is a last resort. The goal is zero panics in all code
paths, including error paths, resource exhaustion, and adversarial input.

## Security Review Checklist

When reviewing code for security:

1. **Undefined handling** — does the code correctly distinguish Undefined from false?
2. **Resource limits** — does new code respect instruction budget, time, memory?
3. **Input validation** — is untrusted input validated before use?
4. **Panic paths** — can any code path panic (overflow, indexing, unwrap)?
5. **Error messages** — do errors avoid leaking policy content or data?
6. **Recursion** — is recursion bounded?
7. **Allocation** — can adversarial input cause unbounded allocation?
8. **Cache behavior** — can cache be poisoned or exhausted?
