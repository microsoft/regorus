<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: RVM Architecture

Deep knowledge about the Rego Virtual Machine. Read this before modifying
anything in `src/rvm/`. Also see `docs/rvm/architecture.md`,
`docs/rvm/instruction-set.md`, and `docs/rvm/vm-runtime.md`.

## Overview

The RVM compiles Rego policies to register-based bytecode with fixed-width
32-bit instructions, then executes them in a virtual machine:

```
Policy source → Lexer → Parser → AST → Compiler → Program (bytecode) → VM → Value
```

This is the **strategic execution path** — new optimization and feature work
focuses on the RVM, not the tree-walking interpreter.

## Directory Structure

```
src/rvm/
  instructions/       Instruction definitions (fixed-width 32-bit opcodes)
  program/
    core.rs           Program struct — instructions, literals, entry points, rule info
    serialization/    Binary and JSON format implementations
    recompile.rs      Recompilation from partial programs
  vm/
    machine.rs        RegoVM — registers, stacks, execution state
    execution.rs      Run-to-completion and suspendable execution loops
    dispatch.rs       Instruction dispatch
    loops.rs          Loop iteration (Any, Every, ForEach modes)
    comprehension.rs  Set/array/object comprehension builders
    rules.rs          Rule evaluation, caching, call stacks
    virtual_data.rs   Virtual document lookup and caching
    state.rs          Register window pooling and state management
    errors.rs         VmError — strongly typed VM errors
  tests/              RVM-specific test suites
```

## Two Execution Modes

### Run-to-Completion

The VM executes instructions sequentially until the program completes or
errors. No suspension. This is the **fast path** for synchronous policy
evaluation. Most production use cases.

### Suspendable

The VM can suspend mid-execution and be resumed later:

| Reason | Use case |
|--------|----------|
| **HostAwait** | Program needs external data from the host |
| **Breakpoint** | Debugging support |
| **SingleStep** | Instruction-by-instruction execution |

The host calls `vm.resume(value)` to continue after suspension. The VM
preserves its entire execution state across suspend/resume cycles.

**Important:** `SuspendReason` variants that appear in run-to-completion mode
trigger `VmError::UnsupportedSuspendInRunToCompletion`.

## Frame Stack

The suspendable mode uses an explicit frame stack (`execution_stack`) with
frame kinds:

| Frame Kind | Purpose |
|------------|---------|
| **Main** | Top-level program execution |
| **Rule** | Rule body evaluation |
| **Loop** | Collection iteration (Any, Every, ForEach) |
| **Comprehension** | Set/array/object comprehension building |

Each frame tracks its own:
- Program counter (PC)
- Register window (base + count)
- Saved caller state (for restoration on frame pop)

Frames are pushed on entry and popped on completion. The frame stack is the
mechanism that makes suspension possible — the entire execution state is
captured in the stack.

## Register Window Pooling

The VM reuses register vectors to minimize allocation:

- **Pool**: `state.rs` manages a pool of `Vec<Value>` vectors
- **Window**: Each frame gets a register window (base offset + count)
- **Reuse**: When a frame pops, its register vector returns to the pool
- **Predictable**: Allocation pattern is bounded and deterministic

**Invariant:** New VM features MUST participate in register window pooling.
Do not allocate fresh Vecs for register storage.

## Instruction Budget

The VM enforces a configurable instruction limit to prevent unbounded execution:

- **Default**: 25,000 instructions (`machine.rs`)
- **Enforcement**: Checked in the execution loop (`execution.rs`)
- **Configurable**: `set_max_instructions(limit)` allows any `usize` value
- **Error**: `VmError::InstructionLimitExceeded` when exceeded

This is the primary defense against denial-of-service via crafted policies.
All new execution paths must respect this budget — do not add loops or
recursion that bypass the instruction counter.

## Program Serialization

Compiled programs can be serialized for distribution and cached execution.

### Binary Format (Primary)

Compact, fast deserialization. Used for production distribution of pre-compiled
policies. Implemented via the `postcard` crate.

### JSON Format (Debugging)

Human-readable. Useful for debugging, tooling, and inspection.

### Artifact Structure

The program has two sections:

**Stable section** (always serializable):
- Source files, entry points, metadata
- Rule information, builtin references
- Sufficient to recompile the execution section

**Execution section** (version-sensitive):
- Instructions, literals, parameter tables
- May fail to deserialize on format version mismatch

**Recompilation fallback**: If the execution section can't be deserialized
(e.g., after a regorus version upgrade), it can be recompiled from the stable
section. This is handled by `recompile.rs`.

### Program Limits

`validate_limits()` in `program/core.rs` enforces hard bounds:

| Resource | Limit |
|----------|-------|
| Instructions | 65,535 |
| Literals | 65,535 |
| Rules | 4,000 |
| Entry points | 1,000 |
| Source files | 256 |
| Builtins | 512 |
| Path depth | 32 |

These limits prevent adversarial programs from consuming excessive resources.

## VmError Pattern

The RVM uses strongly typed errors (`src/rvm/vm/errors.rs`):

```rust
#[derive(Error, Debug, Clone, PartialEq)]
pub enum VmError {
    #[error("Execution stopped: exceeded maximum instruction limit of {limit} ...")]
    InstructionLimitExceeded { limit: usize, executed: usize, pc: usize },
    // ... 30+ variants
}
```

Every error variant includes `pc` (program counter) for debugging. This is the
reference pattern for strongly typed errors in regorus — new subsystems should
follow this design.

## Rule Caching

The VM caches rule evaluation results to avoid redundant computation:
- Rules are identified by index
- Cache is checked before evaluation
- Cache size must match rule info count (`VmError::RuleCacheSizeMismatch`)

## Virtual Document Lookup

Virtual documents (rules-as-data) are resolved through `virtual_data.rs`:
- Paths are navigated through the rule tree
- Results are cached per-evaluation
- `needs_runtime_recursion_check` flag enables recursion detection

## Performance Priorities

Optimization focus areas in `src/rvm/vm/`:
1. **Instruction dispatch** — tight loop, minimal branch overhead
2. **Register window pooling** — predictable allocation, zero unnecessary allocs
3. **Rule caching** — avoid redundant evaluation
4. **Virtual document lookup caching** — avoid redundant path navigation
5. **Comprehension building** — efficient collection construction

Profile with `benches/` (Criterion) before optimizing.
