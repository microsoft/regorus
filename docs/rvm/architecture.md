# Regorus Virtual Machine Architecture

This document explains how Rego source becomes executable bytecode and how the
runtime evaluates it. It is meant for three audiences:

- **Engine developers** working on the RVM execution core and runtime subsystems.
- **Policy front-end authors** targeting the VM from alternate policy languages.
- **Operators/tools** wanting to reason about execution behaviour and
  troubleshooting output.


The high-level pipeline looks like this:

```
        ┌───────────┐   emit Program   ┌────────────┐   load & run   ┌─────────┐
        │  Parser & │ ───────────────▶ │  Program   │ ─────────────▶ │ Rego VM │
        │ Compiler  │   (bytecode)     │  Artifact  │   (instructions│ Runtime │
        └───────────┘                  │            │    + metadata) │         │
                                       └────────────┘                └─────────┘
```

Each step feeds the next via well-defined data structures described below.

---

## RVM in context

The Rego VM uses a register-based architecture with the following traits:

- **Register windows per frame**: Each rule or function call receives a
  compile-time-sized register window. Windows are pooled and reused to keep the
  runtime allocation profile predictable.
- **Sequential bytecode stream**: Fixed-width 32-bit instructions execute from
  a linear program counter with optional jumps. Complex instructions reference
  shared tables (`InstructionData`) that carry literals, loop metadata and call
  parameters.
- **Literal and builtin tables**: Literal pools and builtin dispatch tables are
  resolved at load time so bytecode stays compact and symbol lookups remain
  constant-time during execution.
- **Extended control stacks**: Loop, rule-cache and comprehension stacks sit
  alongside the core call stack, enabling suspension, short-circuiting and
  deterministic rule caching without growing the register windows themselves.

---

## 1. Compilation Outputs

A successful compilation produces a `Program` (`src/rvm/program/core.rs`). The
layout is deliberately split:

- **Stable artifact section**: Always serialised and treated as canonical. It
  captures the original policy sources, entry-points, compiler options,
  etc.
- **Synthesised execution section**: It contains the
  compiled instruction stream, instruction parameter tables, literal tables, etc.
  It can be recreated from the stable artifact section if a future RVM version is
  note able to deserialize it.


| Field                                           | Purpose                                                          | Notes |
| :---------------------------------------------- | :--------------------------------------------------------------- | :---- |
| `instructions: Vec<Instruction>`                | Ordered bytecode emitted by the compiler.                       | Each opcode is defined in `src/rvm/instructions/mod.rs` and executed by the dispatch tree. |
| `literals: Vec<Value>`                          | Literal constants shared across instructions.                   | Skipped by serde but written in the binary format via `BinaryValueSlice`; avoids duplicating large value graphs. |
| `instruction_data: InstructionData`             | Parameter tables for complex opcodes.                           | Tables are indexed by `params_index` values stored in instructions. |
| `builtin_info_table: Vec<BuiltinInfo>`          | Metadata for builtin calls.                                      | Enforced and resolved by `Program::initialize_resolved_builtins`. |
| `entry_points: IndexMap<String, usize>`         | Maps path names (e.g. `data.pkg.rule`) to starting PCs.          | Preserves declaration order for tooling and serialized in the artifact section. |
| `sources: Vec<SourceFile>`                      | Captures original policy sources.                               | Stored in the stable artifact section alongside entry-points. |
| `rule_infos: Vec<RuleInfo>`                     | Metadata for every rule.                                         | Includes register windows, default values, destructuring blocks. |
| `instruction_spans: Vec<Option<SpanInfo>>`      | Optional span info for diagnostics.                             | Lines/columns mapped back into the source table when present. |
| `main_entry_point: usize`                       | Default bytecode entry point.                                   | Used by loaders to jump into the top-level policy. |
| `max_rule_window_size` / `dispatch_window_size` | Register window sizing hints.                                   | The VM uses these to size register banks up-front. |
| `metadata: ProgramMetadata`                     | Compilation metadata (`compiler_version`, etc.).                 | Helps operators verify provenance and tooling compatibility. |
| `rule_tree: Value`                              | Map of rule labels for conflict detection and lookups.          | Serialized via `BinaryValueRef`; rebuilt into a `Value::Object` during load. |
| `resolved_builtins: Vec<BuiltinFcn>`            | Resolved builtin function pointers.                             | Not serialized; repopulated by the host at load time. |
| `needs_runtime_recursion_check: bool`           | Flags when `VirtualDataDocumentLookup` requires runtime guards.  | Ensures the VM short-circuits recursion before hitting the instruction budget ceiling. |
| `needs_recompilation: bool`                     | Indicates partial deserialization of execution data.             | Set when the extensible section fails; signals the loader to recompile. |
| `rego_v0: bool`                                 | Records whether the policy targeted Rego v0 semantics.          | Ensures recompilation preserves language-version behaviour. |

Additional helpers such as `Program::add_*`, `Program::update_*`, and
`Program::display_instruction_with_params` are used by the compiler and
inspection tooling to populate and render the program.

### Serialization layout

The module `src/rvm/program/serialization` writes `Program` instances into a
compact binary envelope that stays forward-compatible within a major format
version:

1. **Header**: magic `REGO` bytes followed by `SERIALIZATION_VERSION` (currently
  `3`).
2. **Section manifest**: four little-endian `u32` lengths for entry points,
  sources, literals, and the rule tree, plus a single-byte `rego_v0` flag.
3. **Preamble payloads**: each section is encoded with `bincode` using helper
  wrappers (`BinaryValueSlice`, `BinaryValueRef`) to stream complex `Value`
  graphs without cloning.
4. **Program core**: the remaining `Program` struct is serialized once more via
  `bincode`; fields skipped by serde (entry points, literals, sources,
  rule_tree, resolved builtins) are re-inserted from the preamble when the
  program is reconstructed.

During deserialization the loader sanity-checks the header, lengths, and
version before decoding each preamble section. Any failure while decoding the
core payload downgrades the result to `DeserializationResult::Partial`,
preserving enough artifact data to trigger a recompilation. Successful loads
call `Program::initialize_resolved_builtins` so host runtimes can plug in their
builtin implementations.

---

## 2. Runtime Subsystems

At evaluation time the `RegoVM` (`src/rvm/vm/machine.rs`) consumes a `Program`
and exposes execution APIs. The VM separates concerns through specialised
stacks and caches.


````text
Runtime stacks (run-to-completion)

┌──────────────────────────── RegoVM ─────────────────────────────┐
│  Registers (active window) ─────┐                               │
│  Program counter (pc) ───────┐  │                               │
│                              ▼  ▼                               │
│  Control flow dispatcher  ───────────────▶  Instruction stream  │
│                               ▲  ▲                              │
│  Rule cache ────────┐         │  │    Loop stack (LoopContext)  │
│  Evaluation cache   │         │  └──▶ Comprehension stack       │
│  Host await queue ──┴─▶ Return values / suspensions             │
└─────────────────────────────────────────────────────────────────┘

Suspendable mode frame stack

┌───────────────────────────────────────────────────────────────────────┐
│                 Frame stack                                           │
│                                                                       │
│  ┌────────────────┐    ┌────────────────┐    ┌──────────────────────┐ │
│  │    RuleFrame   │ →  │    LoopFrame   │ →  │  ComprehensionFrame  │ │
│  └────────────────┘    └────────────────┘    └──────────────────────┘ │
│       ▲                        ▲                          ▲           │
│       │ push frame             │ push frame               │ push frame│
│       ▼                        ▼                          ▼           │
│  allow { ... }                                                        │
│                        some user in input.users                       │
│                                                        [x | ... ]     │
└─────────┴─────────────────────────────────────────────────────────────┘
 
Execution state machine (suspendable)

                          ┌──────────────────────┐
                          │       Suspended      │
                          └─────▲────────────┬───┘
                                │            │
                                |            │
                                │            │
                                │            │
      HostAwait/Breakpoint/Step │            | resume   
                                │            │
                                │            │
                                |            ▼
┌──────────┐              ┌───────────────────────────┐   Return    ┌────────────┐
│  Ready   ├─────────────▶│          Running          │────────────▶│ Completed  │
└──────────┘              └────────────┬──────────────┘             └────────────┘
                                       │ VmError
                                       ▼
                                 ┌──────────┐
                                 │  Error   │
                                 └──────────┘
````

Key state:

- **Registers**: The active register window for the current frame. Windows are
  allocated per rule call using a register pool to minimise allocations.
- **Program counter (`pc`)**: The bytecode index for run-to-completion mode. In
  suspendable mode, each frame tracks its own `pc`.
- **Rule cache**: Stores results and completion flags per rule to avoid
  recomputation.
- **Loop/comprehension stacks**: Track iteration state, completion criteria, and
  pending yields.
- **Execution stack**: Present in suspendable mode. Stores `ExecutionFrame`
  objects (`FrameKind::Rule`, `Loop`, `Comprehension`) so that the VM can pause
  and resume evaluation cleanly.
- **Host await responses**: For run-to-completion execution, pre-defined values
  keyed by identifier. Suspendable mode instead returns a
  `SuspendReason::HostAwait` to the caller.
- **Evaluation cache**: Used by `VirtualDataDocumentLookup` to memoise path
  results.


---

## 3. Execution Modes

The VM supports two execution styles selected via `set_execution_mode`.

### Run-to-completion

- Entry point: `RegoVM::execute` or `execute_entry_point_by_{index,name}`.
- Control loop: `execute_run_to_completion` → `jump_to` which iterates the
  instruction stream sequentially.
- Suspension: Unsupported. Any instruction that would suspend emits a runtime
  error because the host cannot resume.
- Traps: Instruction budget enforced via `max_instructions`; exceeding the limit
  returns `VmError::InstructionLimitExceeded`.

### Suspendable

- Entry point: same as above, but the VM calls `run_stackless_from` which pushes
  a main `ExecutionFrame` and dispatches instructions through
  `run_stackless_loop`.
- Frames: Each instruction can adjust the currently active frame or push/pop
  new frames (rule calls, loops, comprehensions).
- Suspension: `InstructionOutcome::Suspend` transitions the VM into
  `ExecutionState::Suspended` with a `SuspendReason` (host await, breakpoint,
  single-step). The host must call `resume` with an optional value to continue.
- Breakpoints & step mode: Configured via `set_step_mode` and breakpoint
  mutators on `ExecutionState`. Execution halts when a frame `pc` matches a
  registered breakpoint.

In both modes the VM constantly validates safety conditions: parameter indices
must resolve, register windows must exist, and results must stay inside the
supported `Value` lattice. Errors are reported as `VmError` variants that
include formatted state snapshots where possible.

---

## 4. Data-flow Walkthrough

1. **Rule entry**: The compiler emits a `CallRule` instruction referencing a rule
  index. The VM first consults `rule_cache[rule_index]`; non-function rules that
  have already executed within the current top-level run reuse the cached
  result. When the cache is cold, the VM pushes a new rule frame, allocates a
  register window and jumps to the rule entry point. Function rules always run
  afresh today—per-specialisation memoization is not yet implemented.
2. **Literal loads**: `Load` and `Load*` instructions fill registers from the
   literal table or other sources (`LoadData`, `LoadInput`).
3. **Loops**: `LoopStart` fetches `LoopStartParams` from `InstructionData`,
   initialises a `LoopContext`, and either pushes a new execution frame (for
   suspendable mode) or updates `loop_stack`. `LoopNext` consults loop mode
   (`Any`, `Every`, `ForEach`) to decide whether to continue or short-circuit.
4. **Comprehensions**: `ComprehensionBegin`/`Yield`/`End` manage collection
   builders stored in a `ComprehensionContext`. Nested comprehensions stack
   cleanly with loops.
5. **Assertions**: `AssertCondition` and `AssertNotUndefined` enforce Rego's
  truthiness semantics. Inside loops/comprehensions they flag the current
  iteration as failed (or short-circuit `every` loops to `false`); outside loop
  contexts they raise `VmError::AssertionFailed`, mirroring Rego's runtime
  errors for failed guards.
6. **Builtins & functions**: `BuiltinCall` reads `BuiltinCallParams`, resolves
  the host function via `get_resolved_builtin`, and writes the result. Function
  rules use `FunctionCallParams` to marshal arguments and run in the same
  pipeline; repeat invocations with the same arguments are recomputed until the
  VM grows specialisation-aware caching.
7. **Host await**: In run-to-completion mode, `HostAwait` consumes a response
   from `host_await_responses`. Suspendable mode yields control with a
   `SuspendReason::HostAwait { dest, argument, identifier }` that the host must
   service.
8. **Completion**: `Return` wraps the selected register value into
   `InstructionOutcome::Return`, unwinding frames until the entry frame is
   cleared. `RuleReturn` is a specialised variant used by rule execution
   helpers.

Throughout execution, diagnostics (register snapshots, loop counters, cache
hits) can be collected via `RegoVM` accessors. Integration tests in
`tests/rvm/vm/suites` exercise the most complex combinations of loops,
comprehensions and host calls; `complex.yaml` is a good starting point for
understanding real-world instruction streams.

---

## 5. Related Documentation

- [Instruction Set Reference](instruction-set.md)
- [VM Runtime Walkthrough](vm-runtime.md)
