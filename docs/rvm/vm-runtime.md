# VM Runtime Walkthrough

This document explains the runtime architecture implemented under
`src/rvm/vm`. It focuses on the `RegoVM` struct, execution modes, and the
responsibilities of each support module.

---

## 1. RegoVM structure

`src/rvm/vm/machine.rs` defines the public entry point. The table below maps its
fields to responsibilities.

| Field                                 | Purpose                                                     | Related modules |
| :------------------------------------ | :---------------------------------------------------------- | :-------------- |
| `registers: Vec<Value>`               | Active register window for the current frame.               | `execution.rs`, `dispatch.rs` |
| `pc: usize`                           | Instruction pointer in run-to-completion mode.              | `execution.rs` |
| `program: Arc<Program>`               | Loaded program artifact.                                    | `program/core.rs` |
| `compiled_policy`                     | Optional legacy default-rule support.                       | `crate::CompiledPolicy` |
| `rule_cache: Vec<(bool, Value)>`      | Memoized rule results (bool = computed).                    | `rules.rs` |
| `data`, `input`                       | Global documents injected by host.                          | `dispatch.rs`, `virtual_data.rs` |
| `loop_stack`                          | Stack of `LoopContext` for run-to-completion loops.         | `loops.rs` |
| `call_rule_stack`                     | Stack of `CallRuleContext` for nested rule calls.           | `rules.rs` |
| `register_stack`                      | Saves prior register windows during run-to-completion rule calls. | `rules.rs`, `state.rs` |
| `comprehension_stack`                 | Active `ComprehensionContext` objects.                      | `comprehension.rs` |
| `base_register_count`                 | Root window size derived from program metadata.             | `load_program` |
| `register_window_pool`                | Recycled register vectors to reduce allocations.            | `state.rs`, `rules.rs` |
| `max_instructions`, `executed_instructions` | Instruction limit and internal per-execution counter.     | `execution.rs` |
| `evaluated`                           | Cache for virtual document lookups.                         | `virtual_data.rs` |
| `cache_hits`                          | Counters aiding diagnostics.                                | `virtual_data.rs` |
| `execution_stack`                     | Explicit frame stack for suspendable mode.                  | `execution_model.rs` |
| `execution_state`                     | `ExecutionState` enum capturing Ready/Running/Suspended/Error/Completed. | `execution_model.rs`, `execution.rs` |
| `breakpoints`                         | Set of PCs that trigger suspension.                         | `execution_model.rs` |
| `step_mode`                           | Enables single-step suspension after each instruction.      | `execution.rs` |
| `host_await_responses`                | Pre-scripted responses keyed by identifier (run-to-completion). | `dispatch.rs` |
| `execution_mode`                      | `RunToCompletion` or `Suspendable`.                         | `execution.rs` |
| `next_execution_mode`                 | Mode selected for the next initial execution.                | `machine.rs` |
| memory-budget usage scalar            | Per-VM requested-byte total retained across suspendable segments. | `machine.rs`, allocator shim |
| `frame_pc_overridden`                 | Tracks manual PC updates inside frames.                     | `execution.rs`, `loops.rs`, `comprehension.rs` |
| `strict_builtin_errors`               | Configures builtin failure handling (error vs `undefined`).  | `machine.rs`, `arithmetic.rs`, `dispatch.rs` |

### Key methods

- `new` / `new_with_policy`: initialise VM with default register windows and
  instruction limits.
- `load_program`: attaches a compiled `Program`, resizes registers, seeds rule
  cache and resets counters.
- `set_data` / `set_input`: inject host documents. `set_data` runs
  `Program::check_rule_data_conflicts` to guard against rule/data collisions.
- `set_max_instructions`, `set_execution_mode`, `set_step_mode`: configure
  runtime policy. `set_max_instructions` replaces the limit without resetting
  the current execution's counter.
- `set_host_await_responses`: pre-loads responses per identifier, consumed in
  FIFO order when `HostAwait` executes in run-to-completion mode. A registered
  call with an undefined input skips `HostAwait` and leaves the queue untouched.
- `set_strict_builtin_errors`: toggles builtin failure semantics between
  `VmError::ArithmeticError` and returning `Value::Undefined`.
- Accessors (`get_pc`, `get_registers`, `get_loop_stack`, etc.) aid debugging
  and visualisation tooling.
- `get_host_await_argument`: when the VM is suspended on a `HostAwait`, returns
  the argument value passed by the policy. Returns `None` if not suspended or
  suspended for a different reason. At the serialization boundary the argument
  uses the same `Value`→JSON encoding as evaluation results. Newly compiled
  registered calls return the complete ordered input array (including a
  one-element array); explicit raw calls and previously compiled programs keep
  their original payload shape.
- `get_host_await_identifier`: when the VM is suspended on a `HostAwait`, returns
  the identifier that triggered the suspension. Returns `None` if not applicable.
  The identifier is an arbitrary `Value` chosen by the policy — for a registered
  builtin it is the registered name, and for the raw `__builtin_host_await(arg, id)`
  form it is whatever the second argument evaluates to. The current FFI exposes
  string identifiers only.

---

## 2. Execution modes

### Value comparisons and output

Direct comparison instructions (`Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`, and
`AssertEq`) use iterative Value traversal. With an execution timer enabled,
the traversal checkpoints each continuation frame and each 256-byte string chunk, including
same-type comparisons and array, object-value, and set membership. Deadline
errors remain errors in strict and non-strict execution, including resumed
segments, which publish terminal error state and release execution values.
Traversal work counts toward the existing timer's `check_interval`, not the
instruction count. The deadline is not restarted for each comparison.
Equality retains length checks at every nested container, including direct
Array/Set/Object equality and comparisons with resource checks disabled.
Equality and ordering both checkpoint
before skipping pointer-identical strings and containers, including shared DAGs.
With allocator limits enabled, traversal also checks the active execution budget
and global memory ceiling while scratch storage is live, even without a timer.
Without a timer or applicable memory limit, comparisons use native iterative
Value comparisons.

The traversal does not memoize shared substructures. Compact shared DAGs can
still require exponential work to finish, but covered comparisons can stop
at a timer checkpoint instead of expanding the entire structure first.

Depth admission is separate from those traversals: the shared Value depth
validator memoizes completed container subtree heights by pointer identity.
Its active stack is path-sized and its memo has one entry per distinct
container, with cooperative memory checkpoints. Reusing a subtree at a deeper
path still checks its full height. This avoids expanding every DAG occurrence
just to admit a Value; it does not memoize `walk`, comparison, or output
traversals, which may still expand shared occurrences.

Program loading records rule-tree admission errors for execution to report.
Structural depth failures stay rejected. Resource failures are checked again
before execution: lifting a memory limit lets the same VM run a valid program
without loading it again. A successful retry clears the saved error; a retry
can still discover an actual depth violation.

With memory limits but no timer, scalar set membership retains native O(log n)
B-tree lookup, checking limits before and after the lookup. Scalar probes cannot
descend into stored containers. Timed membership and resource-checked compound
probes use a sorted O(n) scan, since a B-tree comparator cannot return a resource
error mid-traversal. Unchecked membership retains the native lookup.
Other implicit B-tree comparisons remain infallible: iterative Value traits
prevent nesting-dependent stack growth but do not checkpoint the execution timer.
Scalar number comparison is also an indivisible checkpoint unit. This is not
a hard interruption guarantee: builtins and other internal VM comparisons
are not wired to these checks, and interpreter comparisons do not gain timer
checks here.

Strict comparison and shared builtin argument diagnostics report structural
summaries such as `Array(len=1)` or `String(bytes=4096)`, without rendering the
contents. Public Value Debug and successful JSON output are unchanged.
Display, `to_json_str`, `to_json_str_compact`, `QueryResults::to_json_str`, and
native returned-value JSON use the upstream iterative
encoder. It checks the global memory ceiling during traversal, buffer growth,
scalar output, and indentation; native VM result formatting also checks the
active execution budget before completing the output. These are cooperative
checks, not a physical-OOM guarantee. Generic Serde callbacks have a separate
64-container nesting budget; this is not an input admission limit. Program JSON
serialization also preserves the separate 32-container program limit for
literals, rule trees, and annotations, returning an error rather than panicking.

The FFI query-result endpoint uses `QueryResults::to_json_str`, preserving the
pretty-JSON field order and omit-empty rules while accepting deep expression
values and bindings. Host-await argument output uses compact iterative JSON,
preserving whitespace within strings, escaping, and the original payload shape.
Neither endpoint inherits the generic Serde nesting budget.

Serialization-budget errors, and memory-limit errors while encoding non-string
object keys, retain typed resource identity through builtin
calls and interpreter function evaluation, including default-function
comprehensions and function-valued `with` replacement expressions. They cannot
select a successful alternative, default, or
negated branch in non-strict mode. Ordinary builtin type errors keep their
existing strict/non-strict semantics.
Azure Policy `string`, `format`, and `join` use fallible compact JSON for
container-to-string conversions. Formatting exhaustion is an error, not a
successful string containing Display's diagnostic text. Public Display remains
diagnostic on failure; successful JSON and scalar-conversion conventions remain
unchanged.

JSON schema and document conversion use checked compact JSON output and the
bounded structural reader, including objects with non-string keys. Memory
exhaustion remains a typed error, not an invalid-schema Boolean or undefined
document. For example, `not json.verify_schema({0: input, 1: true})[0]` cannot
succeed just because copying a large input exhausts the memory budget.

Collection destruction uses the upstream iterative final-owner drain. Shared
owners are not cloned to release them, and exhausted object iterators are freed
before descending into their final pair. Single-child array/set chains need no
continuation allocation; branching shapes and object key/value continuations can
allocate. Cooperative memory limits do not prohibit cleanup allocations, and
successful destruction under physical allocator exhaustion is not guaranteed.

### Interpreter statement continuations

The tree-walking interpreter retains its separate native evaluation nesting
budget of 64. Recursive expression, rule/function, nested-query, and output-loop
evaluation remain guarded; a resource error is not undefined, a rule default,
or a successful negation, even with non-strict builtin errors.

Sequential statement continuations, including `some .. in` and hoisted index
or `walk` loops, use explicit heap-backed backtracking frames instead of nested
native calls. Body width therefore does not consume that native budget.
Frames retain collection cursors and binding plans, restore iteration scopes
and cached loop values, and unwind active `with` state on success or error.
Array traversal stays lazy. Object/set continuations take shallow, shared-Value
snapshots using borrowed iteration, with memory/time checkpoints before and
after each entry/member is accumulated. Advancing these snapshots does not
search, hash, or structurally compare keys/members; shared DAG prefixes therefore
do not turn cursor advancement into an unchecked structural traversal. Snapshot
storage is proportional to the collection's entry count, not its expanded tree.
Hoisted collection evaluation restores the complete saved state before
propagating an error. Function-value `with` replacement also propagates typed
resource errors instead of falling back to function-name lookup.
Default evaluation restores the caller's scopes on every result path. Error
unwinding attempts every frame's scope, cached-value, and saved-state cleanup:
cleanup failures cannot downgrade an original fatal evaluation error, and an
independent cleanup failure is returned even if evaluation otherwise succeeded.

This is not an unlimited-width or constant-memory guarantee: live choice points
and scope snapshots consume memory, and combinations can require exponential
work. The RVM's independent 255-register window still rejects some wide bodies
with register overflow; `with` remains unsupported by its compiler. Tests cover
128-statement interpreter bodies, shared-backend 24-hoisted-loop and 40-some-in
bodies with eight helper calls, and real native-nesting rejection/recovery in
isolated 1,500,000-byte workers. These are bounded measurements, not a universal
host-stack guarantee.

### Native rule-call depth limit

By default, the VM allows at most 16 active rule calls that use the native thread
stack. The next call returns `VmError::RuleCallDepthExceeded`, not undefined or a
rule default. The VM clears the failed execution's state and can be used again.

The limit applies to run-to-completion calls and synchronous virtual-document
lookups in either mode, including during resume. Explicit suspendable rule
frames do not count toward it.

Rust callers can change the per-VM limit with
`vm.set_max_native_rule_call_depth(max)` and read it with
`vm.max_native_rule_call_depth()`. It is checked before each new native rule
evaluation, including during resume, and survives evaluation resets and program
loads. Zero rejects calls that need a native rule frame; cached results and
default-only rules can still return without one. There is no new binding API.
The private supported native ceiling is 17. Larger settings are retained by the
setter, but a synchronous uncached rule evaluation rejects them with
`RuleCallDepthExceeded { limit: 17, .. }` before entering its body. The configured
setting is not clamped or reset. Explicit suspendable frames remain independent
of this setting; synchronous virtual-document lookups still check it.

This VM resource limit can reject valid, nonrecursive policies. It is separate
from instruction, time, and memory limits. Depth 16 was tested on Windows in
debug and release with a 2 MiB test-thread stack; other stack sizes and call
patterns may behave differently. The limit does not guarantee stack safety.

`tests/rvm/rego/cases/native_depth.yaml` covers results and errors. Rust tests
reuse those cases to check typed errors, cleanup, VM reuse, and stepping. Both
run in subprocesses with a timeout and a 2 MiB test-thread stack.
These subprocess-backed tests are excluded under Miri.
Additional boundary/configuration and frontend/interpreter regressions use
explicit 1,500,000-byte workers inside isolated subprocesses. These bounded
checks do not establish a universal host-stack guarantee.

### Run-to-completion

- Entry path: `execute()` or `execute_entry_point_by_*` when
  `ExecutionMode::RunToCompletion`.
- `execute_run_to_completion` resets state, marks `ExecutionState::Running` and
  calls `jump_to(start_pc)`.
- `jump_to` loops over instructions, updating `pc` and calling
  `execute_instruction`. The loop stops on `Return`, `Break`, or `VmError`.
  `Break` (emitted by `RuleReturn` and `DestructuringSuccess`) returns
  register 0 to the caller for compatibility with rule evaluation.
- Suspension is not allowed: an instruction that would suspend the VM raises an
  internal error. `HostAwait` therefore does not suspend here — it consumes the
  next pre-loaded response for its identifier (see `set_host_await_responses`),
  and raises `VmError::HostAwaitResponseMissing` only when no response is
  queued for that identifier.
- Instruction budgets trigger `VmError::InstructionLimitExceeded` and switch the
  state to `ExecutionState::Error`.

### Suspendable

- Entry path: same public API, but the VM calls `run_stackless_from`.
- `run_stackless_from` pushes an initial `ExecutionFrame::main(start_pc, 0)`
  onto `execution_stack` and dispatches instructions via `run_stackless_loop`.
- Each frame tracks its own `pc` and `FrameKind` (`Main`, `Rule`, `Loop`,
  `Comprehension`).
- `RuleFrameData` carries scheduling cursors, register window sizing, and saved
  copies of the caller's registers and stacks so finalisation can restore the
  original context.
- Suspension: `InstructionOutcome::Suspend` records a `SuspendReason` (host
  await, breakpoint, step) and stores the last result snapshot. Host code calls
  `resume(resume_value)` to continue.
- Completion: when `execution_stack` becomes empty the VM sets
  `ExecutionState::Completed { result }`.
- With `allocator-memory-limits`, the VM retains a checked requested-byte
  scalar across suspendable segments. The allocator shim selects it in
  thread-local state only while a synchronous segment runs, charging every
  successful allocation, zeroed allocation, and reallocation; frees do not
  refund it. Segment boundaries persist the scalar to the VM and restore the
  prior selector, so resumes may migrate between threads without resetting
  consumption. Updating the configured budget or execution mode affects only
  the next initial execution. Native FFI resume parsing, inner resume, and
  immediate result serialization share one accounting window.
- An independent unbudgeted VM entry, resume, or native conversion nested inside
  a budgeted callback temporarily selects no usage and restores the caller's
  selector on return or unwind. This does not alter run-to-completion
  thread-baseline accounting. Initial suspendable failures publish
  `ExecutionState::Error`; unbudgeted failures retain the legacy register
  contents.
- With `allocator-memory-limits`, each valid initial entry point checks the
  global memory ceiling after setup and validation, immediately before dispatch.
  Per-instruction checks remain throttled, and resume behavior is unchanged.

`execution_model.rs` defines the frame types and state machine:

- `ExecutionFrame`: captures the frame-local `pc` together with its
  `FrameKind` payload.
- `RuleFrameData`: tracks rule index, scheduling phase, register window sizing,
  and the saved caller state (`saved_registers`, `saved_loop_stack`,
  `saved_comprehension_stack`).
- `SuspendReason`: currently surfaced values are host await, breakpoint, and
  step; additional variants (`SuspendInstruction`, `InstructionLimit`,
  `External`) are reserved for future instructions.

---

## 3. Instruction dispatch

`dispatch.rs` routes each `Instruction` variant through layered helpers
(`execute_load_and_move`, `execute_arithmetic_instruction`, `execute_call_instruction`, etc.). Control
flow hinges on the `InstructionOutcome` enum:

- `Continue`: normal execution; the caller increments the frame `pc`.
- `Return(Value)`: unwinds the current rule/function frame, propagating the
  value upward.
- `Break`: used for rule-specific constructs (destructuring success, rule
  return) to exit to the owning frame without returning a value.
- `Suspend { reason }`: used exclusively in suspendable mode.

Arithmetic and comparison opcodes live in `arithmetic.rs`, honouring
`strict_builtin_errors` when operand types differ. Collection, loop, and
virtual-data operations share helpers that convert `Value` variants with runtime
type checking. Errors become `VmError` variants to ensure consistent reporting.
`Halt` returns the value stored in register 0, allowing bytecode to terminate
early without suspending.

---

## 4. Loops and comprehensions

`loops.rs` implements iteration. Major components:

- `LoopContext`: stores iteration state (`IterationState` enum), key/value/result
  registers, body and exit PCs, counters, and loop mode.
- `IterationState`: variants for arrays, objects, sets. Tracks progress for both
  execution modes.
- `LoopMode`: `Any`, `Every`, `ForEach` controls short-circuit behaviour.

`execute_loop_start` initialises iteration, pushing the context onto
`loop_stack` (run-to-completion) or embedding it into a `FrameKind::Loop`
(suspendable). `LoopParams` carries the bytecode offsets, registers, and
destinations required by the instruction. `LoopNext` evaluates the previous
iteration outcome, updates `success_count`, advances the iterator, overrides
the caller's PC when needed, and decides whether to continue or exit.

`comprehension.rs` parallels `loops.rs` but maintains builder collections in
`ComprehensionContext`. The context stores:

- Builder value (array, set, object).
- Pending key/value registers.
- `body_start` / `comprehension_end` PCs.
- `iteration_state` for nested loops bound to the comprehension.

`ComprehensionYield` writes to the builder, respecting set uniqueness and object
key/value pairing. `ComprehensionEnd` publishes the result to `result_reg` and
pops the context.

---

## 5. Rule execution and caching

`rules.rs` and `functions.rs` coordinate rule calls:

- `execute_call_rule` dispatches based on execution mode. Both paths consult
  `rule_cache` and short-circuit if the result is already available.
- Run-to-completion (`execute_call_rule_common`): swaps the active register,
  loop, and comprehension stacks; pushes them onto `register_stack`; and drives
  bodies via `jump_to`. Successful results are cached for non-function rules.
- Suspendable (`execute_call_rule_suspendable`): builds a `RuleFrameData`
  containing saved registers/stacks and pushes a `FrameKind::Rule` so the
  stackless loop can schedule destructuring, bodies, and finalisation.
- `execute_rule_init` writes the rule result register to `Value::Undefined`
  (or initialises sets/objects) before running the bodies and records the
  result register in the active `CallRuleContext`.
- `execute_rule_return` lets the scheduler finalise the frame and propagate the
  cached value to the caller.
- `functions.rs::execute_function_call` prepares argument registers and delegates
  to `execute_call_rule*`, enforcing arity via `BuiltinInfo` metadata.

Rule destructuring relies on `CallRuleContext`,
`RuleFramePhase::ExecutingDestructuring`, and the `DestructuringSuccess`
instruction to detect when pattern matching succeeded before entering the body.

---

## 6. Virtual data lookups

`virtual_data.rs` implements `VirtualDataDocumentLookup` and caches intermediate
path results in the VM's `evaluated` field (using `Value::Undefined` as a
sentinel) to avoid repeated rule evaluations. The compiler may set
`Program::needs_runtime_recursion_check`; the runtime currently relies on the
instruction budget and caching to prevent runaway recursion. Paths consist of
literals and register values supplied via `VirtualDataDocumentLookupParams`.

`ChainedIndex` follows a similar pattern but operates on register roots instead
of the global `data` namespace.

---

## 7. Error handling and diagnostics

`errors.rs` defines the `VmError` enum. Common variants include:

- `InstructionLimitExceeded`
- `LiteralIndexOutOfBounds`
- `RegisterNotArray` / `RegisterNotObject`
- `InvalidEntryPointIndex` / `EntryPointNotFound`
- `ArithmeticError`
- `RuleDataConflict`
- `RuleConflict` when definitions of a complete rule, or of a function for the
  same arguments, succeed with different values. Like resource-limit errors it
  is never absorbed as a body failure, so it aborts the whole evaluation.
- `HostAwaitResponseMissing`
- `Internal(String)` for invariant violations

Value-bearing error fields use `regorus::DiagnosticValue`. Construct them with
`value.into()`; Display and Debug summarize the value without expanding shared
containers or oversized scalar payloads. Use `as_value()` to inspect the original
`Value`, or `into_value()` to recover it. The wrapper preserves the original
payload and does not guarantee PII redaction.

`execution.rs::handle_instruction_error` centralises error propagation. In
suspendable mode it unwinds frames while preserving partial results where
possible. Run-to-completion mode returns the error immediately.

`state.rs` provides helpers to reset the VM and emit debug snapshots used in
assertion messages. When an internal invariant fails, the error message includes
`self.get_debug_state()` to help diagnose the issue.

---

## 8. Operational guidance

### Instruction budget contract

The default instruction limit is 25,000 dispatched bytecode instructions per
execution. A limit of zero permits no dispatches. The counter is incremented
once immediately before each dispatched instruction; the next instruction is
rejected when the counter has reached the configured limit. Builtin calls and
`HostAwait` each consume one dispatch, not the work performed inside the host
or builtin.

`execute` and a valid entry-point execution begin a fresh count, and
`load_program` also resets the count while preserving the configured maximum.
`resume` continues the same count. Replacing the maximum while suspended
preserves consumption: lowering it below the current count rejects the next
dispatch, while raising it can provide more headroom. Invalid entry-point
selection can fail before a fresh execution is initialized.

Instruction exhaustion is `VmError::InstructionLimitExceeded` with the limit,
executed count, and program counter. The C# binding maps it to the existing
generic `InvalidOperationException`; `executed_instructions` remains an
internal runtime field and is not a public C# getter.

- **Instruction budgets**: adjust via `set_max_instructions` when running
  untrusted policies. Use the instruction-limit error for the runtime metadata;
  consumers should not assume a public consumed-count accessor.
- **Breakpoints & stepping**: populate `breakpoints` with bytecode PCs (see the
  assembly listing) and enable `set_step_mode(true)` to pause after each
  instruction.
- **Host await**: in run-to-completion mode, configure `set_host_await_responses`
  before execution; each `HostAwait` consumes the next queued response for its
  identifier, and a missing response is a `VmError::HostAwaitResponseMissing`.
  In suspendable mode, expect `ExecutionState::Suspended { reason: HostAwait
  { .. } }`, read the identifier and argument, and resume with the chosen value.
- **Builtin strictness**: `set_strict_builtin_errors(true)` reports type
  mismatches as `VmError::ArithmeticError`; leave it `false` to coerce results
  to `Value::Undefined`.
- **State inspection**: use getters (`get_registers`, `get_call_stack`,
  `get_loop_stack`, `get_cache_hits`) to instrument evaluation or build
  debugging UIs. `get_debug_state()` provides a concise snapshot for logs.
- **Testing**: YAML suites under `tests/rvm/vm/suites` exercise loops,
  comprehensions, virtual data, host awaits, and serialization. `complex.yaml`
  combines nested loops, comprehensions, function calls, and host awaits.

---
