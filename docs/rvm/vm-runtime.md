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
  FIFO order when `HostAwait` executes in run-to-completion mode.
- `set_strict_builtin_errors`: toggles builtin failure semantics between
  `VmError::ArithmeticError` and returning `Value::Undefined`.
- Accessors (`get_pc`, `get_registers`, `get_loop_stack`, etc.) aid debugging
  and visualisation tooling.
- `get_host_await_argument`: when the VM is suspended on a `HostAwait`, returns
  the argument value passed by the policy. Returns `None` if not suspended or
  suspended for a different reason. At the serialization boundary the argument
  uses the same `Value`→JSON encoding as evaluation results.
- `get_host_await_identifier`: when the VM is suspended on a `HostAwait`, returns
  the identifier that triggered the suspension. Returns `None` if not applicable.
  The identifier is an arbitrary `Value` chosen by the policy — for a registered
  builtin it is the registered name, and for the raw `__builtin_host_await(arg, id)`
  form it is whatever the second argument evaluates to. The current FFI exposes
  string identifiers only.

---

## 2. Execution modes

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
- `HostAwaitResponseMissing`
- `Internal(String)` for invariant violations

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

