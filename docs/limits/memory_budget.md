# RVM memory budgets

RVM run-to-completion and suspendable execution support an optional memory
budget when Regorus is built with the `allocator-memory-limits` feature.

Each accepted initial `execute` or entry-point execution snapshots the configured
budget. `set_memory_budget_config` and `set_execution_mode` configure the next
initial execution; changing or clearing either setting while a suspendable run
is suspended does not change that run. Resuming never starts a new budget.

```rust
use core::num::NonZeroU64;
use regorus::rvm::vm::RegoVM;
use regorus::MemoryBudgetConfig;

let mut vm = RegoVM::new();
vm.set_memory_budget_config(Some(MemoryBudgetConfig {
    limit: NonZeroU64::new(16 * 1024 * 1024).expect("non-zero budget"),
}));
```

A zero-byte budget is not representable in Rust and is rejected by language
bindings. With no configured budget, existing RVM behavior is unchanged.

## Accounting scope

Run-to-completion execution retains its existing thread-baseline accounting:
sampled live bytes are observed on the execution thread, with the baseline
ratcheted downward when usage falls. Cross-thread frees can therefore skew its
observations. Suspendable execution instead stores a checked gross-requested-
byte scalar in the VM for the accepted execution. During each synchronous
segment the allocator shim selects that scalar in thread-local state and adds
the requested size of every successful allocation, zeroed allocation, and
reallocation. Frees never refund the total. Temporary allocations and
allocations made synchronously by builtins or callbacks count; allocator
metadata and allocator-rounded capacity do not.

At a segment boundary the updated scalar returns to the VM, so a resume can run
on a different thread without moving or resetting its budget. The selector is
restored on normal return or unwind. No per-allocation headers, ownership
records, or shared execution-account atomics are used. Nested VM operations
select their own usage or no usage and restore the parent selector. This
mechanism is separate from run-to-completion thread-baseline accounting.

A successful `realloc` charges its full new requested size to the active
execution; it does not refund the old size, even if the block was allocated
before execution or in another scope. A failed `realloc` charges nothing.
Allocations made before execution are not charged unless successfully
reallocated during that execution, in which case the full new request is
charged.

Program compilation and loading, data/input/context loading, host I/O, cache
getter serialization, managed C# encoding/decoding, other allocators, and
detached work are outside the budget. For native FFI execute and resume calls,
the C-string copy and JSON parsing of resume input, VM resume work, immediate
result JSON serialization, and native `CString` allocation are included.
Managed C# string allocation after the native call returns is excluded.

The process-global live-byte limit remains independent and its counters are
not changed by per-execution attribution. At shared checkpoints the
per-execution budget takes precedence over a global memory-limit error.

## Enforcement and lifecycle

Enforcement is cooperative, not an allocation-time peak-memory cap. Regorus
checks before instruction dispatch, after resume input conversion, before
returning from a suspension point, after terminal execution, and after native
result serialization. A single instruction, builtin, callback, input parse, or
serialization operation can temporarily overshoot before the next check.
Usage equal to the configured limit succeeds; usage greater than it fails.

Exhaustion returns `VmError::MemoryBudgetExceeded`, including the observed
requested-byte total for suspendable execution or live-byte delta for
run-to-completion, the configured budget, and the VM program counter. A terminal failure
of a budgeted suspendable execution invalidates retained and completed
results, releases execution state, and records `ExecutionState::Error`.
Unbudgeted initial failures also record `Error` while preserving legacy
register contents. Missing or unexpected resume values and native JSON
syntax/EOF errors are retryable and preserve a valid suspended continuation.
Malformed syntax/EOF errors do not themselves terminalize the continuation,
but allocations consumed while processing those attempts are not rolled back.
A later valid resume can therefore exhaust the accumulated budget. Typed
resource failures during conversion remain terminal.

The C FFI reports `RegorusStatus::MemoryBudgetExceeded` (status 10), including
when native resume parsing or immediate result serialization exceeds the
budget. Status 11 remains reserved for ABI compatibility. C# throws
`RegorusMemoryBudgetExceededException`. Native resume input conversion, inner
resume, and immediate output serialization share one selected usage window.
The selector is restored on success, terminal error, or unwinding; a
suspendable execution's cumulative total remains with its continuation until
it completes or fails.

Loading a new program while a budgeted suspendable execution is active abandons
that continuation and retires its budget. Starting another initial execution
also abandons any prior continuation. Terminal success or failure retires
enforcement. Run-to-completion accounting and ordinary no-budget execution
retain their existing behavior.

There is no public multi-call begin/end memory-budget scope. The VM owns the
usage scalar and retires it with the execution lifecycle. Rust, C FFI, and C#
are supported; other bindings require follow-up work.
