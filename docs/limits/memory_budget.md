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
observations. Suspendable execution instead snapshots one thread-safe account
for the accepted execution. It tracks currently live requested bytes allocated
while that execution is selected, including retained VM frames, registers,
caches, continuations, and allocations made synchronously by builtins or
callbacks. Allocator metadata and allocator-rounded capacity are not charged.

The account is selected only during each synchronous execution segment. Each
allocation records its requested size and account; freeing the block debits that
same account on any thread, including after the VM or execution has ended.
Nested and concurrent executions therefore have independent accounts, and a
resume may run on a different thread without moving or resetting its budget.
The account remains alive while any attributed allocation remains live.
An independent unbudgeted VM entry, resume, or immediate native conversion
temporarily selects no execution account, even when nested inside a budgeted
callback; the previous selector is restored on return or unwind. This selector
is separate from run-to-completion thread-baseline accounting.

A successful `realloc` is treated as replacing the old block: its old account is
debited and the full new requested size is charged to the account selected for
the reallocation, or to no execution if none is selected. A failed `realloc`
preserves the old block and its attribution. Allocations made before execution
are not charged unless a successful reallocation replaces them during that
execution.

Program compilation and loading, data/input/context loading, host I/O, cache
getter serialization, managed C# encoding/decoding, other allocators, and
detached work are outside the budget. For native FFI execute and resume calls,
the C-string copy and JSON parsing of resume input, VM resume work, immediate
result JSON serialization, and native `CString` allocation are included.
Managed C# string allocation after the native call returns is excluded.

The process-global requested-byte limit remains independent and its counters
are not changed by per-execution attribution. At shared checkpoints the
per-execution budget takes precedence over a global memory-limit error.

## Enforcement and lifecycle

Enforcement is cooperative, not an allocation-time peak-memory cap. Regorus
checks before instruction dispatch, after resume input conversion, before
returning from a suspension point, after terminal execution, and after native
result serialization. A single instruction, builtin, callback, input parse, or
serialization operation can temporarily overshoot before the next check.
Usage equal to the configured limit succeeds; usage greater than it fails.

Exhaustion returns `VmError::MemoryBudgetExceeded`, including the observed live
requested bytes, configured budget, and VM program counter. A terminal failure
of a budgeted suspendable execution invalidates retained and completed
results, releases execution state, and records `ExecutionState::Error`.
Unbudgeted initial failures also record `Error` while preserving legacy
register contents. Missing or unexpected resume values and native JSON
syntax/EOF errors are retryable and preserve a valid suspended continuation.
A later global or per-execution counter observation does not turn malformed
syntax into a terminal resource failure; actual typed resource failures during
conversion remain terminal.

The C FFI reports `RegorusStatus::MemoryBudgetExceeded` (status 10), including
when native resume parsing or immediate result serialization exceeds the
budget. Status 11 remains reserved for ABI compatibility. C# throws
`RegorusMemoryBudgetExceededException`. The FFI budget window closes on success,
terminal error, or unwinding; allocations already returned to a host remain
attributed until freed.

Loading a new program while a budgeted suspendable execution is active abandons
that continuation and retires its budget. Starting another initial execution
also abandons any prior continuation. Terminal success retires enforcement,
but the allocation account remains available to debit outstanding exported
blocks. Run-to-completion accounting and ordinary no-budget execution retain
their existing behavior.

There is no public multi-call begin/end memory-budget scope; the RVM owns the
account and retires enforcement with its execution lifecycle. Rust, C FFI, and
C# are supported; other bindings require follow-up work.
