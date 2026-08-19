# RVM memory budgets

RVM run-to-completion execution supports an optional memory budget when Regorus is built with the `allocator-memory-limits` feature.

The budget limits additional live bytes on the execution thread. Regorus captures a baseline when execution starts and compares later live-byte samples with that baseline. Every call to `execute`, `execute_entry_point_by_name`, or `execute_entry_point_by_index` starts with a fresh budget.

```rust
use core::num::NonZeroU64;
use regorus::rvm::vm::RegoVM;
use regorus::MemoryBudgetConfig;

let mut vm = RegoVM::new();
vm.set_memory_budget_config(Some(MemoryBudgetConfig {
    limit: NonZeroU64::new(16 * 1024 * 1024).expect("non-zero budget"),
}));
```

No configured budget preserves existing RVM behavior. A zero-byte budget is not representable in Rust and is rejected by language bindings.

## Included work

The budget starts when RVM execution begins. Allocations retained by rule evaluation and its result count against the budget.

Program compilation, program loading, data loading, input loading, and context loading happen before the execution baseline and are not charged.

## Enforcement

Regorus checks the budget cooperatively during VM dispatch and once before returning a successful result. Enforcement can overshoot between checks. A short-lived allocation created and freed inside one instruction may not be observed.

Exhaustion returns `VmError::MemoryBudgetExceeded`, including:

- additional live-byte usage observed for the evaluation
- configured budget
- VM program counter

The C FFI reports `RegorusStatus::MemoryBudgetExceeded`. The C# binding throws `RegorusMemoryBudgetExceededException`.

## Execution modes

The first implementation supports run-to-completion execution only. Configuring a budget and executing in suspendable mode returns `VmError::MemoryBudgetUnsupportedInSuspendableExecution`.

Suspendable execution may resume on another thread. A thread-local baseline cannot safely span that migration without evaluation-owned allocation attribution.

## Process-global limit

The existing process-global memory limit remains separate. It protects the process as a whole and is not an isolation mechanism for individual evaluations. When both controls are configured, the per-evaluation budget is checked first.
