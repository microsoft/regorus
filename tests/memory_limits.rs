#![cfg(all(feature = "mimalloc", feature = "allocator-memory-limits", not(miri)))]

#[cfg(feature = "rvm")]
use std::num::NonZeroU64;
#[cfg(feature = "rvm")]
use std::sync::{Arc, Barrier};
use std::sync::{Mutex, OnceLock};

use anyhow::Error;
use mimalloc::global_allocation_stats_snapshot;
#[cfg(feature = "rvm")]
use regorus::MemoryBudgetConfig;
use regorus::{set_global_memory_limit, Engine, LimitError, Value};

#[cfg(feature = "rvm")]
use regorus::languages::rego::compiler::Compiler;
#[cfg(feature = "rvm")]
use regorus::rvm::vm::RegoVM;
#[cfg(feature = "rvm")]
use regorus::rvm::vm::VmError;
#[cfg(feature = "rvm")]
use regorus::Rc;

static LIMIT_LOCK: OnceLock<Mutex<()>> = OnceLock::new();

struct LimitGuard {
    _guard: std::sync::MutexGuard<'static, ()>,
}

impl LimitGuard {
    fn lock() -> Self {
        let mutex = LIMIT_LOCK.get_or_init(|| Mutex::new(()));
        let guard = mutex.lock().expect("limit mutex poisoned");
        // Start with no global limit while the caller prepares state.
        set_global_memory_limit(None);
        Self { _guard: guard }
    }

    fn set_below_current_usage(&mut self) {
        self.set_absolute_limit(1);
    }

    fn set_with_additional_budget(&mut self, budget: u64) {
        self.set_with_usage_limit(|usage| usage.saturating_add(budget));
    }

    fn set_absolute_limit(&mut self, limit: u64) {
        set_global_memory_limit(Some(limit));
    }

    fn set_with_usage_limit<F>(&mut self, calc: F)
    where
        F: FnOnce(u64) -> u64,
    {
        let usage = global_allocation_stats_snapshot().allocated as u64;
        let limit = calc(usage);
        self.set_absolute_limit(limit);
    }
}

impl Drop for LimitGuard {
    fn drop(&mut self) {
        set_global_memory_limit(None);
    }
}

const SIMPLE_MODULE: &str = r#"
package limit

allow if {
    true
}
"#;

const LARGE_PARSE_MODULE: &str = r#"
package limit

large_array := json.unmarshal(data.limit.large_json)
"#;

#[cfg(feature = "jsonpatch")]
const JSON_PATCH_MODULE: &str = r#"
package limit

patched := json.patch(input, [{"op": "add", "path": "/-", "value": 0}])
"#;

fn assert_memory_limit_error(err: &Error) {
    match err.downcast_ref::<LimitError>() {
        Some(LimitError::MemoryLimitExceeded { .. }) => {}
        Some(other) => panic!("unexpected limit error variant: {other:?}"),
        None => panic!("expected memory limit error, got: {err}"),
    }
}

fn large_json_data(elements: usize) -> Value {
    let mut payload = String::with_capacity(elements * 6);
    payload.push('[');
    for i in 0..elements {
        if i > 0 {
            payload.push(',');
        }
        payload.push_str(&i.to_string());
    }
    payload.push(']');

    let json = serde_json::json!({
        "limit": {
            "large_json": payload,
        }
    });

    Value::from_json_str(&json.to_string()).expect("valid JSON")
}

fn new_engine_with_module(module: &str) -> Engine {
    let mut engine = Engine::new();
    engine
        .add_policy("limit.rego".to_string(), module.to_string())
        .expect("add policy");
    engine
}

#[test]
fn interpreter_memory_limit_on_entry() {
    let mut guard = LimitGuard::lock();
    let mut engine = new_engine_with_module(SIMPLE_MODULE);
    guard.set_below_current_usage();
    let err = engine
        .eval_query("data.limit.allow".to_string(), false)
        .expect_err("expected interpreter memory limit error");
    assert_memory_limit_error(&err);
}

#[cfg(feature = "rvm")]
#[test]
fn vm_memory_limit_on_entry() {
    let mut guard = LimitGuard::lock();
    let mut engine = new_engine_with_module(SIMPLE_MODULE);
    let entrypoint = Rc::from("data.limit.allow");
    let compiled = engine
        .compile_with_entrypoint(&entrypoint)
        .expect("compile policy for VM");
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
        .expect("compile VM program");

    let mut vm = RegoVM::new();
    vm.load_program(program.clone());
    vm.set_data(engine.get_data()).expect("set data");
    vm.set_input(Value::Undefined);

    guard.set_below_current_usage();
    match vm.execute() {
        Err(VmError::MemoryLimitExceeded { .. }) => {}
        Err(other) => panic!("expected VM memory limit error, got {other}"),
        Ok(value) => panic!("expected VM memory limit error, got value {value:?}"),
    }
}

#[test]
fn interpreter_memory_limit_during_large_allocation() {
    let mut guard = LimitGuard::lock();
    let mut engine = new_engine_with_module(LARGE_PARSE_MODULE);
    let large_data = large_json_data(200_000);
    engine.add_data(large_data).expect("add large JSON data");

    guard.set_with_additional_budget(0);
    let err = engine
        .eval_rule("data.limit.large_array".to_string())
        .expect_err("expected interpreter memory limit error while parsing");
    assert_memory_limit_error(&err);
}

#[cfg(feature = "jsonpatch")]
#[test]
fn json_patch_propagates_memory_limit_errors() {
    let mut guard = LimitGuard::lock();
    let mut engine = new_engine_with_module(JSON_PATCH_MODULE);
    let input = Value::from((0..50_000).map(Value::from).collect::<Vec<_>>());
    engine.set_input(input);

    // Entry checks require no meaningful allocation. This budget lets
    // evaluation enter the builtin, then forces the edit-tree construction
    // to trip the allocator limit. The builtin must propagate LimitError,
    // never translate it to Undefined as it does malformed patches.
    guard.set_with_additional_budget(64 * 1024);
    let err = engine
        .eval_rule("data.limit.patched".to_string())
        .expect_err("expected json.patch edit-tree allocation to hit the memory limit");
    assert_memory_limit_error(&err);
}

#[cfg(feature = "rvm")]
#[test]
fn vm_memory_limit_during_large_allocation() {
    let mut guard = LimitGuard::lock();
    let mut engine = new_engine_with_module(LARGE_PARSE_MODULE);
    let large_data = large_json_data(200_000);
    engine.add_data(large_data).expect("add large JSON data");

    let entrypoint = Rc::from("data.limit.large_array");
    let compiled = engine
        .compile_with_entrypoint(&entrypoint)
        .expect("compile policy for VM");
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
        .expect("compile VM program");

    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(engine.get_data()).expect("set data");
    vm.set_input(Value::Undefined);

    guard.set_with_additional_budget(0);
    match vm.execute() {
        Err(VmError::MemoryLimitExceeded { .. }) => {}
        Err(other) => panic!("expected VM memory limit error, got {other}"),
        Ok(value) => panic!("expected VM memory limit error, got value {value:?}"),
    }
}

/// On the `allocator-memory-limits` build, an `add_data` whose merge trips the memory limit
/// mid-way must leave the data document unchanged — no partial insertions may leak. Atomicity
/// here relies on the candidate-copy commit (`check_mergeable` models conflicts, not limits).
#[test]
fn add_data_memory_limit_partial_merge_is_atomic() {
    let mut guard = LimitGuard::lock();
    let mut engine = Engine::new();

    // Seed existing data while the limit is relaxed.
    engine
        .add_data(Value::from_json_str(r#"{ "a": { "existing": 1 } }"#).expect("valid JSON"))
        .expect("seed add_data");

    // Merge `{ "a": { "k0": 0, ... } }` into `a` as pure insertions. The count is sized to
    // beat the limit check's throttling — a check only fires every MEMORY_CHECK_STRIDE (16)
    // insertions or per MEMORY_CHECK_DELTA_BYTES (32 KiB), and mimalloc's usage snapshot lags
    // small allocations — so the trip lands mid-merge rather than after it completes.
    let elements = 20_000;
    let mut payload = String::with_capacity(elements * 16);
    payload.push_str("{\"a\":{");
    for i in 0..elements {
        if i > 0 {
            payload.push(',');
        }
        payload.push_str("\"k");
        payload.push_str(&i.to_string());
        payload.push_str("\":");
        payload.push_str(&i.to_string());
    }
    payload.push_str("}}");
    let big = Value::from_json_str(&payload).expect("valid JSON");

    // What the engine must still hold if the add is rejected.
    let pristine = Value::from_json_str(r#"{ "a": { "existing": 1 } }"#).expect("valid JSON");

    // Budget 0: the merge's insertions trip the limit mid-way.
    guard.set_with_additional_budget(0);

    let err = engine
        .add_data(big)
        .expect_err("expected memory limit error during add_data merge");
    assert_memory_limit_error(&err);

    // Atomicity: the rejected add must leave data untouched — no `k*` keys leaked.
    assert_eq!(engine.get_data(), pristine);
}

/// Companion for the candidate-copy build: a *conflict* must also be atomic (the candidate is
/// discarded before commit). Default-build conflict atomicity is covered in
/// `src/tests/interpreter/mod.rs`; this exercises the distinct candidate-copy branch.
#[test]
fn add_data_conflict_is_atomic_on_allocator_build() {
    // Hold the lock (no budget set) so the conflict — not a limit — is the sole failure.
    let _guard = LimitGuard::lock();
    let mut engine = Engine::new();

    engine
        .add_data(Value::from_json_str(r#"{ "a": { "z": 1 } }"#).expect("valid JSON"))
        .expect("seed add_data");

    // `m` sorts before `z`, so a naive in-place merge inserts `m` then hits the `z` conflict
    // (1 vs 3). The whole call must be rejected with `m` left out.
    assert!(engine
        .add_data(Value::from_json_str(r#"{ "a": { "m": 2, "z": 3 } }"#).expect("valid JSON"))
        .is_err());

    assert_eq!(
        engine.get_data(),
        Value::from_json_str(r#"{ "a": { "z": 1 } }"#).expect("valid JSON")
    );
}

#[cfg(feature = "rvm")]
#[test]
fn vm_memory_budget_is_enforced_per_execution() {
    let _guard = LimitGuard::lock();
    let mut engine = new_engine_with_module(LARGE_PARSE_MODULE);
    let large_data = large_json_data(200_000);
    engine.add_data(large_data).expect("add large JSON data");

    let entrypoint = Rc::from("data.limit.large_array");
    let compiled = engine
        .compile_with_entrypoint(&entrypoint)
        .expect("compile policy for VM");
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
        .expect("compile VM program");

    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(engine.get_data()).expect("set data");
    vm.set_input(Value::Undefined);
    vm.set_memory_budget_config(Some(MemoryBudgetConfig {
        limit: NonZeroU64::new(1).expect("non-zero budget"),
    }));

    match vm.execute() {
        Err(VmError::MemoryBudgetExceeded { .. }) => {}
        Err(other) => panic!("expected VM memory budget error, got {other}"),
        Ok(value) => panic!("expected VM memory budget error, got value {value:?}"),
    }
}

#[cfg(feature = "rvm")]
#[test]
fn vm_memory_budget_takes_precedence_over_global_limit() {
    let mut guard = LimitGuard::lock();
    let mut engine = new_engine_with_module(SIMPLE_MODULE);
    let entrypoint = Rc::from("data.limit.allow");
    let compiled = engine
        .compile_with_entrypoint(&entrypoint)
        .expect("compile policy for VM");
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
        .expect("compile VM program");

    let mut vm = RegoVM::new();
    vm.load_program(program.clone());
    vm.set_data(engine.get_data()).expect("set data");
    vm.set_input(Value::Undefined);
    vm.set_memory_budget_config(Some(MemoryBudgetConfig {
        limit: NonZeroU64::new(1).expect("non-zero budget"),
    }));
    guard.set_below_current_usage();

    assert!(matches!(
        vm.execute(),
        Err(VmError::MemoryBudgetExceeded { .. })
    ));

    set_global_memory_limit(None);
    let mut vm = RegoVM::new();
    vm.load_program(program.clone());
    vm.set_data(engine.get_data()).expect("set data");
    vm.set_input(Value::Undefined);
    vm.set_memory_budget_config(Some(MemoryBudgetConfig {
        limit: NonZeroU64::new(1).expect("non-zero budget"),
    }));
    guard.set_below_current_usage();

    assert!(matches!(
        vm.execute_entry_point_by_name("data.limit.allow"),
        Err(VmError::MemoryBudgetExceeded { .. })
    ));

    set_global_memory_limit(None);
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(engine.get_data()).expect("set data");
    vm.set_input(Value::Undefined);
    vm.set_memory_budget_config(Some(MemoryBudgetConfig {
        limit: NonZeroU64::new(1).expect("non-zero budget"),
    }));
    guard.set_below_current_usage();

    assert!(matches!(
        vm.execute_entry_point_by_index(0),
        Err(VmError::MemoryBudgetExceeded { .. })
    ));
}

#[cfg(feature = "rvm")]
#[test]
fn vm_memory_budget_is_fresh_for_each_execution() {
    let _guard = LimitGuard::lock();
    let mut engine = new_engine_with_module(SIMPLE_MODULE);
    let entrypoint = Rc::from("data.limit.allow");
    let compiled = engine
        .compile_with_entrypoint(&entrypoint)
        .expect("compile policy for VM");
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
        .expect("compile VM program");

    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(engine.get_data()).expect("set data");
    vm.set_input(Value::Undefined);
    vm.set_memory_budget_config(Some(MemoryBudgetConfig {
        limit: NonZeroU64::new(1024 * 1024).expect("non-zero budget"),
    }));

    assert_eq!(vm.execute().expect("first execution"), Value::Bool(true));
    assert_eq!(vm.execute().expect("second execution"), Value::Bool(true));
    assert_eq!(
        vm.execute_entry_point_by_name("data.limit.allow")
            .expect("named entry point"),
        Value::Bool(true)
    );
    assert_eq!(
        vm.execute_entry_point_by_index(0)
            .expect("indexed entry point"),
        Value::Bool(true)
    );
}

#[cfg(feature = "rvm")]
#[test]
fn vm_memory_budget_does_not_receive_credit_from_previous_results() {
    let _guard = LimitGuard::lock();
    let mut engine = new_engine_with_module(LARGE_PARSE_MODULE);
    let large_data = large_json_data(50_000);
    engine.add_data(large_data).expect("add large JSON data");

    let entrypoint = Rc::from("data.limit.large_array");
    let compiled = engine
        .compile_with_entrypoint(&entrypoint)
        .expect("compile policy for VM");
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
        .expect("compile VM program");

    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(engine.get_data()).expect("set data");
    vm.set_memory_budget_config(Some(MemoryBudgetConfig {
        limit: NonZeroU64::new(256 * 1024 * 1024).expect("non-zero budget"),
    }));
    assert!(matches!(
        vm.execute().expect("first execution"),
        Value::Array(_)
    ));

    vm.set_memory_budget_config(Some(MemoryBudgetConfig {
        limit: NonZeroU64::new(1).expect("non-zero budget"),
    }));

    assert!(matches!(
        vm.execute(),
        Err(VmError::MemoryBudgetExceeded { .. })
    ));
}

#[cfg(feature = "rvm")]
#[test]
fn vm_memory_budget_rejects_suspendable_execution() {
    let _guard = LimitGuard::lock();
    let mut vm = RegoVM::new();
    vm.set_execution_mode(regorus::rvm::vm::ExecutionMode::Suspendable);
    vm.set_memory_budget_config(Some(MemoryBudgetConfig {
        limit: NonZeroU64::new(1024).expect("non-zero budget"),
    }));

    match vm.execute() {
        Err(VmError::MemoryBudgetUnsupportedInSuspendableExecution { .. }) => {}
        Err(other) => panic!("expected unsupported memory budget error, got {other}"),
        Ok(value) => panic!("expected unsupported memory budget error, got value {value:?}"),
    }
}

#[cfg(feature = "rvm")]
#[test]
fn vm_memory_budgets_are_independent_across_threads() {
    let _guard = LimitGuard::lock();
    let mut engine = new_engine_with_module(LARGE_PARSE_MODULE);
    let large_data = large_json_data(50_000);
    engine
        .add_data(large_data.clone())
        .expect("add large JSON data");

    let entrypoint = Rc::from("data.limit.large_array");
    let compiled = engine
        .compile_with_entrypoint(&entrypoint)
        .expect("compile policy for VM");
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
        .expect("compile VM program");
    let barrier = Arc::new(Barrier::new(2));

    std::thread::scope(|scope| {
        let constrained_program = program.clone();
        let constrained_data = large_data.clone();
        let constrained_barrier = barrier.clone();
        let constrained = scope.spawn(move || {
            let mut vm = RegoVM::new();
            vm.load_program(constrained_program);
            vm.set_data(constrained_data).expect("set constrained data");
            vm.set_memory_budget_config(Some(MemoryBudgetConfig {
                limit: NonZeroU64::new(1).expect("non-zero budget"),
            }));
            constrained_barrier.wait();
            vm.execute()
        });

        let relaxed_program = program.clone();
        let relaxed_barrier = barrier.clone();
        let relaxed = scope.spawn(move || {
            let mut vm = RegoVM::new();
            vm.load_program(relaxed_program);
            vm.set_data(large_data).expect("set relaxed data");
            vm.set_memory_budget_config(Some(MemoryBudgetConfig {
                limit: NonZeroU64::new(256 * 1024 * 1024).expect("non-zero budget"),
            }));
            relaxed_barrier.wait();
            vm.execute()
        });

        assert!(matches!(
            constrained.join().expect("constrained thread"),
            Err(VmError::MemoryBudgetExceeded { .. })
        ));
        assert!(matches!(
            relaxed
                .join()
                .expect("relaxed thread")
                .expect("relaxed execution"),
            Value::Array(_)
        ));
    });
}
