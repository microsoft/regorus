// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Comprehensive RVM benchmarks covering all aspects of the Rego Virtual Machine.
//!
//! # Policy families
//!
//! | Family     | Source                        | Policies | Inputs/policy |
//! |------------|-------------------------------|----------|---------------|
//! | Synthetic  | `benches/evaluation/test_data`| 9        | 3 each        |
//! | ACI        | `tests/aci`                   | 9        | 1 each        |
//!
//! # Benchmark groups
//!
//! | Group                    | What it measures                                      |
//! |--------------------------|-------------------------------------------------------|
//! | `cold/{case}/{config}`   | Cold: new VM + load + data + input + execute          |
//! | `hot/{case}/{config}`    | Hot: set_input + execute (VM reused across iters)     |
//! | `compilation`            | Rego CompiledPolicy → RVM Program                     |
//! | `serialization`          | Program binary serialize / deserialize roundtrip       |
//! | `startup`                | Isolated VM creation & setup overhead                 |
//! | `stats`                  | Instruction/literal counts (reported as throughput)    |
//! | `end_to_end`             | Full roundtrip: compile → serialize → deserialize → eval |
//!
//! # Running subsets
//!
//! ```sh
//! cargo bench --bench rvm_benchmark                              # everything
//! cargo bench --bench rvm_benchmark -- cold                      # all cold eval
//! cargo bench --bench rvm_benchmark -- hot                       # all hot eval
//! cargo bench --bench rvm_benchmark -- regular_with_limits       # one config across cases
//! cargo bench --bench rvm_benchmark -- cold/aci/                 # all ACI cold benchmarks
//! cargo bench --bench rvm_benchmark -- rbac                      # one policy family
//! cargo bench --bench rvm_benchmark -- compilation               # compilation only
//! cargo bench --bench rvm_benchmark -- serialization             # serialization only
//! cargo bench --bench rvm_benchmark -- startup                   # startup overhead
//! ```

use std::hint::black_box;
use std::num::NonZeroU32;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use serde::{Deserialize, Serialize};
use walkdir::WalkDir;

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::Program;
use regorus::rvm::vm::{ExecutionMode, RegoVM};
use regorus::utils::limits::ExecutionTimerConfig;
use regorus::{Engine, Rc, Value};

// ---------------------------------------------------------------------------
// Limit constants – generous ceilings that still exercise the limit-checking
// hot path (memory_check, execution_timer_tick, instruction-limit compare).
// ---------------------------------------------------------------------------

#[cfg(feature = "allocator-memory-limits")]
const MEMORY_LIMIT_BYTES: u64 = 256 * 1024 * 1024;
const TIME_LIMIT: Duration = Duration::from_secs(30);
const TIMER_CHECK_INTERVAL: NonZeroU32 = NonZeroU32::new(16).unwrap();
const INSTRUCTION_LIMIT: usize = 10_000_000;

#[derive(Clone, Copy)]
struct EvalConfig {
    name: &'static str,
    mode: ExecutionMode,
    limits: bool,
}

const EVAL_CONFIGS: [EvalConfig; 4] = [
    EvalConfig {
        name: "regular_no_limits",
        mode: ExecutionMode::RunToCompletion,
        limits: false,
    },
    EvalConfig {
        name: "regular_with_limits",
        mode: ExecutionMode::RunToCompletion,
        limits: true,
    },
    EvalConfig {
        name: "suspendable_no_limits",
        mode: ExecutionMode::Suspendable,
        limits: false,
    },
    EvalConfig {
        name: "suspendable_with_limits",
        mode: ExecutionMode::Suspendable,
        limits: true,
    },
];

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

/// A compiled benchmark program ready for RVM execution.
struct BenchmarkProgram {
    /// Human-readable name (e.g. "rbac_policy" or "aci/create_container").
    name: String,
    /// Pre-compiled RVM program.
    program: Arc<Program>,
    /// Compiled policy (kept for compilation benchmarks).
    compiled_policy: regorus::CompiledPolicy,
    /// Entry-point rule path.
    entry_point: String,
    /// Data object (Some for policies that require external data like ACI).
    data: Option<Value>,
    /// Named inputs for this policy.
    inputs: Vec<(String, Value)>,
}

// ---------------------------------------------------------------------------
// ACI YAML types
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize, Debug)]
struct AciTestCase {
    note: String,
    data: Value,
    input: Value,
    modules: Vec<String>,
    query: String,
    want_result: Value,
}

#[derive(Serialize, Deserialize, Debug)]
struct AciYamlTest {
    cases: Vec<AciTestCase>,
}

// ---------------------------------------------------------------------------
// Synthetic policy loading
// ---------------------------------------------------------------------------

/// Policy ↔ input file mapping for synthetic policies.
const SYNTHETIC_POLICIES: &[(&str, &str, &[&str])] = &[
    (
        "rbac_policy",
        "rbac_policy.rego",
        &["rbac_input.json", "rbac_input2.json", "rbac_input3.json"],
    ),
    (
        "api_access",
        "api_access_policy.rego",
        &[
            "api_access_input.json",
            "api_access_input2.json",
            "api_access_input3.json",
        ],
    ),
    (
        "data_sensitivity",
        "data_sensitivity_policy.rego",
        &[
            "data_sensitivity_input.json",
            "data_sensitivity_input2.json",
            "data_sensitivity_input3.json",
        ],
    ),
    (
        "time_based",
        "time_based_policy.rego",
        &[
            "time_based_input.json",
            "time_based_input2.json",
            "time_based_input3.json",
        ],
    ),
    (
        "data_processing",
        "data_processing_policy.rego",
        &[
            "data_processing_input.json",
            "data_processing_input2.json",
            "data_processing_input3.json",
        ],
    ),
    (
        "azure_vm",
        "azure_vm_policy.rego",
        &[
            "azure_vm_input.json",
            "azure_vm_input2.json",
            "azure_vm_input3.json",
        ],
    ),
    (
        "azure_storage",
        "azure_storage_policy.rego",
        &[
            "azure_storage_input.json",
            "azure_storage_input2.json",
            "azure_storage_input3.json",
        ],
    ),
    (
        "azure_keyvault",
        "azure_keyvault_policy.rego",
        &[
            "azure_keyvault_input.json",
            "azure_keyvault_input2.json",
            "azure_keyvault_input3.json",
        ],
    ),
    (
        "azure_nsg",
        "azure_nsg_policy.rego",
        &[
            "azure_nsg_input.json",
            "azure_nsg_input2.json",
            "azure_nsg_input3.json",
        ],
    ),
];

/// Compile synthetic Rego policies into RVM programs.
fn compile_synthetic_programs() -> Vec<BenchmarkProgram> {
    let base_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("benches")
        .join("evaluation")
        .join("test_data");

    let entry_point = "data.bench.allow";
    let entry_point_rc: Rc<str> = entry_point.into();

    SYNTHETIC_POLICIES
        .iter()
        .map(|(name, policy_file, input_files)| {
            let policy_path = base_dir.join("policies").join(policy_file);
            let policy_content = std::fs::read_to_string(&policy_path)
                .unwrap_or_else(|e| panic!("Failed to read {policy_path:?}: {e}"));

            let mut engine = Engine::new();
            engine
                .add_policy("policy.rego".to_string(), policy_content)
                .expect("failed to add policy");

            let compiled_policy = engine
                .compile_with_entrypoint(&entry_point_rc)
                .expect("failed to compile policy");

            let program = Compiler::compile_from_policy(&compiled_policy, &[entry_point])
                .expect("failed to compile to RVM program");

            let inputs: Vec<(String, Value)> = input_files
                .iter()
                .map(|input_file| {
                    let input_path = base_dir.join("inputs").join(input_file);
                    let json = std::fs::read_to_string(&input_path)
                        .unwrap_or_else(|e| panic!("Failed to read {input_path:?}: {e}"));
                    let value = Value::from_json_str(&json).expect("failed to parse input JSON");
                    let display = input_file.trim_end_matches(".json").to_string();
                    (display, value)
                })
                .collect();

            BenchmarkProgram {
                name: name.to_string(),
                program,
                compiled_policy,
                entry_point: entry_point.to_string(),
                data: None,
                inputs,
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// ACI policy loading
// ---------------------------------------------------------------------------

/// Load all ACI test cases from YAML files.
fn load_aci_cases(dir: &Path) -> Vec<AciTestCase> {
    let mut cases = Vec::new();
    for entry in WalkDir::new(dir)
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path = entry.path();
        if !path.to_string_lossy().ends_with(".yaml") {
            continue;
        }
        let yaml = std::fs::read(path).expect("failed to read yaml");
        let yaml = String::from_utf8_lossy(&yaml);
        let test: AciYamlTest = serde_yaml::from_str(&yaml).expect("failed to deserialize yaml");
        cases.extend(test.cases);
    }
    cases
}

/// Build an Engine with policies loaded for a given ACI test case.
fn build_aci_engine(dir: &Path, case: &AciTestCase) -> Engine {
    let mut engine = Engine::new();
    engine.set_rego_v0(true);
    engine
        .add_data(case.data.clone())
        .expect("failed to add data");
    engine.set_input(case.input.clone());
    for (idx, rego) in case.modules.iter().enumerate() {
        if rego.ends_with(".rego") {
            engine
                .add_policy_from_file(dir.join(rego).to_str().expect("invalid path"))
                .expect("failed to add policy");
        } else {
            engine
                .add_policy(format!("rego{idx}.rego"), rego.clone())
                .expect("failed to add policy");
        }
    }
    engine
}

/// Compile ACI test cases into RVM programs.
fn compile_aci_programs() -> Vec<BenchmarkProgram> {
    let dir = Path::new("tests/aci");
    load_aci_cases(dir)
        .into_iter()
        .map(|case| {
            let mut engine = build_aci_engine(dir, &case);
            let rule = case.query.replace("=x", "");
            let rule_rc: Rc<str> = rule.clone().into();
            let compiled_policy = engine
                .compile_with_entrypoint(&rule_rc)
                .expect("failed to compile");
            let program = Compiler::compile_from_policy(&compiled_policy, &[rule.as_str()])
                .expect("failed to compile to RVM");

            BenchmarkProgram {
                name: format!("aci/{}", case.note),
                program,
                compiled_policy,
                entry_point: rule,
                data: Some(case.data),
                inputs: vec![("input".to_string(), case.input)],
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Compile all policies
// ---------------------------------------------------------------------------

/// Compile all policies (synthetic + ACI) into RVM programs.
fn compile_all_programs() -> Vec<BenchmarkProgram> {
    let mut programs = compile_synthetic_programs();
    programs.extend(compile_aci_programs());
    programs
}

// ---------------------------------------------------------------------------
// Limit helpers
// ---------------------------------------------------------------------------

/// Apply or remove production-style limits based on a boolean flag.
fn configure_limits(vm: &mut RegoVM, limits: bool) {
    if limits {
        #[cfg(feature = "allocator-memory-limits")]
        regorus::set_global_memory_limit(Some(MEMORY_LIMIT_BYTES));
        vm.set_execution_timer_config(Some(ExecutionTimerConfig {
            limit: TIME_LIMIT,
            check_interval: TIMER_CHECK_INTERVAL,
        }));
        vm.set_max_instructions(INSTRUCTION_LIMIT);
    } else {
        #[cfg(feature = "allocator-memory-limits")]
        regorus::set_global_memory_limit(None);
        vm.set_execution_timer_config(None);
        vm.set_max_instructions(usize::MAX);
    }
}

// ---------------------------------------------------------------------------
// Cold evaluation — new VM per iteration (full setup + execute)
//
// Benchmarks are registered case-first so each workload is shown with all
// config variants adjacent to one another, making per-case comparisons easier.
// ---------------------------------------------------------------------------

fn bench_cold(c: &mut Criterion) {
    let programs = compile_all_programs();
    let mut group = c.benchmark_group("cold");

    for bp in &programs {
        for (input_name, input_value) in &bp.inputs {
            let case_id = if bp.inputs.len() == 1 {
                bp.name.clone()
            } else {
                format!("{}/{}", bp.name, input_name)
            };
            let program = bp.program.clone();
            let data = bp.data.clone();
            let input = input_value.clone();

            for config in EVAL_CONFIGS {
                group.bench_function(BenchmarkId::new(&case_id, config.name), |b| {
                    b.iter(|| {
                        let mut vm = RegoVM::new();
                        vm.set_execution_mode(config.mode);
                        vm.load_program(black_box(program.clone()));
                        if let Some(ref d) = data {
                            vm.set_data(black_box(d.clone())).unwrap();
                        }
                        vm.set_input(black_box(input.clone()));
                        configure_limits(&mut vm, config.limits);
                        black_box(vm.execute().unwrap())
                    })
                });
            }
        }
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// Hot evaluation — VM reused across iterations
//
// The VM is created once with program, data, mode, and limits.  Each
// iteration only calls set_input + execute, measuring pure execution
// overhead with minimal setup.  A warm-up execution fills the register
// window pool so all iterations benefit from pooled allocations.
// ---------------------------------------------------------------------------

fn bench_hot(c: &mut Criterion) {
    let programs = compile_all_programs();
    let mut group = c.benchmark_group("hot");

    for bp in &programs {
        let program = bp.program.clone();
        let data = bp.data.clone();
        let inputs: Vec<Value> = bp.inputs.iter().map(|(_, v)| v.clone()).collect();
        let num_inputs = inputs.len();

        for config in EVAL_CONFIGS {
            group.bench_function(BenchmarkId::new(&bp.name, config.name), |b| {
                let mut vm = RegoVM::new();
                vm.set_execution_mode(config.mode);
                vm.load_program(program.clone());
                if let Some(ref d) = data {
                    vm.set_data(d.clone()).unwrap();
                }
                configure_limits(&mut vm, config.limits);

                // Warm up: fill register window pools, caches, etc.
                vm.set_input(inputs[0].clone());
                vm.execute().expect("warm-up failed");

                let mut i = 0usize;
                b.iter(|| {
                    let input = &inputs[i % num_inputs];
                    vm.set_input(black_box(input.clone()));
                    black_box(vm.execute().unwrap());
                    i += 1;
                })
            });
        }
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// Compilation — Rego CompiledPolicy → RVM Program
// ---------------------------------------------------------------------------

fn bench_compilation(c: &mut Criterion) {
    let programs = compile_all_programs();
    let mut group = c.benchmark_group("compilation");

    for bp in &programs {
        let entry_point: &str = &bp.entry_point;
        group.bench_with_input(
            BenchmarkId::new("rego_to_rvm", &bp.name),
            &bp.compiled_policy,
            |b, compiled_policy| {
                b.iter(|| {
                    Compiler::compile_from_policy(
                        black_box(compiled_policy),
                        black_box(&[entry_point]),
                    )
                    .unwrap();
                })
            },
        );
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// Serialization — binary serialize / deserialize roundtrip
// ---------------------------------------------------------------------------

fn bench_serialization(c: &mut Criterion) {
    let programs = compile_all_programs();
    let mut group = c.benchmark_group("serialization");

    for bp in &programs {
        let program = &bp.program;
        let serialized = program
            .serialize_binary()
            .expect("failed to serialize program");
        let byte_len = serialized.len() as u64;

        group.throughput(Throughput::Bytes(byte_len));
        group.bench_function(BenchmarkId::new("serialize", &bp.name), |b| {
            b.iter(|| black_box(program.serialize_binary().unwrap()))
        });

        group.throughput(Throughput::Bytes(byte_len));
        group.bench_function(BenchmarkId::new("deserialize", &bp.name), |b| {
            b.iter(|| black_box(Program::deserialize_binary(black_box(&serialized)).unwrap()))
        });
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// Startup — isolated VM creation & setup overhead
// ---------------------------------------------------------------------------

fn bench_startup(c: &mut Criterion) {
    let programs = compile_all_programs();
    let mut group = c.benchmark_group("startup");

    // Use the first program as representative for startup overhead.
    let bp = &programs[0];
    let program = bp.program.clone();
    let input = bp.inputs[0].1.clone();

    // Bare VM creation
    group.bench_function("new", |b| b.iter(|| black_box(RegoVM::new())));

    // load_program (Arc clone + internal setup)
    group.bench_function("load_program", |b| {
        b.iter(|| {
            let mut vm = RegoVM::new();
            vm.load_program(black_box(program.clone()));
            black_box(&vm);
        })
    });

    // set_input
    group.bench_function("set_input", |b| {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        b.iter(|| {
            vm.set_input(black_box(input.clone()));
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Stats — instruction / literal counts (reported as throughput)
// ---------------------------------------------------------------------------

fn bench_stats(c: &mut Criterion) {
    let programs = compile_all_programs();

    eprintln!();
    eprintln!(
        "{:<30} {:>8} {:>8} {:>8} {:>10}",
        "program", "instrs", "lits", "entries", "bytes"
    );
    eprintln!("{}", "-".repeat(70));

    let mut group = c.benchmark_group("stats");
    for bp in &programs {
        let serialized = bp.program.serialize_binary().expect("serialize failed");
        let byte_len = serialized.len();
        let instr_count = bp.program.instructions.len();
        let lit_count = bp.program.literals.len();
        let entry_count = bp.program.entry_points.len();

        eprintln!(
            "{:<30} {:>8} {:>8} {:>8} {:>10}",
            bp.name, instr_count, lit_count, entry_count, byte_len,
        );

        group.throughput(Throughput::Elements(instr_count as u64));
        group.bench_function(BenchmarkId::new("serialize", &bp.name), |b| {
            b.iter(|| black_box(bp.program.serialize_binary().unwrap()))
        });
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// End-to-end roundtrip (compile + serialize + deserialize + eval)
//
// Only runs for synthetic policies where we have direct access to rego
// source files.  ACI policies are loaded from YAML with module references
// which makes the setup pipeline different.
// ---------------------------------------------------------------------------

fn bench_end_to_end(c: &mut Criterion) {
    let base_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("benches")
        .join("evaluation")
        .join("test_data");

    let entry_point = "data.bench.allow";
    let entry_point_rc: Rc<str> = entry_point.into();

    let mut group = c.benchmark_group("end_to_end");

    for &(name, policy_file, input_files) in SYNTHETIC_POLICIES {
        let policy_path = base_dir.join("policies").join(policy_file);
        let policy_content = std::fs::read_to_string(&policy_path)
            .unwrap_or_else(|e| panic!("Failed to read {policy_path:?}: {e}"));

        // Use just the first input for end-to-end
        let input_path = base_dir.join("inputs").join(input_files[0]);
        let input_json = std::fs::read_to_string(&input_path)
            .unwrap_or_else(|e| panic!("Failed to read {input_path:?}: {e}"));

        group.bench_function(BenchmarkId::new("roundtrip", name), |b| {
            b.iter(|| {
                // 1. Engine + parse
                let mut engine = Engine::new();
                engine
                    .add_policy("policy.rego".to_string(), policy_content.clone())
                    .unwrap();

                // 2. Compile to CompiledPolicy
                let compiled_policy = engine.compile_with_entrypoint(&entry_point_rc).unwrap();

                // 3. Compile to RVM Program
                let program =
                    Compiler::compile_from_policy(&compiled_policy, &[entry_point]).unwrap();

                // 4. Serialize
                let bytes = program.serialize_binary().unwrap();

                // 5. Deserialize
                let deserialized = Program::deserialize_binary(&bytes).unwrap();
                let program = match deserialized {
                    regorus::rvm::program::DeserializationResult::Complete(p) => Arc::new(p),
                    regorus::rvm::program::DeserializationResult::Partial(p) => {
                        Arc::new(Program::compile_from_partial(p).unwrap())
                    }
                };

                // 6. Execute
                let mut vm = RegoVM::new();
                vm.load_program(program);
                let input = Value::from_json_str(&input_json).unwrap();
                vm.set_input(input);
                black_box(vm.execute().unwrap());
            })
        });
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Criterion groups — organised for selective runs
// ---------------------------------------------------------------------------

criterion_group!(cold_benches, bench_cold);

criterion_group!(hot_benches, bench_hot);

criterion_group!(
    misc_benches,
    bench_compilation,
    bench_serialization,
    bench_startup,
    bench_stats,
    bench_end_to_end,
);

criterion_main!(cold_benches, hot_benches, misc_benches);
