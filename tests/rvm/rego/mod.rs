// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use anyhow::Result;
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{
    generate_tabular_assembly_listing, AssemblyListingConfig, DeserializationResult, Program,
};
use regorus::rvm::tests::test_utils::test_round_trip_serialization;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, SuspendReason, VmError};
use regorus::test_utils::{check_output, process_value, value_or_vec_to_vec, ValueOrVec};
use regorus::{CompiledPolicy, Engine, Rc, Value};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, VecDeque};
use std::fs;
use std::sync::Arc;
use test_generator::test_resources;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestCase {
    pub data: Option<Value>,
    pub input: Option<ValueOrVec>,
    pub modules: Vec<String>,
    pub note: String,
    pub query: String,
    pub entry_points: Option<Vec<String>>,
    pub sort_bindings: Option<bool>,
    pub want_result: Option<ValueOrVec>,
    pub want_results: Option<Vec<ValueOrVec>>,
    pub want_prints: Option<Vec<String>>,
    pub no_result: Option<bool>,
    pub skip: Option<bool>,
    pub error: Option<String>,
    pub traces: Option<bool>,
    pub want_error: Option<String>,
    pub want_error_code: Option<String>,
    #[serde(default = "default_strict")]
    pub strict: bool,
    pub rego_v0: Option<bool>,
    pub allow_interpreter_success: Option<bool>,
    pub allow_interpreter_incorrect_behavior: Option<bool>,
    pub skip_interpreter: Option<bool>,
    pub execution_mode: Option<String>,
    pub host_await_responses: Option<Vec<HostAwaitResponseSpec>>,
    pub host_await_responses_run_to_completion: Option<Vec<HostAwaitResponseSpec>>,
    pub host_await_responses_suspendable: Option<Vec<HostAwaitResponseSpec>>,
    pub host_await_builtins: Option<Vec<HostAwaitBuiltinSpec>>,
}

fn default_strict() -> bool {
    true
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    pub cases: Vec<TestCase>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq)]
struct HostAwaitResponseSpec {
    pub id: Value,
    pub args: Option<Value>,
    pub value: Value,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq)]
struct HostAwaitBuiltinSpec {
    pub name: String,
    pub arg_count: usize,
}

type HostAwaitResponseMap = BTreeMap<Value, VecDeque<(Option<Value>, Value)>>;

#[derive(Debug, Clone)]
struct RvmExecutionOptions {
    execution_mode: ExecutionMode,
    host_await_responses_run_to_completion: Option<Vec<(Value, Vec<Value>)>>,
    host_await_responses_suspendable: Option<HostAwaitResponseMap>,
    host_await_builtins: Option<Vec<(String, usize)>>,
}

impl Default for RvmExecutionOptions {
    fn default() -> Self {
        Self {
            execution_mode: ExecutionMode::RunToCompletion,
            host_await_responses_run_to_completion: None,
            host_await_responses_suspendable: None,
            host_await_builtins: None,
        }
    }
}

fn render_program_listing(program: &Program) -> String {
    let config = AssemblyListingConfig::default();
    generate_tabular_assembly_listing(program, &config)
}

fn build_host_await_response_map(
    responses: &[HostAwaitResponseSpec],
) -> anyhow::Result<HostAwaitResponseMap> {
    let mut map: HostAwaitResponseMap = BTreeMap::new();
    for response in responses {
        let id = process_value(&response.id)?;
        let expected_args = response.args.as_ref().map(process_value).transpose()?;
        let value = process_value(&response.value)?;
        map.entry(id).or_default().push_back((expected_args, value));
    }
    Ok(map)
}

fn build_host_await_response_vec(
    responses: &[HostAwaitResponseSpec],
) -> anyhow::Result<Vec<(Value, Vec<Value>)>> {
    // Run-to-completion responses are pre-loaded into the VM, which consumes
    // them internally without surfacing each call's argument to the harness.
    // There is therefore no point at which an `args:` expectation could be
    // checked, so silently dropping it would let a case "assert" a payload
    // that is never verified. Reject `args:` up front instead, pointing the
    // author at suspendable mode where argument validation is supported.
    if let Some(response) = responses.iter().find(|response| response.args.is_some()) {
        return Err(anyhow::anyhow!(
            "`args:` payload validation is not supported in run-to-completion mode \
             (response for id {:?}); drop the `args:` field or move the case to \
             execution_mode: suspendable",
            response.id
        ));
    }
    let map = build_host_await_response_map(responses)?;
    Ok(map
        .into_iter()
        .map(|(id, values)| (id, values.into_iter().map(|(_, output)| output).collect()))
        .collect())
}

fn build_execution_options(case: &TestCase) -> anyhow::Result<RvmExecutionOptions> {
    let execution_mode = match case.execution_mode.as_deref() {
        None | Some("run-to-completion") => ExecutionMode::RunToCompletion,
        Some("suspendable") => ExecutionMode::Suspendable,
        Some(other) => {
            return Err(anyhow::anyhow!("unsupported execution_mode: {other}"));
        }
    };

    // Only build the run-to-completion response vec when the case actually
    // runs in RTC mode. A suspendable case may legitimately use the shared
    // `host_await_responses` field with `args:` expectations (validated via
    // the suspendable map below); building the RTC vec for it would wrongly
    // trip the RTC-only `args:` rejection in `build_host_await_response_vec`.
    let rtc_responses = if execution_mode == ExecutionMode::RunToCompletion {
        case.host_await_responses_run_to_completion
            .as_ref()
            .or(case.host_await_responses.as_ref())
            .map(|responses| build_host_await_response_vec(responses))
            .transpose()?
    } else {
        None
    };

    let suspendable_responses = case
        .host_await_responses_suspendable
        .as_ref()
        .or(case.host_await_responses.as_ref())
        .map(|responses| build_host_await_response_map(responses))
        .transpose()?;

    let ha_builtins = case.host_await_builtins.as_ref().map(|specs| {
        specs
            .iter()
            .map(|s| (s.name.clone(), s.arg_count))
            .collect()
    });

    Ok(RvmExecutionOptions {
        execution_mode,
        host_await_responses_run_to_completion: rtc_responses,
        host_await_responses_suspendable: suspendable_responses,
        host_await_builtins: ha_builtins,
    })
}

fn dump_rvm_listing(case_note: &str, listing: &Option<String>) {
    if let Some(listing) = listing {
        eprintln!("\n===== RVM assembly for '{}' =====", case_note);
        eprintln!("{}", listing);
        eprintln!("===== End RVM assembly =====\n");
    }
}

macro_rules! panic_with_listing {
    ($listing:expr, $case_note:expr, $($arg:tt)*) => {{
        dump_rvm_listing($case_note, $listing);
        panic!($($arg)*);
    }};
}

macro_rules! bail_with_listing {
    ($listing:expr, $case_note:expr, $($arg:tt)*) => {{
        dump_rvm_listing($case_note, $listing);
        anyhow::bail!($($arg)*);
    }};
}

fn should_run_test_case(case_note: &str) -> bool {
    if let Ok(filter) = std::env::var("TEST_CASE_FILTER") {
        case_note.contains(&filter)
    } else {
        true
    }
}

fn compile_and_run_rvm(
    compiled_policy: &CompiledPolicy,
    entrypoint: &str,
    data: &Value,
    input: &Value,
    listing_out: &mut Option<String>,
    execution_options: &RvmExecutionOptions,
) -> anyhow::Result<Value> {
    let results = compile_and_run_rvm_with_all_entry_points(
        compiled_policy,
        &[entrypoint],
        data,
        input,
        listing_out,
        execution_options,
    )?;
    results
        .into_iter()
        .next()
        .ok_or_else(|| anyhow::anyhow!("no result returned from VM"))
}

fn compile_and_run_rvm_with_entry_points(
    compiled_policy: &CompiledPolicy,
    entry_points: &[&str],
    execute_entry_point: &str,
    data: &Value,
    input: &Value,
    listing_out: &mut Option<String>,
    execution_options: &RvmExecutionOptions,
) -> anyhow::Result<Value> {
    let results = compile_and_run_rvm_with_all_entry_points(
        compiled_policy,
        entry_points,
        data,
        input,
        listing_out,
        execution_options,
    )?;

    if let Some(index) = entry_points
        .iter()
        .position(|ep| *ep == execute_entry_point)
    {
        results
            .get(index)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("missing entry point result"))
    } else {
        Err(anyhow::anyhow!(
            "entry point '{}' not found in {:?}",
            execute_entry_point,
            entry_points
        ))
    }
}

fn compile_and_run_rvm_with_all_entry_points(
    compiled_policy: &CompiledPolicy,
    entry_points: &[&str],
    data: &Value,
    input: &Value,
    listing_out: &mut Option<String>,
    execution_options: &RvmExecutionOptions,
) -> anyhow::Result<Vec<Value>> {
    let ha_builtins = execution_options
        .host_await_builtins
        .as_ref()
        .map(|b| b.iter().map(|(n, a)| (n.as_str(), *a)).collect::<Vec<_>>())
        .unwrap_or_default();
    let program =
        Compiler::compile_from_policy_with_host_await(compiled_policy, entry_points, &ha_builtins)?;

    // Basic serialization sanity check keeps regressions visible in CI.
    test_round_trip_serialization(program.as_ref()).map_err(|e| anyhow::anyhow!(e))?;

    *listing_out = Some(render_program_listing(program.as_ref()));

    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(data.clone())?;
    vm.set_input(input.clone());

    if execution_options.execution_mode == ExecutionMode::Suspendable {
        vm.set_execution_mode(ExecutionMode::Suspendable);
    }

    if execution_options.execution_mode == ExecutionMode::RunToCompletion {
        if let Some(responses) = &execution_options.host_await_responses_run_to_completion {
            vm.set_host_await_responses(responses.clone());
        }
    }

    let mut results = Vec::new();
    for (idx, _) in entry_points.iter().enumerate() {
        let result = if execution_options.execution_mode == ExecutionMode::Suspendable {
            let mut suspendable_responses = execution_options
                .host_await_responses_suspendable
                .clone()
                .unwrap_or_default();
            let _ = if entry_points.len() == 1 {
                vm.execute()?
            } else {
                vm.execute_entry_point_by_index(idx)?
            };

            loop {
                match vm.execution_state() {
                    ExecutionState::Completed { result } => break result.clone(),
                    ExecutionState::Error { error } => {
                        return Err(anyhow::anyhow!("{}", error));
                    }
                    ExecutionState::Suspended { reason, .. } => match reason {
                        SuspendReason::HostAwait {
                            identifier,
                            argument,
                            ..
                        } => {
                            let (expected_args, response) = suspendable_responses
                                .get_mut(identifier)
                                .and_then(|queue| queue.pop_front())
                                .ok_or_else(|| {
                                    anyhow::anyhow!(
                                        "Missing HostAwait response for identifier {:?}",
                                        identifier
                                    )
                                })?;
                            if let Some(expected) = expected_args {
                                // `argument` is already a runtime `Value`; the
                                // expected side has been through `process_value`
                                // once at YAML decode time (see
                                // `build_host_await_response_map`). Comparing
                                // raw runtime values keeps fixture sentinels like
                                // "#undefined" from coercing a runtime string
                                // payload into a different shape, which would
                                // otherwise let tests pass for the wrong reason.
                                if argument != &expected {
                                    return Err(anyhow::anyhow!(
                                        "HostAwait argument mismatch for {:?}: expected {:?}, got {:?}",
                                        identifier,
                                        expected,
                                        argument
                                    ));
                                }
                            }
                            vm.resume(Some(response))?;
                        }
                        other => {
                            return Err(anyhow::anyhow!(
                                "Unexpected suspension reason: {:?}",
                                other
                            ));
                        }
                    },
                    ExecutionState::Running | ExecutionState::Ready => {
                        return Err(anyhow::anyhow!("VM stuck in running state"));
                    }
                }
            }
        } else if entry_points.len() == 1 {
            vm.execute()?
        } else {
            vm.execute_entry_point_by_index(idx)?
        };
        results.push(result);
    }

    Ok(results)
}

fn yaml_test_impl(file: &str) -> Result<()> {
    let yaml_str = fs::read_to_string(file)?;
    let test: YamlTest = yaml_serde::from_str(&yaml_str)?;

    println!("running {file}");
    if let Ok(filter) = std::env::var("TEST_CASE_FILTER") {
        println!("🔍 Test case filter active: '{filter}'");
    }

    let mut executed_count = 0usize;
    let mut skipped_count = 0usize;

    for case in test.cases {
        let mut last_listing: Option<String> = None;
        if !should_run_test_case(&case.note) {
            println!("case {} filtered out", case.note);
            skipped_count += 1;
            continue;
        }

        print!("case {} ", case.note);

        if case.skip == Some(true) {
            println!("skipped");
            skipped_count += 1;
            continue;
        }

        executed_count += 1;

        let mut engine = Engine::new();
        engine.set_rego_v0(case.rego_v0 == Some(true));
        for (idx, module) in case.modules.iter().enumerate() {
            engine.add_policy(format!("rego_{idx}"), module.clone())?;
        }

        if let Some(ref data) = case.data {
            engine.add_data(data.clone())?;
        }

        let input_value = case
            .input
            .clone()
            .map(|i| match i {
                ValueOrVec::Single(v) => v,
                ValueOrVec::Many(_) => Value::Null,
            })
            .unwrap_or(Value::Null);

        if case.input.is_some() {
            engine.set_input(input_value.clone());
        }

        let entrypoint_ref = Rc::from(case.query.as_str());
        let compilation_result = engine.compile_with_entrypoint(&entrypoint_ref);
        let data = engine.get_data();
        let interpreter_result = if case.skip_interpreter == Some(true) {
            None
        } else {
            Some(engine.eval_rule(case.query.clone()))
        };

        let execution_options = match build_execution_options(&case) {
            Ok(options) => options,
            Err(options_error) => {
                // A malformed host-await fixture (e.g. an `args:` expectation on
                // a run-to-completion response, which can never be validated) is
                // reported here. Mirror the compilation-error handling below: if
                // the case expects an error, match it; otherwise fail hard.
                if let (None, Some(expected_error)) = (&case.want_result, &case.want_error) {
                    let error_str = options_error.to_string();
                    if error_str.contains(expected_error) {
                        println!(
                            "✓ Execution-options error matches expected for case '{}'",
                            case.note
                        );
                        println!("passed");
                        continue;
                    }
                    panic_with_listing!(
                        &last_listing,
                        &case.note,
                        "Execution-options error does not match expected for case '{}':\nExpected: '{expected_error}'\nActual: '{error_str}'",
                        case.note
                    );
                }
                dump_rvm_listing(&case.note, &last_listing);
                return Err(options_error);
            }
        };

        if let Err(compilation_error) = &compilation_result {
            if let (None, Some(expected_error)) = (&case.want_result, &case.want_error) {
                let error_str = compilation_error.to_string();
                if error_str.contains(expected_error) {
                    println!(
                        "✓ RVM compilation error matches expected for case '{}'",
                        case.note
                    );
                    println!("passed");
                    continue;
                }

                panic_with_listing!(
                    &last_listing,
                    &case.note,
                    "RVM compilation error does not match expected for case '{}':\nExpected: '{expected_error}'\nActual: '{error_str}'",
                    case.note
                );
            }

            dump_rvm_listing(&case.note, &last_listing);
            return Err(anyhow::anyhow!("Compilation failed: {compilation_error}"));
        }

        let compiled_policy = compilation_result.unwrap();

        if let Some(expected_results) = &case.want_results {
            if case.want_result.is_some() {
                bail_with_listing!(
                    &last_listing,
                    &case.note,
                    "Cannot specify both want_result and want_results for case '{}'",
                    case.note
                );
            }
            if case.want_error.is_some() {
                bail_with_listing!(
                    &last_listing,
                    &case.note,
                    "Cannot specify both want_results and want_error for case '{}'",
                    case.note
                );
            }

            if let Some(ref entry_points) = case.entry_points {
                let entry_point_refs: Vec<&str> = entry_points.iter().map(|s| s.as_str()).collect();
                match compile_and_run_rvm_with_all_entry_points(
                    &compiled_policy,
                    &entry_point_refs,
                    &data,
                    &input_value,
                    &mut last_listing,
                    &execution_options,
                ) {
                    Ok(actual_results) => {
                        if actual_results.len() != expected_results.len() {
                            bail_with_listing!(
                                &last_listing,
                                &case.note,
                                "Expected {} results, but got {} for case '{}'",
                                expected_results.len(),
                                actual_results.len(),
                                case.note
                            );
                        }

                        for (index, (actual, expected)) in actual_results
                            .iter()
                            .zip(expected_results.iter())
                            .enumerate()
                        {
                            let expected_value = match expected {
                                ValueOrVec::Single(v) => v.clone(),
                                ValueOrVec::Many(vec) if vec.len() == 1 => vec[0].clone(),
                                ValueOrVec::Many(_) => {
                                    bail_with_listing!(
                                        &last_listing,
                                        &case.note,
                                        "Unexpected multiple expected values for result {} in case '{}'",
                                        index,
                                        case.note
                                    );
                                }
                            };

                            let processed_expected = process_value(&expected_value)?;
                            if *actual != processed_expected {
                                bail_with_listing!(
                                    &last_listing,
                                    &case.note,
                                    "Result {} mismatch for case '{}': expected {:?}, got {:?}",
                                    index,
                                    case.note,
                                    processed_expected,
                                    actual
                                );
                            }
                        }

                        println!(
                            "✓ All {} entry point results match expected values for case '{}'",
                            actual_results.len(),
                            case.note
                        );
                        continue;
                    }
                    Err(e) => {
                        bail_with_listing!(
                            &last_listing,
                            &case.note,
                            "Multiple entry points execution failed for case '{}': {}",
                            case.note,
                            e
                        );
                    }
                }
            } else {
                bail_with_listing!(
                    &last_listing,
                    &case.note,
                    "want_results specified but no entry_points provided for case '{}'",
                    case.note
                );
            }
        }

        match (&case.want_result, &case.want_error) {
            (Some(expected_result), None) => {
                let result = if let Some(ref entry_points) = case.entry_points {
                    let refs: Vec<&str> = entry_points.iter().map(|s| s.as_str()).collect();
                    compile_and_run_rvm_with_entry_points(
                        &compiled_policy,
                        &refs,
                        &case.query,
                        &data,
                        &input_value,
                        &mut last_listing,
                        &execution_options,
                    )
                } else {
                    compile_and_run_rvm(
                        &compiled_policy,
                        &case.query,
                        &data,
                        &input_value,
                        &mut last_listing,
                        &execution_options,
                    )
                };

                match result {
                    Ok(actual_result) => {
                        if let Some(interpreter_result) = &interpreter_result {
                            match interpreter_result {
                                Ok(interpreter_value) => {
                                    if actual_result != *interpreter_value {
                                        if case.allow_interpreter_incorrect_behavior == Some(true) {
                                            println!(
                                                "✓ RVM result differs from interpreter for case '{}' (allowed)",
                                                case.note
                                            );
                                        } else {
                                            panic_with_listing!(
                                                &last_listing,
                                                &case.note,
                                                "RVM result does not match interpreter result for case '{}':\nRVM: {:?}\nInterpreter: {:?}",
                                                case.note,
                                                actual_result,
                                                interpreter_value
                                            );
                                        }
                                    }
                                }
                                Err(err) => {
                                    if case.allow_interpreter_incorrect_behavior == Some(true) {
                                        println!(
                                            "✓ Interpreter failed for case '{}' but RVM succeeded (allowed): {}",
                                            case.note,
                                            err
                                        );
                                    } else {
                                        panic_with_listing!(
                                            &last_listing,
                                            &case.note,
                                            "Interpreter failed for case '{}' but RVM succeeded:\nRVM result: {:?}\nInterpreter error: {}",
                                            case.note,
                                            actual_result,
                                            err
                                        );
                                    }
                                }
                            }
                        }

                        let expected_results = value_or_vec_to_vec(expected_result.clone());
                        let actual_results = vec![actual_result];
                        check_output(&actual_results, &expected_results)?;
                    }
                    Err(e) => match &interpreter_result {
                        Some(Ok(interpreter_value)) => {
                            if case.allow_interpreter_success == Some(true) {
                                println!(
                                    "✓ RVM detected conflict for case '{}' (interpreter success allowed): {}",
                                    case.note,
                                    e
                                );
                            } else {
                                panic_with_listing!(
                                    &last_listing,
                                    &case.note,
                                    "RVM failed for case '{}' but interpreter succeeded:\nRVM error: {}\nInterpreter result: {:?}",
                                    case.note,
                                    e,
                                    interpreter_value
                                );
                            }
                        }
                        Some(Err(err)) => {
                            panic_with_listing!(
                                &last_listing,
                                &case.note,
                                "Both RVM and interpreter failed for case '{}' but a result was expected:\nInterpreter error: {:?}\nRVM error: {}",
                                case.note,
                                err,
                                e
                            );
                        }
                        None => {
                            panic_with_listing!(
                                &last_listing,
                                &case.note,
                                "RVM failed for case '{}' but a result was expected:\nRVM error: {}",
                                case.note,
                                e
                            );
                        }
                    },
                }
            }
            (None, Some(expected_error)) => {
                let result = if let Some(ref entry_points) = case.entry_points {
                    let refs: Vec<&str> = entry_points.iter().map(|s| s.as_str()).collect();
                    compile_and_run_rvm_with_entry_points(
                        &compiled_policy,
                        &refs,
                        &case.query,
                        &data,
                        &input_value,
                        &mut last_listing,
                        &execution_options,
                    )
                } else {
                    compile_and_run_rvm(
                        &compiled_policy,
                        &case.query,
                        &data,
                        &input_value,
                        &mut last_listing,
                        &execution_options,
                    )
                };

                match result {
                    Ok(result) => match &interpreter_result {
                        Some(Ok(interpreter_value)) => {
                            panic_with_listing!(
                                &last_listing,
                                &case.note,
                                "Test case '{}' expected error '{}' but both RVM and interpreter succeeded:\nRVM result: {}\nInterpreter result: {:?}",
                                case.note,
                                expected_error,
                                serde_json::to_string_pretty(&result)?,
                                interpreter_value
                            );
                        }
                        Some(Err(_)) => {
                            panic_with_listing!(
                                &last_listing,
                                &case.note,
                                "Test case '{}' expected error '{}' but RVM succeeded while interpreter failed:\nRVM result: {}",
                                case.note,
                                expected_error,
                                serde_json::to_string_pretty(&result)?
                            );
                        }
                        None => {
                            panic_with_listing!(
                                &last_listing,
                                &case.note,
                                "Test case '{}' expected error '{}' but RVM succeeded:\nRVM result: {}",
                                case.note,
                                expected_error,
                                serde_json::to_string_pretty(&result)?
                            );
                        }
                    },
                    Err(actual_error) => match &interpreter_result {
                        Some(Ok(interpreter_value)) => {
                            if case.allow_interpreter_success == Some(true) {
                                let actual_error_str = actual_error.to_string();
                                if !actual_error_str.contains(expected_error) {
                                    panic_with_listing!(
                                        &last_listing,
                                        &case.note,
                                        "Error message mismatch for case '{}': expected contains '{}', actual '{}'",
                                        case.note,
                                        expected_error,
                                        actual_error_str
                                    );
                                }
                                println!(
                                    "✓ RVM error matches expected for case '{}' (interpreter success allowed)",
                                    case.note
                                );
                            } else {
                                panic_with_listing!(
                                    &last_listing,
                                    &case.note,
                                    "RVM failed for case '{}' but interpreter succeeded:\nRVM error: {}\nInterpreter result: {:?}",
                                    case.note,
                                    actual_error,
                                    interpreter_value
                                );
                            }
                        }
                        Some(Err(_)) | None => {
                            let actual_error_str = actual_error.to_string();
                            if !actual_error_str.contains(expected_error) {
                                panic_with_listing!(
                                    &last_listing,
                                    &case.note,
                                    "Error message mismatch for case '{}': expected contains '{}', actual '{}'",
                                    case.note,
                                    expected_error,
                                    actual_error_str
                                );
                            }
                            println!("✓ RVM error matches expected for case '{}'", case.note);
                        }
                    },
                }
            }
            _ => {
                panic_with_listing!(
                    &last_listing,
                    &case.note,
                    "Test case '{}' must specify either want_result or want_error",
                    case.note
                );
            }
        }

        println!("passed");
    }

    println!(
        "📊 Test Summary for {}: {} executed, {} skipped",
        file, executed_count, skipped_count
    );

    Ok(())
}

#[test]
fn namespace_entrypoint_roundtrips_and_reuses_vm_state() -> Result<()> {
    let entrypoint = "data.graph.defUniqueName[\"1.0.0\"].deny";
    let mut engine = Engine::new();
    engine.add_policy(
        "namespace.rego".to_string(),
        r#"
        package graph.defUniqueName["1.0.0"]

        default deny := false
        deny := true if { input.blocked == true }
        "#
        .to_string(),
    )?;
    let entrypoint_ref: Rc<str> = entrypoint.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint_ref)?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;

    let json = program.serialize_json().map_err(anyhow::Error::msg)?;
    let json_program = Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;
    let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
    let binary_program = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => program,
        DeserializationResult::Partial(_) => {
            anyhow::bail!("binary namespace program unexpectedly needs recompilation")
        }
    };

    for (program, mode) in [
        (json_program, ExecutionMode::RunToCompletion),
        (binary_program, ExecutionMode::Suspendable),
    ] {
        let mut vm = RegoVM::new();
        vm.load_program(Arc::new(program));
        vm.set_data(Value::new_object())?;
        vm.set_execution_mode(mode);

        vm.set_input(Value::from_json_str(r#"{"blocked":true}"#)?);
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            Value::Bool(true)
        );

        vm.set_input(Value::from_json_str(r#"{"blocked":false}"#)?);
        assert_eq!(vm.execute_entry_point_by_index(0)?, Value::Bool(false));

        vm.set_input(Value::Undefined);
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            Value::Bool(false)
        );
    }

    Ok(())
}

#[test]
fn numeric_namespace_selectors_keep_string_identity_on_reused_vm() -> Result<()> {
    let entrypoint = "data.consumer.result";
    let mut engine = Engine::new();
    engine.add_data(Value::from_json_str(
        r#"{"graph":{"1":{"extra":9},"1.0":{"extra":90}}}"#,
    )?)?;
    engine.add_policy(
        "namespace.rego".to_string(),
        r#"
        package graph["1"]
        value := 7
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "decimal_namespace.rego".to_string(),
        r#"
        package graph["1.0"]
        value := 70
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        result := data.graph[input.selector]
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let cases = [
        (r#"{"selector":"1"}"#, r#"{"extra":9,"value":7}"#),
        (r#"{"selector":1}"#, r#"{"extra":9,"value":7}"#),
        (r#"{"selector":1.0}"#, r#"{"extra":9,"value":7}"#),
        (r#"{"selector":"1.0"}"#, r#"{"extra":90,"value":70}"#),
        (r#"{"selector":1.0}"#, r#"{"extra":9,"value":7}"#),
        (r#"{"selector":"1"}"#, r#"{"extra":9,"value":7}"#),
        (r#"{"selector":"1.0"}"#, r#"{"extra":90,"value":70}"#),
    ];

    for (input_json, expected_json) in cases {
        let input = Value::from_json_str(input_json)?;
        let expected = Value::from_json_str(expected_json)?;
        engine.set_input(input);
        assert_eq!(
            engine.eval_rule(entrypoint.to_string())?,
            expected,
            "interpreter result for input {input_json}"
        );
    }

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);

        for (input_json, expected_json) in cases {
            vm.set_input(Value::from_json_str(input_json)?);
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                Value::from_json_str(expected_json)?,
                "{mode:?} result for input {input_json}"
            );
        }
    }

    Ok(())
}

#[test]
fn dynamic_namespace_package_prefetch_matches_in_both_vm_modes() -> Result<()> {
    let entrypoint = "data.framework.allow";
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        default allow := true
        allow := false if {
            cfg := data.config[input.namespace]
            cfg.blocked
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package config.target\nblocked := true".to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let cases = [
        (
            Value::from_json_str(r#"{"namespace":"target"}"#)?,
            Value::Bool(false),
        ),
        (Value::new_object(), Value::Bool(true)),
        (Value::Undefined, Value::Bool(true)),
        (
            Value::from_json_str(r#"{"namespace":"target"}"#)?,
            Value::Bool(false),
        ),
    ];

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);

        for (input, expected) in &cases {
            vm.set_input(input.clone());
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                *expected,
                "{mode:?} result for input {input:?}"
            );
        }
    }

    Ok(())
}

#[test]
fn dynamic_namespace_selected_package_defaults_follow_normal_rules_in_both_vm_modes() -> Result<()>
{
    let entrypoint = "data.framework.allow";

    for default_first in [true, false] {
        let mut engine = Engine::new();
        engine.add_policy(
            "framework.rego".to_string(),
            r#"
            package framework
            default allow := true
            allow := false if {
                cfg := data.config[input.namespace]
                cfg.blocked
            }
            "#
            .to_string(),
        )?;

        let default_policy = "package config.target\ndefault blocked := false".to_string();
        let ordinary_policy = "package config.target\nblocked := true".to_string();
        if default_first {
            engine.add_policy("default.rego".to_string(), default_policy)?;
            engine.add_policy("ordinary.rego".to_string(), ordinary_policy)?;
        } else {
            engine.add_policy("ordinary.rego".to_string(), ordinary_policy)?;
            engine.add_policy("default.rego".to_string(), default_policy)?;
        }

        let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
        let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
        let data = engine.get_data();

        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_data(data.clone())?;
            vm.set_execution_mode(mode);
            vm.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                Value::Bool(false),
                "{mode:?} result with default_first={default_first}"
            );
        }
    }

    Ok(())
}

#[test]
fn dynamic_indexed_defaults_preserve_object_semantics_in_both_vm_modes() -> Result<()> {
    let entrypoint = "data.probe.values";
    let policy = r#"
        package probe
        default values["constant"] := true
        default values["runtime"] := [item | item := input.items[_]]
        values := {"ordinary": "defined"} if input.include_ordinary
    "#;

    let mut compiler_engine = Engine::new();
    compiler_engine.add_policy("probe.rego".to_string(), policy.to_string())?;
    let compiled = compiler_engine.compile_with_entrypoint(&entrypoint.into())?;
    let compiled_program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let binary = compiled_program
        .serialize_binary()
        .map_err(anyhow::Error::msg)?;
    assert_eq!(u32::from_le_bytes(binary[4..8].try_into().unwrap()), 7);
    let binary_program = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => Arc::new(program),
        DeserializationResult::Partial(_) => anyhow::bail!("indexed-default artifact was partial"),
    };
    let json = binary_program
        .serialize_json()
        .map_err(anyhow::Error::msg)?;
    let json_value: serde_json::Value = serde_json::from_str(&json)?;
    assert_eq!(json_value["version"], 7);
    let program = Arc::new(Program::deserialize_json(&json).map_err(anyhow::Error::msg)?);

    let cases = [
        (
            r#"{"items":["a","b"],"include_ordinary":true}"#,
            r#"{"constant":true,"ordinary":"defined","runtime":["a","b"]}"#,
        ),
        (r#"{"items":[3]}"#, r#"{"constant":true,"runtime":[3]}"#),
    ];

    for (input_json, expected_json) in cases {
        let input = Value::from_json_str(input_json)?;
        let expected = Value::from_json_str(expected_json)?;
        let mut interpreter_engine = Engine::new();
        interpreter_engine.add_policy("probe.rego".to_string(), policy.to_string())?;
        interpreter_engine.set_input(input.clone());
        let interpreter_result = interpreter_engine.eval_rule(entrypoint.to_string())?;
        assert_eq!(
            interpreter_result, expected,
            "interpreter result for {input_json}"
        );

        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_input(input.clone());
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                expected,
                "{mode:?} result for {input_json}"
            );
        }
    }

    Ok(())
}

#[test]
fn literal_indexed_defaults_preserve_multiple_object_keys_in_both_vm_modes() -> Result<()> {
    let entrypoint = "data.probe.values";
    let policy = r#"
        package probe
        default values["first"] := true
        default values["second"] := 2
    "#;

    let mut compiler_engine = Engine::new();
    compiler_engine.add_policy("probe.rego".to_string(), policy.to_string())?;
    let compiled = compiler_engine.compile_with_entrypoint(&entrypoint.into())?;
    let compiled_program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let binary = compiled_program
        .serialize_binary()
        .map_err(anyhow::Error::msg)?;
    assert_eq!(u32::from_le_bytes(binary[4..8].try_into().unwrap()), 7);
    let binary_program = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => Arc::new(program),
        DeserializationResult::Partial(_) => {
            anyhow::bail!("literal indexed-default binary unexpectedly needs recompilation")
        }
    };
    let json = binary_program
        .serialize_json()
        .map_err(anyhow::Error::msg)?;
    let json_value: serde_json::Value = serde_json::from_str(&json)?;
    assert_eq!(json_value["version"], 7);
    let json_program = Arc::new(Program::deserialize_json(&json).map_err(anyhow::Error::msg)?);

    let mut interpreter_engine = Engine::new();
    interpreter_engine.add_policy("probe.rego".to_string(), policy.to_string())?;
    let expected = interpreter_engine.eval_rule(entrypoint.to_string())?;
    assert_eq!(
        expected,
        Value::from_json_str(r#"{"first":true,"second":2}"#)?
    );

    for program in [binary_program, json_program] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                expected,
                "{mode:?} indexed defaults"
            );
        }
    }
    Ok(())
}

#[test]
fn dynamic_default_comprehension_matches_runtime_data_in_both_vm_modes() -> Result<()> {
    let entrypoint = "data.probe.value";
    let default_policy = r#"
        package probe
        other := true
        default value := [x | x := other]
    "#;
    let ordinary_policy = r#"
        package probe
        other := true
        value := [x | x := other]
    "#;

    let run_interpreter = |policy: &str| -> Result<Value> {
        let mut engine = Engine::new();
        engine.add_policy("probe.rego".to_string(), policy.to_string())?;
        engine.set_input(Value::new_object());
        engine.eval_rule(entrypoint.to_string())
    };

    let expected = run_interpreter(ordinary_policy)?;
    assert_eq!(expected, Value::from_json_str("[true]")?);
    assert_eq!(run_interpreter(default_policy)?, expected);

    for compile_data in [
        Value::new_object(),
        Value::from_json_str(r#"{"probe":{"other":false}}"#)?,
    ] {
        let mut engine = Engine::new();
        engine.add_data(compile_data.clone())?;
        engine.add_policy("probe.rego".to_string(), default_policy.to_string())?;
        let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
        let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;

        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_data(Value::new_object())?;
            vm.set_input(Value::new_object());
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                expected,
                "{mode:?} result with compile data {compile_data:?}"
            );
        }
    }

    Ok(())
}

#[test]
fn dynamic_default_reuses_vm_with_changed_runtime_input_and_data() -> Result<()> {
    let entrypoint = "data.probe.value";
    let default_policy = r#"
        package probe
        default value := [item |
            item := data.values[_]
            item >= input.minimum
        ]
    "#;
    let ordinary_policy = r#"
        package probe
        value := [item |
            item := data.values[_]
            item >= input.minimum
        ]
    "#;
    let mut compiler_engine = Engine::new();
    compiler_engine.add_policy("probe.rego".to_string(), default_policy.to_string())?;
    let compiled = compiler_engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;

    let cases = [
        (r#"{"values":[1,2,3]}"#, r#"{"minimum":2}"#),
        (r#"{"values":[4,5]}"#, r#"{"minimum":5}"#),
        (r#"{"values":[]}"#, r#"{"minimum":0}"#),
    ];

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);

        for (data_json, input_json) in cases {
            let data = Value::from_json_str(data_json)?;
            let input = Value::from_json_str(input_json)?;
            let mut interpreter = Engine::new();
            interpreter.add_data(data.clone())?;
            interpreter.add_policy("probe.rego".to_string(), ordinary_policy.to_string())?;
            interpreter.set_input(input.clone());
            let expected = interpreter.eval_rule(entrypoint.to_string())?;

            vm.set_data(data)?;
            vm.set_input(input);
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                expected,
                "{mode:?} result for runtime data {data_json} and input {input_json}"
            );
        }
    }

    Ok(())
}

#[test]
fn undefined_function_argument_does_not_invoke_default_function_fallback() -> Result<()> {
    let entrypoint = "data.probe.result";
    let policy = r#"
        package probe
        default choose(x) := [item | item := true]
        choose(x) := "ordinary" if x == "defined"
        result := choose(input.missing)
    "#;
    let mut interpreter = Engine::new();
    interpreter.add_policy("probe.rego".to_string(), policy.to_string())?;
    interpreter.set_input(Value::new_object());
    let expected = interpreter.eval_rule(entrypoint.to_string())?;
    assert_eq!(expected, Value::Undefined);

    let mut compiler = Engine::new();
    compiler.add_policy("probe.rego".to_string(), policy.to_string())?;
    let compiled = compiler.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(Value::new_object());
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            expected,
            "{mode:?} should not invoke the default function for an Undefined actual argument"
        );
    }

    Ok(())
}

#[test]
fn default_only_functions_are_not_exposed_in_data_namespace_objects() -> Result<()> {
    let entrypoint = "data.probe.namespace";
    let mut engine = Engine::new();
    engine.add_policy(
        "lib.rego".to_string(),
        r#"
        package lib
        default pick(_) := [item | item := true]
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "probe.rego".to_string(),
        r#"
        package probe
        namespace := data.lib
        "#
        .to_string(),
    )?;

    let expected = engine.eval_rule(entrypoint.to_string())?;
    assert_eq!(expected, Value::new_object());

    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            expected,
            "{mode:?} must not expose a default-only function as a data value"
        );
    }

    let callable_entrypoint = "data.lib.result";
    let mut callable_engine = Engine::new();
    callable_engine.add_policy(
        "lib.rego".to_string(),
        r#"
        package lib
        default pick(_) := [item | item := true]
        result := pick("defined")
        "#
        .to_string(),
    )?;
    let callable_compiled = callable_engine.compile_with_entrypoint(&callable_entrypoint.into())?;
    let callable_program =
        Compiler::compile_from_policy(&callable_compiled, &[callable_entrypoint])?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(callable_program.clone());
        vm.set_execution_mode(mode);
        assert_eq!(
            vm.execute_entry_point_by_name(callable_entrypoint)?,
            Value::from_json_str("[true]")?,
            "{mode:?} must retain callable metadata for a default-only function"
        );
    }

    Ok(())
}

#[test]
fn qualified_and_imported_default_only_function_calls_match_interpreter() -> Result<()> {
    type Source<'a> = (&'a str, &'a str);
    type Case<'a> = (&'a str, &'a [Source<'a>], &'a str);

    let cases: [Case<'_>; 3] = [
        (
            "same-package",
            &[(
                "test.rego",
                r#"
                package test
                default pick(_) := [item | item := true]
                result := data.test.pick("defined")
                "#,
            )],
            "data.test.result",
        ),
        (
            "cross-package",
            &[
                (
                    "lib.rego",
                    r#"
                    package lib
                    default pick(_) := [true]
                    "#,
                ),
                (
                    "test.rego",
                    r#"
                    package test
                    result := data.lib.pick("defined")
                    "#,
                ),
            ],
            "data.test.result",
        ),
        (
            "import-alias",
            &[
                (
                    "lib.rego",
                    r#"
                    package lib
                    default pick(_) := [true]
                    "#,
                ),
                (
                    "test.rego",
                    r#"
                    package test
                    import data.lib.pick as pick
                    result := pick("defined")
                    "#,
                ),
            ],
            "data.test.result",
        ),
    ];

    for (case_name, modules, entrypoint) in cases {
        let mut engine = Engine::new();
        for (filename, source) in modules {
            engine.add_policy((*filename).to_string(), (*source).to_string())?;
        }
        let expected = engine.eval_rule(entrypoint.to_string())?;
        assert_eq!(
            expected,
            Value::from_json_str("[true]")?,
            "{case_name}: interpreter function result"
        );

        let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
        let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                expected,
                "{case_name}, {mode:?}: RVM result"
            );
        }
    }

    Ok(())
}

#[test]
fn dynamic_default_errors_match_ordinary_expression_in_both_builtin_modes() -> Result<()> {
    let entrypoint = "data.probe.value";
    let default_policy = r#"
        package probe
        default value := [result | result := 1 / input.divisor]
    "#;
    let ordinary_policy = r#"
        package probe
        value := [result | result := 1 / input.divisor]
    "#;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for strict_builtin_errors in [false, true] {
            let mut outcomes = Vec::new();
            for policy in [default_policy, ordinary_policy] {
                let mut engine = Engine::new();
                engine.add_policy("probe.rego".to_string(), policy.to_string())?;
                let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
                let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
                let mut vm = RegoVM::new();
                vm.load_program(program);
                vm.set_execution_mode(mode);
                vm.set_strict_builtin_errors(strict_builtin_errors);
                vm.set_input(Value::from_json_str(r#"{"divisor":0}"#)?);
                outcomes.push(vm.execute_entry_point_by_name(entrypoint));
            }

            match (&outcomes[0], &outcomes[1]) {
                (Ok(default_value), Ok(ordinary_value)) => {
                    assert_eq!(default_value, ordinary_value);
                }
                (Err(_), Err(_)) => {}
                (default_result, ordinary_result) => panic!(
                    "{mode:?}, strict={strict_builtin_errors}: default outcome {default_result:?} differs from ordinary outcome {ordinary_result:?}"
                ),
            }
        }
    }
    Ok(())
}

#[test]
fn strict_ordinary_errors_do_not_run_dynamic_default_fallback_or_consume_responses() -> Result<()> {
    let entrypoint = "data.probe.value";
    let next_entrypoint = "data.probe.next";
    let policy = r#"
        package probe
        default value := [response | response := __builtin_host_await("fallback", "lookup")]
        value := 1 / input.divisor if input.branch == "ordinary"
        else := 2 / input.divisor if input.branch == "else"
        next := __builtin_host_await("next", "lookup")
    "#;
    let mut engine = Engine::new();
    engine.add_policy("probe.rego".to_string(), policy.to_string())?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint, next_entrypoint])?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for (branch, divisor, should_error) in [
            ("ordinary", 0, true),
            ("else", 0, true),
            ("ordinary", 1, false),
            ("else", 2, false),
        ] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_strict_builtin_errors(true);
            vm.set_input(Value::from_json_str(&format!(
                r#"{{"branch":"{branch}","divisor":{divisor}}}"#
            ))?);
            if mode == ExecutionMode::RunToCompletion {
                vm.set_host_await_responses([(
                    Value::from("lookup"),
                    vec![Value::from("fallback-response")],
                )]);
            }

            let result = vm.execute_entry_point_by_name(entrypoint);
            if should_error {
                assert!(
                    matches!(result, Err(VmError::InvalidDivision { .. })),
                    "{mode:?} strict {branch} division error must be surfaced before the default: {result:?}"
                );
            } else {
                assert_eq!(
                    result?,
                    Value::from_json_str("1")?,
                    "{mode:?} successful {branch} body must remain unchanged"
                );
            }

            if mode == ExecutionMode::RunToCompletion {
                assert_eq!(
                    vm.execute_entry_point_by_name(next_entrypoint)?,
                    Value::from("fallback-response"),
                    "the {branch} result must not consume the queued default response"
                );
            } else {
                vm.execute_entry_point_by_name(next_entrypoint)?;
                assert!(matches!(
                    vm.execution_state(),
                    ExecutionState::Suspended {
                        reason: SuspendReason::HostAwait { identifier, argument, .. },
                        ..
                    } if identifier == &Value::from("lookup") && argument == &Value::from("next")
                ));
                assert_eq!(
                    vm.resume(Some(Value::from("reused-response")))?,
                    Value::from("reused-response")
                );
            }
        }
    }
    Ok(())
}

#[test]
fn non_strict_ordinary_errors_still_run_dynamic_default_and_consume_responses() -> Result<()> {
    let entrypoint = "data.probe.value";
    let next_entrypoint = "data.probe.next";
    let policy = r#"
        package probe
        default value := [response | response := __builtin_host_await("fallback", "lookup")]
        value := 1 / input.divisor if input.branch == "ordinary"
        else := 2 / input.divisor if input.branch == "else"
        next := __builtin_host_await("next", "lookup")
    "#;
    let mut engine = Engine::new();
    engine.add_policy("probe.rego".to_string(), policy.to_string())?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint, next_entrypoint])?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_strict_builtin_errors(false);
        vm.set_input(Value::from_json_str(
            r#"{"branch":"ordinary","divisor":0}"#,
        )?);
        if mode == ExecutionMode::RunToCompletion {
            vm.set_host_await_responses([(
                Value::from("lookup"),
                vec![
                    Value::from("fallback-response"),
                    Value::from("next-response"),
                ],
            )]);
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                Value::from_json_str(r#"["fallback-response"]"#)?,
                "non-strict division must retain its existing default fallback behavior"
            );
            assert_eq!(
                vm.execute_entry_point_by_name(next_entrypoint)?,
                Value::from("next-response"),
                "the non-strict fallback consumes exactly its own response"
            );
        } else {
            vm.execute_entry_point_by_name(entrypoint)?;
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason: SuspendReason::HostAwait { identifier, argument, .. },
                    ..
                } if identifier == &Value::from("lookup") && argument == &Value::from("fallback")
            ));
            assert_eq!(
                vm.resume(Some(Value::from("fallback-response")))?,
                Value::from_json_str(r#"["fallback-response"]"#)?,
            );
            vm.execute_entry_point_by_name(next_entrypoint)?;
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason: SuspendReason::HostAwait { identifier, argument, .. },
                    ..
                } if identifier == &Value::from("lookup") && argument == &Value::from("next")
            ));
            assert_eq!(
                vm.resume(Some(Value::from("next-response")))?,
                Value::from("next-response")
            );
        }
    }
    Ok(())
}

#[test]
fn dynamic_default_artifacts_roundtrip_before_host_await_resume_and_vm_reuse() -> Result<()> {
    let entrypoint = "data.probe.value";
    let mut engine = Engine::new();
    engine.add_policy(
        "probe.rego".to_string(),
        r#"
        package probe
        default value := [response |
            response := __builtin_host_await(input.token, "dynamic-default")
        ]
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    assert!(program.has_host_await);

    let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
    let binary_version = u32::from_le_bytes(
        binary
            .get(4..8)
            .ok_or_else(|| anyhow::anyhow!("serialized binary has no version field"))?
            .try_into()
            .map_err(|_| anyhow::anyhow!("invalid version field"))?,
    );
    assert_eq!(binary_version, 7);

    let json = program.serialize_json().map_err(anyhow::Error::msg)?;
    let json_value: serde_json::Value = serde_json::from_str(&json)?;
    assert_eq!(json_value.get("version").and_then(|v| v.as_u64()), Some(7));
    assert!(json_value.get("program").is_some());
    let json_program = Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;
    let binary_program = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => program,
        DeserializationResult::Partial(_) => {
            anyhow::bail!("dynamic-default binary unexpectedly needs recompilation")
        }
    };

    for program in [json_program, binary_program] {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.load_program(Arc::new(program));
        vm.set_data(Value::new_object())?;

        for (token, response) in [("alpha", "first-response"), ("beta", "second-response")] {
            let expected = Value::from_json_str(&format!(r#"["{response}"]"#))?;
            vm.set_input(Value::from_json_str(&format!(r#"{{"token":"{token}"}}"#))?);
            let _ = vm.execute_entry_point_by_name(entrypoint)?;
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason: SuspendReason::HostAwait { identifier, argument, .. },
                    ..
                } if identifier == &Value::from("dynamic-default")
                    && argument == &Value::from(token)
            ));
            vm.resume(Some(Value::from(response)))?;
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Completed { result }
                    if result == &expected
            ));
            assert!(matches!(
                vm.resume(Some(Value::from("duplicate-response"))),
                Err(VmError::InvalidResumeState { .. })
            ));
        }
    }

    Ok(())
}

#[test]
fn dynamic_default_host_await_skip_and_error_cleanup_allow_reuse() -> Result<()> {
    let entrypoint = "data.probe.value";
    let next_entrypoint = "data.probe.next";
    let mut engine = Engine::new();
    engine.add_policy(
        "probe.rego".to_string(),
        r#"
        package probe
        default value := [response |
            response := __builtin_host_await("fallback", "lookup")
        ]
        value := false if input.use_definition
        next := __builtin_host_await("next", "lookup")
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint, next_entrypoint])?;

    let mut rtc_vm = RegoVM::new();
    rtc_vm.load_program(program.clone());
    rtc_vm.set_execution_mode(ExecutionMode::RunToCompletion);
    rtc_vm.set_input(Value::from_json_str(r#"{"use_definition":true}"#)?);
    rtc_vm.set_host_await_responses([(
        Value::from("lookup"),
        vec![Value::from("response-for-next")],
    )]);
    assert_eq!(
        rtc_vm.execute_entry_point_by_name(entrypoint)?,
        Value::Bool(false)
    );
    assert_eq!(
        rtc_vm.execute_entry_point_by_name(next_entrypoint)?,
        Value::from("response-for-next"),
        "skipped dynamic fallback must not consume the next HostAwait response"
    );

    let mut missing_response_vm = RegoVM::new();
    missing_response_vm.load_program(program.clone());
    missing_response_vm.set_execution_mode(ExecutionMode::RunToCompletion);
    missing_response_vm.set_input(Value::new_object());
    assert!(
        matches!(
            missing_response_vm.execute_entry_point_by_name(entrypoint),
            Ok(Value::Undefined)
        ),
        "missing queued responses must retain ordinary RTC rule-failure semantics"
    );
    missing_response_vm.set_host_await_responses([(
        Value::from("lookup"),
        vec![Value::from("reused-after-missing-response")],
    )]);
    assert_eq!(
        missing_response_vm.execute_entry_point_by_name(entrypoint)?,
        Value::from_json_str(r#"["reused-after-missing-response"]"#)?
    );

    let mut limited_vm = RegoVM::new();
    limited_vm.load_program(program.clone());
    limited_vm.set_execution_mode(ExecutionMode::Suspendable);
    limited_vm.set_input(Value::new_object());
    limited_vm.set_max_instructions(usize::MAX);
    limited_vm.execute_entry_point_by_name(entrypoint)?;
    assert!(matches!(
        limited_vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { .. },
            ..
        }
    ));
    limited_vm.set_max_instructions(0);
    assert!(matches!(
        limited_vm.resume(Some(Value::from("limited"))),
        Err(VmError::InstructionLimitExceeded { limit: 0, .. })
    ));
    limited_vm.set_max_instructions(usize::MAX);
    limited_vm.set_input(Value::new_object());
    limited_vm.execute_entry_point_by_name(entrypoint)?;
    assert!(matches!(
        limited_vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { .. },
            ..
        }
    ));
    limited_vm.resume(Some(Value::from("reused-after-limit")))?;
    assert!(matches!(
        limited_vm.execution_state(),
        ExecutionState::Completed { result }
            if result == &Value::from_json_str(r#"["reused-after-limit"]"#)?
    ));

    let mut restarted_vm = RegoVM::new();
    restarted_vm.load_program(program);
    restarted_vm.set_execution_mode(ExecutionMode::Suspendable);
    restarted_vm.set_input(Value::new_object());
    restarted_vm.execute_entry_point_by_name(entrypoint)?;
    assert!(matches!(
        restarted_vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, .. },
            ..
        } if identifier == &Value::from("lookup")
    ));
    restarted_vm.set_input(Value::from_json_str(r#"{"use_definition":true}"#)?);
    assert_eq!(
        restarted_vm.execute_entry_point_by_name(entrypoint)?,
        Value::Bool(false),
        "starting a new execution should abandon the suspended fallback"
    );
    restarted_vm.execute_entry_point_by_name(next_entrypoint)?;
    assert!(matches!(
        restarted_vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, argument, .. },
            ..
        } if identifier == &Value::from("lookup") && argument == &Value::from("next")
    ));
    restarted_vm.resume(Some(Value::from("reused-after-suspended-fallback")))?;
    assert!(matches!(
        restarted_vm.execution_state(),
        ExecutionState::Completed { result }
            if result == &Value::from("reused-after-suspended-fallback")
    ));

    Ok(())
}

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
#[test]
fn dynamic_default_memory_budget_failure_occurs_in_fallback_and_allows_reuse() -> Result<()> {
    use core::num::NonZeroU64;
    use regorus::MemoryBudgetConfig;

    let entrypoint = "data.probe.value";
    let mut engine = Engine::new();
    engine.add_policy(
        "probe.rego".to_string(),
        r#"
        package probe
        default value := [item | item := input.items[_]]
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let default_entry_point = program
        .rule_infos
        .iter()
        .find(|rule_info| rule_info.name == entrypoint)
        .and_then(|rule_info| rule_info.default_entry_point)
        .expect("dynamic default should have an executable entry point");

    let input_json = serde_json::json!({"items": vec![1; 8192]}).to_string();
    let fallback_pc = usize::try_from(default_entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(Value::from_json_str(&input_json)?);
        vm.set_memory_budget_config(Some(MemoryBudgetConfig {
            limit: NonZeroU64::new(4096).expect("nonzero memory budget"),
        }));

        let error = vm
            .execute_entry_point_by_name(entrypoint)
            .expect_err("the dynamic fallback comprehension should exceed its execution budget");
        assert_eq!(
            vm.execution_state(),
            &ExecutionState::Error {
                error: error.clone()
            },
            "{mode:?} should expose the failed execution state"
        );
        match error {
            VmError::MemoryBudgetExceeded {
                budget: 4096, pc, ..
            } => assert!(
                pc >= fallback_pc,
                "{mode:?} memory budget should fail in the fallback, pc={pc}, fallback={fallback_pc}"
            ),
            other => panic!("expected fallback memory-budget failure, got {other:?}"),
        }

        vm.set_memory_budget_config(None);
        vm.set_input(Value::from_json_str(r#"{"items":[1,2,3]}"#)?);
        let expected = Value::from_json_str("[1,2,3]")?;
        let result = vm.execute_entry_point_by_name(entrypoint)?;
        assert_eq!(
            result, expected,
            "{mode:?} VM should be reusable after a fallback budget failure"
        );
        match mode {
            ExecutionMode::RunToCompletion => assert_eq!(
                vm.execution_state(),
                &ExecutionState::Ready,
                "run-to-completion named entry points preserve the Ready-state contract"
            ),
            ExecutionMode::Suspendable => assert_eq!(
                vm.execution_state(),
                &ExecutionState::Completed { result },
                "suspendable VM should finish the reused execution"
            ),
        }
    }
    Ok(())
}

#[test]
fn dynamic_namespace_lookup_does_not_prefetch_a_trailing_sibling_rule() -> Result<()> {
    let entrypoint = "data.framework.result";
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        "package framework\nresult := data[input.namespace].value".to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nvalue := 7\nunrelated := data.framework.result".to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);
        vm.set_input(input.clone());
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            Value::from(7),
            "{mode:?} result"
        );
    }

    Ok(())
}

#[test]
fn dynamic_namespace_lookup_materializes_a_trailing_subpackage_without_parent_siblings(
) -> Result<()> {
    let entrypoint = "data.framework.config";
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        "package framework\nconfig := data[input.namespace].nested".to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nunrelated := data.framework.config".to_string(),
    )?;
    engine.add_policy(
        "nested.rego".to_string(),
        "package target.nested\nvalue := 7".to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    let expected = Value::from_json_str(r#"{"value":7}"#)?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);
        vm.set_input(input.clone());
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            expected,
            "{mode:?} result"
        );
    }

    Ok(())
}

#[test]
fn rvm_compiler_rejects_large_entrypoints_with_many_components() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "base.rego".to_string(),
        "package base\nvalue := true".to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&"data.base.value".into())?;
    let paths = [
        format!("data{}", ".a".repeat(300_000)),
        format!("data{}", r#"["a"]"#.repeat(180_000)),
    ];

    for path in &paths {
        assert!(path.len() < 1024 * 1024);
        assert!(Compiler::compile_from_policy(&compiled, &[path]).is_err());
    }

    Ok(())
}

#[test]
fn numeric_object_selectors_do_not_use_data_namespace_fallback() -> Result<()> {
    let entrypoint = "data.consumer.result";
    let mut engine = Engine::new();
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        result := input.object[input.selector]
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let cases = [
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":"1"}"#,
            Value::String("integer string".into()),
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":1}"#,
            Value::Undefined,
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":1.0}"#,
            Value::Undefined,
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":"1.0"}"#,
            Value::String("decimal string".into()),
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":1.0}"#,
            Value::Undefined,
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":"1"}"#,
            Value::String("integer string".into()),
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":"1.0"}"#,
            Value::String("decimal string".into()),
        ),
    ];

    for (input_json, expected) in &cases {
        engine.set_input(Value::from_json_str(input_json)?);
        let actual = engine.eval_rule(entrypoint.to_string())?;
        assert_eq!(
            &actual, expected,
            "interpreter result for input {input_json}"
        );
    }

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);

        for (input_json, expected) in &cases {
            vm.set_input(Value::from_json_str(input_json)?);
            let actual = vm.execute_entry_point_by_name(entrypoint)?;
            assert_eq!(&actual, expected, "{mode:?} result for input {input_json}");
        }
    }

    Ok(())
}

#[test]
fn bracketed_identifier_entrypoint_roundtrips_and_executes_by_name_and_index() -> Result<()> {
    let requested_entrypoint = "data.graph[\"version\"].value";
    let mut engine = Engine::new();
    engine.add_policy(
        "namespace.rego".to_string(),
        "package graph.version\nvalue := 7".to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&"data.graph.version.value".into())?;
    for invalid_entrypoint in [
        "data.graph[1].value",
        "data.graph.version.value trailing",
        "data.graph.missing.value",
    ] {
        assert!(Compiler::compile_from_policy(&compiled, &[invalid_entrypoint]).is_err());
    }
    let program = Compiler::compile_from_policy(&compiled, &[requested_entrypoint])?;

    let json = program.serialize_json().map_err(anyhow::Error::msg)?;
    let json_program = Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;
    let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
    let binary_program = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => program,
        DeserializationResult::Partial(_) => {
            anyhow::bail!("binary identifier program unexpectedly needs recompilation")
        }
    };

    for program in [json_program, binary_program] {
        let mut vm = RegoVM::new();
        vm.load_program(Arc::new(program));
        vm.set_data(Value::new_object())?;
        assert_eq!(
            vm.execute_entry_point_by_name(requested_entrypoint)?,
            Value::from(7)
        );
        assert_eq!(vm.execute_entry_point_by_index(0)?, Value::from(7));
    }

    Ok(())
}

#[test]
fn bracketed_entrypoints_match_dotted_paths_at_supported_depths_and_reuse_vm() -> Result<()> {
    for (package_component_count, rule_component_count) in [(31, 1), (32, 1), (32, 32)] {
        let package_components = (0..package_component_count)
            .map(|index| format!("p{index}"))
            .collect::<Vec<_>>();
        let rule_components = (0..rule_component_count)
            .map(|index| format!("r{index}"))
            .collect::<Vec<_>>();
        let package_path = package_components.join(".");
        let rule_path = rule_components.join(".");
        let dotted_path = format!("data.{package_path}.{rule_path}");
        let mut bracketed_path = String::from("data");
        for component in package_components.iter().chain(&rule_components) {
            bracketed_path.push_str(&format!("[\"{component}\"]"));
        }

        let mut engine = Engine::new();
        engine.add_policy(
            "deep.rego".to_string(),
            format!("package {package_path}\n{rule_path} := 7"),
        )?;
        let dotted_entrypoint: Rc<str> = dotted_path.into();
        let compiled = engine.compile_with_entrypoint(&dotted_entrypoint)?;
        let program = Compiler::compile_from_policy(&compiled, &[bracketed_path.as_str()])?;

        let json = program.serialize_json().map_err(anyhow::Error::msg)?;
        let json_program = Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;
        let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
        let binary_program =
            match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
                DeserializationResult::Complete(program) => program,
                DeserializationResult::Partial(_) => {
                    anyhow::bail!("deep namespace program unexpectedly needs recompilation")
                }
            };

        for (program, mode) in [
            (json_program, ExecutionMode::RunToCompletion),
            (binary_program, ExecutionMode::Suspendable),
        ] {
            let mut vm = RegoVM::new();
            vm.load_program(Arc::new(program));
            vm.set_data(Value::new_object())?;
            vm.set_execution_mode(mode);
            for _ in 0..2 {
                assert_eq!(
                    vm.execute_entry_point_by_name(&bracketed_path)?,
                    Value::from(7),
                    "{mode:?} named path with {package_component_count} package and {rule_component_count} rule components"
                );
                assert_eq!(
                    vm.execute_entry_point_by_index(0)?,
                    Value::from(7),
                    "{mode:?} indexed path with {package_component_count} package and {rule_component_count} rule components"
                );
            }
        }
    }

    Ok(())
}

#[test_resources("tests/rvm/rego/cases/*.yaml")]
fn run_rego_compiler_yaml(file: &str) {
    yaml_test_impl(file).unwrap();
}

#[test]
fn registered_host_await_vm_reuses_after_instruction_limit() -> Result<()> {
    const ENTRYPOINT: &str = "data.demo.result";
    let mut engine = Engine::new();
    engine.add_policy(
        "host-await.rego".to_string(),
        r#"
        package demo
        import rego.v1

        result := echo(input.value, {"nested": input.value})
        "#
        .to_string(),
    )?;
    let entrypoint: Rc<str> = ENTRYPOINT.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let program =
        Compiler::compile_from_policy_with_host_await(&compiled, &[ENTRYPOINT], &[("echo", 2)])?;

    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);
    vm.set_data(engine.get_data())?;
    vm.set_input(Value::from_json_str(r#"{"value":"request"}"#)?);
    vm.set_max_instructions(usize::MAX);

    vm.execute_entry_point_by_name(ENTRYPOINT)?;
    let expected_argument = Value::from_json_str(r#"["request", {"nested":"request"}]"#)?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait {
                identifier,
                argument,
                ..
            },
            ..
        } if identifier == &Value::from("echo") && argument == &expected_argument
    ));

    vm.set_max_instructions(0);
    assert!(matches!(
        vm.resume(Some(Value::from("limited-response"))),
        Err(VmError::InstructionLimitExceeded { limit: 0, .. })
    ));
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Error {
            error: VmError::InstructionLimitExceeded { limit: 0, .. }
        }
    ));

    vm.set_max_instructions(usize::MAX);
    vm.execute_entry_point_by_name(ENTRYPOINT)?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { argument, .. },
            ..
        } if argument == &expected_argument
    ));
    vm.resume(Some(Value::from("host-response")))?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Completed { result } if result == &Value::from("host-response")
    ));

    Ok(())
}

#[test]
fn strict_nested_rule_error_precedes_outer_dynamic_default() -> Result<()> {
    let entrypoint = "data.probe.value";
    let next_entrypoint = "data.probe.next";
    let policy = r#"
        package probe
        default value := [response | response := __builtin_host_await("fallback", "lookup")]
        value := inner(input.divisor)
        inner(divisor) := 1 / divisor
        next := __builtin_host_await("next", "lookup")
    "#;
    let ordinary_control = r#"
        package probe
        value := 1 / input.divisor
    "#;

    // The no-host interpreter/RVM control must surface the same ordinary
    // division error, independent of any outer runtime default.
    let mut interpreter = Engine::new();
    interpreter.add_policy("control.rego".to_string(), ordinary_control.to_string())?;
    interpreter.set_input(Value::from_json_str(r#"{"divisor":0}"#)?);
    interpreter.set_strict_builtin_errors(true);
    assert!(interpreter.eval_rule(entrypoint.to_string()).is_err());

    let mut engine = Engine::new();
    engine.add_policy("probe.rego".to_string(), policy.to_string())?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint, next_entrypoint])?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for strict in [true, false] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_strict_builtin_errors(strict);
            vm.set_input(Value::from_json_str(r#"{"divisor":0}"#)?);
            if mode == ExecutionMode::RunToCompletion {
                vm.set_host_await_responses([(
                    Value::from("lookup"),
                    vec![Value::from("fallback-queued"), Value::from("next-queued")],
                )]);
            }

            let result = vm.execute_entry_point_by_name(entrypoint);
            if strict {
                assert!(
                    matches!(result, Err(VmError::InvalidDivision { .. })),
                    "{mode:?} strict nested division should reach the caller, not its default: {result:?}"
                );
                if mode == ExecutionMode::RunToCompletion {
                    assert_eq!(
                        vm.execute_entry_point_by_name(next_entrypoint)?,
                        Value::from("fallback-queued"),
                        "strict error must not consume the default HostAwait response"
                    );
                } else {
                    vm.execute_entry_point_by_name(next_entrypoint)?;
                    assert!(
                        matches!(
                            vm.execution_state(),
                            ExecutionState::Suspended {
                                reason: SuspendReason::HostAwait { identifier, argument, .. },
                                ..
                            } if identifier == &Value::from("lookup") && argument == &Value::from("next")
                        ),
                        "strict failure must leave no pending fallback HostAwait"
                    );
                    assert_eq!(
                        vm.resume(Some(Value::from("next-response")))?,
                        Value::from("next-response")
                    );
                }
            } else if mode == ExecutionMode::RunToCompletion {
                assert_eq!(
                    result?,
                    Value::from_json_str(r#"["fallback-queued"]"#)?,
                    "non-strict nested division keeps its existing fallback behavior"
                );
                assert_eq!(
                    vm.execute_entry_point_by_name(next_entrypoint)?,
                    Value::from("next-queued"),
                    "non-strict fallback consumes exactly its own response"
                );
            } else {
                assert!(matches!(
                    vm.execution_state(),
                    ExecutionState::Suspended {
                        reason: SuspendReason::HostAwait { identifier, argument, .. },
                        ..
                    } if identifier == &Value::from("lookup") && argument == &Value::from("fallback")
                ));
                assert_eq!(
                    vm.resume(Some(Value::from("fallback-response")))?,
                    Value::from_json_str(r#"["fallback-response"]"#)?
                );
                vm.execute_entry_point_by_name(next_entrypoint)?;
                assert!(matches!(
                    vm.execution_state(),
                    ExecutionState::Suspended {
                        reason: SuspendReason::HostAwait { identifier, argument, .. },
                        ..
                    } if identifier == &Value::from("lookup") && argument == &Value::from("next")
                ));
                assert_eq!(
                    vm.resume(Some(Value::from("next-response")))?,
                    Value::from("next-response")
                );
            }
        }
    }

    Ok(())
}

#[test]
fn suspendable_virtual_namespace_defaults_resume_once_and_cache_completed_subtree() -> Result<()> {
    let entrypoint = "data.consumer.result";
    let mut engine = Engine::new();
    engine.add_policy(
        "lib.rego".to_string(),
        r#"
        package lib
        default first := [response | response := __builtin_host_await(input.first_payload, "first")]
        default second := [response | response := __builtin_host_await(input.second_payload, "second")]
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        result := [data.lib, data.lib]
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let expected = Value::from_json_str(
        r#"[{"first":["response-first"],"second":["response-second"]},{"first":["response-first"],"second":["response-second"]}]"#,
    )?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);
        vm.set_input(Value::from_json_str(
            r#"{"first_payload":"first-arg","second_payload":"second-arg"}"#,
        )?);

        if mode == ExecutionMode::RunToCompletion {
            vm.set_host_await_responses([
                (Value::from("first"), vec![Value::from("response-first")]),
                (Value::from("second"), vec![Value::from("response-second")]),
            ]);
            assert_eq!(vm.execute_entry_point_by_name(entrypoint)?, expected);
            continue;
        }

        let initial = vm.execute_entry_point_by_name(entrypoint);
        assert!(
            initial.is_ok(),
            "namespace lookup should suspend rather than fail: {initial:?}"
        );
        let mut seen = Vec::new();
        for _ in 0..2 {
            let (identifier, argument) = match vm.execution_state().clone() {
                ExecutionState::Suspended {
                    reason:
                        SuspendReason::HostAwait {
                            identifier,
                            argument,
                            ..
                        },
                    ..
                } => (identifier, argument),
                other => panic!("expected the next namespace leaf to suspend, got {other:?}"),
            };
            assert!(
                !seen.contains(&identifier),
                "a completed namespace leaf must not be re-executed: {identifier:?}"
            );
            let (expected_argument, response) = if identifier == Value::from("first") {
                (Value::from("first-arg"), Value::from("response-first"))
            } else if identifier == Value::from("second") {
                (Value::from("second-arg"), Value::from("response-second"))
            } else {
                panic!("unexpected namespace HostAwait identifier: {identifier:?}");
            };
            assert_eq!(argument, expected_argument);
            seen.push(identifier);
            let _ = vm.resume(Some(response))?;
        }
        assert_eq!(seen.len(), 2);
        assert!(seen.contains(&Value::from("first")));
        assert!(seen.contains(&Value::from("second")));
        assert!(
            matches!(
                vm.execution_state(),
                ExecutionState::Completed { result } if result == &expected
            ),
            "completed namespace result mismatch: {:?}",
            vm.execution_state()
        );
        assert!(
            vm.get_cache_hits() > 0,
            "repeated namespace lookup should use the completed-child cache"
        );
    }

    Ok(())
}

#[test]
fn suspendable_dynamic_numeric_namespace_leaf_preserves_path_suffix_and_registers() -> Result<()> {
    let entrypoint = "data.consumer.result";
    let mut engine = Engine::new();
    engine.add_data(Value::from_json_str(r#"{"graph":{"1":{"extra":"base"}}}"#)?)?;
    engine.add_policy(
        "numeric.rego".to_string(),
        r#"
        package graph["1"]
        default value := [response | response := __builtin_host_await(input.payload, "numeric-leaf")]
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        result := [data.graph[input.selector].value[input.index], input.marker]
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let input =
        Value::from_json_str(r#"{"selector":1,"index":0,"marker":"kept","payload":"payload"}"#)?;
    let expected = Value::from_json_str(r#"["resolved-value","kept"]"#)?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);
        vm.set_input(input.clone());
        if mode == ExecutionMode::RunToCompletion {
            vm.set_host_await_responses([(
                Value::from("numeric-leaf"),
                vec![Value::from("resolved-value")],
            )]);
            assert_eq!(vm.execute_entry_point_by_name(entrypoint)?, expected);
            continue;
        }

        let initial = vm.execute_entry_point_by_name(entrypoint);
        assert!(
            initial.is_ok(),
            "dynamic numeric namespace lookup should suspend: {initial:?}"
        );
        assert!(matches!(
            vm.execution_state(),
            ExecutionState::Suspended {
                reason: SuspendReason::HostAwait { identifier, argument, .. },
                ..
            } if identifier == &Value::from("numeric-leaf") && argument == &Value::from("payload")
        ));
        assert_eq!(vm.resume(Some(Value::from("resolved-value")))?, expected);
    }

    Ok(())
}

#[test]
fn suspendable_virtual_namespace_restart_and_instruction_limit_error_allow_reuse() -> Result<()> {
    let entrypoint = "data.consumer.namespace";
    let next_entrypoint = "data.consumer.next";
    let mut engine = Engine::new();
    engine.add_policy(
        "lib.rego".to_string(),
        r#"
        package lib
        default value := [response | response := __builtin_host_await(input.payload, "lookup")]
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        namespace := data.lib
        next := __builtin_host_await(input.next_payload, "next")
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint, next_entrypoint])?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(engine.get_data())?;
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.set_max_instructions(usize::MAX);
    vm.set_input(Value::from_json_str(
        r#"{"payload":"namespace-payload","next_payload":"fresh-payload"}"#,
    )?);

    let initial = vm.execute_entry_point_by_name(entrypoint);
    assert!(
        initial.is_ok(),
        "virtual namespace should suspend: {initial:?}"
    );
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, argument, .. },
            ..
        } if identifier == &Value::from("lookup") && argument == &Value::from("namespace-payload")
    ));

    // Starting another entry point abandons the previous suspended continuation.
    vm.execute_entry_point_by_name(next_entrypoint)?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, argument, .. },
            ..
        } if identifier == &Value::from("next") && argument == &Value::from("fresh-payload")
    ));
    assert_eq!(
        vm.resume(Some(Value::from("fresh-response")))?,
        Value::from("fresh-response")
    );

    vm.execute_entry_point_by_name(entrypoint)?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, argument, .. },
            ..
        } if identifier == &Value::from("lookup") && argument == &Value::from("namespace-payload")
    ));
    vm.set_max_instructions(0);
    assert!(matches!(
        vm.resume(Some(Value::from("limited-response"))),
        Err(VmError::InstructionLimitExceeded { limit: 0, .. })
    ));

    vm.set_max_instructions(usize::MAX);
    vm.execute_entry_point_by_name(entrypoint)?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, .. },
            ..
        } if identifier == &Value::from("lookup")
    ));
    assert_eq!(
        vm.resume(Some(Value::from("reused-response")))?,
        Value::from_json_str(r#"{"value":["reused-response"]}"#)?
    );

    Ok(())
}

#[test]
fn suspendable_virtual_namespace_error_after_completed_child_does_not_run_outer_default(
) -> Result<()> {
    let entrypoint = "data.consumer.namespace";
    let fallback_entrypoint = "data.consumer.fallback_probe";
    let mut engine = Engine::new();
    engine.add_policy(
        "lib.rego".to_string(),
        r#"
        package lib
        default first := [response | response := __builtin_host_await("first-payload", "first")]
        second := 1 / input.divisor
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        default namespace := [response | response := __builtin_host_await("fallback-payload", "fallback")]
        namespace := data.lib
        fallback_probe := __builtin_host_await("probe-payload", "fallback")
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint, fallback_entrypoint])?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(engine.get_data())?;
    vm.set_strict_builtin_errors(true);
    vm.set_max_instructions(usize::MAX);
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.set_input(Value::from_json_str(r#"{"divisor":0}"#)?);

    let initial = vm.execute_entry_point_by_name(entrypoint);
    assert!(
        initial.is_ok(),
        "first virtual leaf should suspend: {initial:?}"
    );
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, .. },
            ..
        } if identifier == &Value::from("first")
    ));
    assert!(matches!(
        vm.resume(Some(Value::from("first-response"))),
        Err(VmError::InvalidDivision { .. })
    ), "strict child error must propagate through the virtual lookup, not execute the outer default");

    vm.execute_entry_point_by_name(fallback_entrypoint)?;
    assert!(
        matches!(
            vm.execution_state(),
            ExecutionState::Suspended {
                reason: SuspendReason::HostAwait { identifier, argument, .. },
                ..
            } if identifier == &Value::from("fallback") && argument == &Value::from("probe-payload")
        ),
        "the failed lookup must not leave a stale fallback HostAwait"
    );
    assert_eq!(
        vm.resume(Some(Value::from("probe-response")))?,
        Value::from("probe-response")
    );

    vm.set_input(Value::from_json_str(r#"{"divisor":1}"#)?);
    vm.execute_entry_point_by_name(entrypoint)?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, .. },
            ..
        } if identifier == &Value::from("first")
    ));
    assert_eq!(
        vm.resume(Some(Value::from("reused-first")))?,
        Value::from_json_str(r#"{"first":["reused-first"],"second":1}"#)?
    );

    Ok(())
}

#[test]
fn test_specific_case() {
    if std::env::var("TEST_CASE_FILTER").is_err() {
        println!("💡 Specific case test skipped - no TEST_CASE_FILTER set");
        println!("   Usage: TEST_CASE_FILTER=\"note substring\" cargo test test_specific_case -- --nocapture");
        return;
    }

    if let Ok(entries) = fs::read_dir("tests/rvm/rego/cases") {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("yaml") {
                if let Err(e) = yaml_test_impl(path.to_str().unwrap()) {
                    println!("❌ Error in file {}: {}", path.display(), e);
                }
            }
        }
    }
}

#[test]
fn virtual_namespace_subtree_restores_parent_path_after_awaited_child() -> Result<()> {
    let entrypoint = "data.consumer.result";
    let first_modules = [
        (
            "nested.rego",
            r#"
            package lib.a.b
            default x := [response | response := __builtin_host_await("leaf-payload", "leaf")]
            empty := {}
            "#,
        ),
        (
            "sibling.rego",
            r#"
            package lib
            z := 1
            "#,
        ),
        (
            "consumer.rego",
            r#"
            package consumer
            result := [data.lib, data.lib]
            "#,
        ),
    ];
    let second_modules = [
        (
            "sibling.rego",
            r#"
            package lib
            a := {}
            "#,
        ),
        (
            "nested.rego",
            r#"
            package lib.z.b
            default x := [response | response := __builtin_host_await("leaf-payload", "leaf")]
            empty := {}
            "#,
        ),
        (
            "consumer.rego",
            r#"
            package consumer
            result := [data.lib, data.lib]
            "#,
        ),
    ];
    let cases = [
        (
            "nested child before parent sibling",
            &first_modules[..],
            r#"[{"a":{"b":{"empty":{},"x":["first-response"]}},"z":1},{"a":{"b":{"empty":{},"x":["first-response"]}},"z":1}]"#,
        ),
        (
            "parent sibling before nested child",
            &second_modules[..],
            r#"[{"a":{},"z":{"b":{"empty":{},"x":["first-response"]}}},{"a":{},"z":{"b":{"empty":{},"x":["first-response"]}}}]"#,
        ),
    ];

    for (case_name, modules, expected_json) in cases {
        let expected = Value::from_json_str(expected_json)?;
        let mut engine = Engine::new();
        for (module_name, source) in modules {
            engine.add_policy((*module_name).to_string(), (*source).to_string())?;
        }
        let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
        let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
        let data = engine.get_data();

        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_data(data.clone())?;
            vm.set_execution_mode(mode);
            vm.set_input(Value::from_json_str(r#"{"payload":"unused"}"#)?);

            if mode == ExecutionMode::RunToCompletion {
                vm.set_host_await_responses([(
                    Value::from("leaf"),
                    vec![
                        Value::from("first-response"),
                        Value::from("duplicate-response"),
                    ],
                )]);
                assert_eq!(
                    vm.execute_entry_point_by_name(entrypoint)?,
                    expected,
                    "{case_name}: RTC must preserve the actual parent path"
                );
            } else {
                vm.execute_entry_point_by_name(entrypoint)?;
                assert!(
                    matches!(
                        vm.execution_state(),
                        ExecutionState::Suspended {
                            reason: SuspendReason::HostAwait { identifier, argument, .. },
                            ..
                        } if identifier == &Value::from("leaf") && argument == &Value::from("leaf-payload")
                    ),
                    "{case_name}: expected the nested leaf to suspend once"
                );
                assert_eq!(vm.resume(Some(Value::from("first-response")))?, expected);
                assert!(
                    matches!(
                        vm.execution_state(),
                        ExecutionState::Completed { result } if result == &expected
                    ),
                    "{case_name}: parent traversal must finish after the one leaf response"
                );
                assert!(
                    vm.get_cache_hits() > 0,
                    "{case_name}: repeated namespace query should use completed-child cache"
                );
            }
        }
    }

    Ok(())
}

#[test]
fn default_only_function_is_not_invoked_by_document_references() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "lib.rego".to_string(),
        r#"
        package test
        default pick(_) := {"child": [response | response := __builtin_host_await(input.payload, "shared")]}
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        bare := data.test.pick
        suffixed := data.test.pick.child
        dynamic := data.test[input.key]
        probe := __builtin_host_await(input.payload, "shared")
        called := data.test.pick("arg")
        "#
        .to_string(),
    )?;
    let entrypoints = [
        "data.consumer.bare",
        "data.consumer.suffixed",
        "data.consumer.dynamic",
        "data.consumer.probe",
        "data.consumer.called",
    ];
    let compiled = engine.compile_with_entrypoint(&entrypoints[0].into())?;
    let program = Compiler::compile_from_policy(&compiled, &entrypoints)?;
    let data = engine.get_data();
    let expected_call = Value::from_json_str(r#"{"child":["call-response"]}"#)?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);
        vm.set_input(Value::from_json_str(
            r#"{"key":"pick","payload":"host-payload"}"#,
        )?);
        if mode == ExecutionMode::RunToCompletion {
            vm.set_host_await_responses([(
                Value::from("shared"),
                vec![Value::from("probe-response"), Value::from("call-response")],
            )]);
        }

        for reference_entrypoint in [
            "data.consumer.bare",
            "data.consumer.suffixed",
            "data.consumer.dynamic",
        ] {
            assert_eq!(
                vm.execute_entry_point_by_name(reference_entrypoint)?,
                Value::Undefined,
                "{mode:?} document reference {reference_entrypoint} must remain Undefined"
            );
            if mode == ExecutionMode::Suspendable {
                assert!(
                    matches!(
                        vm.execution_state(),
                        ExecutionState::Completed { result } if result == &Value::Undefined
                    ),
                    "{mode:?} document reference {reference_entrypoint} must not invoke HostAwait"
                );
            }
        }

        if mode == ExecutionMode::RunToCompletion {
            assert_eq!(
                vm.execute_entry_point_by_name("data.consumer.probe")?,
                Value::from("probe-response"),
                "bare document references must not consume the queued HostAwait response"
            );
            assert_eq!(
                vm.execute_entry_point_by_name("data.consumer.called")?,
                expected_call,
                "an actual qualified call must still invoke the default-only function"
            );
        } else {
            vm.execute_entry_point_by_name("data.consumer.probe")?;
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason: SuspendReason::HostAwait { identifier, argument, .. },
                    ..
                } if identifier == &Value::from("shared") && argument == &Value::from("host-payload")
            ));
            assert_eq!(
                vm.resume(Some(Value::from("probe-response")))?,
                Value::from("probe-response")
            );

            vm.execute_entry_point_by_name("data.consumer.called")?;
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason: SuspendReason::HostAwait { identifier, argument, .. },
                    ..
                } if identifier == &Value::from("shared") && argument == &Value::from("host-payload")
            ));
            assert_eq!(
                vm.resume(Some(Value::from("call-response")))?,
                expected_call
            );
        }
    }

    Ok(())
}

#[test]
fn empty_default_only_function_packages_are_projected_and_round_trip() -> Result<()> {
    let isolated_modules = [
        (
            "lib.rego",
            r#"
            package lib.a
            default pick(_) := [item | item := true]
            "#,
        ),
        (
            "consumer.rego",
            r#"
            package test
            parent := data.lib
            child := data.lib.a
            repeated := [data.lib, data.lib.a, data.lib]
            "#,
        ),
    ];
    let nested_modules = [
        (
            "lib.rego",
            r#"
            package lib.a.b
            default pick(_) := [item | item := true]
            "#,
        ),
        (
            "sibling.rego",
            r#"
            package lib.z
            value := 1
            "#,
        ),
        (
            "consumer.rego",
            r#"
            package test
            parent := data.lib
            child := data.lib.a
            deep := data.lib.a.b
            repeated := [data.lib, data.lib.a, data.lib]
            "#,
        ),
    ];
    let runtime_data_json = r#"{"lib":{"a":{"kept":7,"allowed":false},"sibling":"preserved"}}"#;
    let cases = [
        (
            "isolated empty package",
            &isolated_modules[..],
            &[
                ("data.test.parent", r#"{"a":{}}"#),
                ("data.test.child", r#"{}"#),
                ("data.test.repeated", r#"[{"a":{}},{},{"a":{}}]"#),
            ][..],
            &[
                (
                    "data.test.parent",
                    r#"{"a":{"allowed":false,"kept":7},"sibling":"preserved"}"#,
                ),
                ("data.test.child", r#"{"allowed":false,"kept":7}"#),
                (
                    "data.test.repeated",
                    r#"[{"a":{"allowed":false,"kept":7},"sibling":"preserved"},{"allowed":false,"kept":7},{"a":{"allowed":false,"kept":7},"sibling":"preserved"}]"#,
                ),
            ][..],
        ),
        (
            "nested empty package with sibling",
            &nested_modules[..],
            &[
                ("data.test.parent", r#"{"a":{"b":{}},"z":{"value":1}}"#),
                ("data.test.child", r#"{"b":{}}"#),
                ("data.test.deep", r#"{}"#),
                (
                    "data.test.repeated",
                    r#"[{"a":{"b":{}},"z":{"value":1}},{"b":{}},{"a":{"b":{}},"z":{"value":1}}]"#,
                ),
            ][..],
            &[
                (
                    "data.test.parent",
                    r#"{"a":{"allowed":false,"b":{},"kept":7},"sibling":"preserved","z":{"value":1}}"#,
                ),
                ("data.test.child", r#"{"allowed":false,"b":{},"kept":7}"#),
                ("data.test.deep", r#"{}"#),
                (
                    "data.test.repeated",
                    r#"[{"a":{"allowed":false,"b":{},"kept":7},"sibling":"preserved","z":{"value":1}},{"allowed":false,"b":{},"kept":7},{"a":{"allowed":false,"b":{},"kept":7},"sibling":"preserved","z":{"value":1}}]"#,
                ),
            ][..],
        ),
    ];

    for (case_name, modules, empty_expected_entries, runtime_expected_entries) in cases {
        let mut engine = Engine::new();
        for (module_name, source) in modules {
            engine.add_policy((*module_name).to_string(), (*source).to_string())?;
        }
        let entrypoints = empty_expected_entries
            .iter()
            .map(|(entrypoint, _)| *entrypoint)
            .collect::<Vec<_>>();
        for (entrypoint, expected_json) in empty_expected_entries {
            assert_eq!(
                engine.eval_rule((*entrypoint).to_string())?,
                Value::from_json_str(expected_json)?,
                "interpreter {case_name} projection for {entrypoint}"
            );
        }

        let compiled = engine.compile_with_entrypoint(&entrypoints[0].into())?;
        let program = Compiler::compile_from_policy(&compiled, &entrypoints)?;
        test_round_trip_serialization(program.as_ref()).map_err(anyhow::Error::msg)?;

        let json = program.serialize_json().map_err(anyhow::Error::msg)?;
        let json_program = Arc::new(Program::deserialize_json(&json).map_err(anyhow::Error::msg)?);
        let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
        let binary_program = Arc::new(
            match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
                DeserializationResult::Complete(program) => program,
                DeserializationResult::Partial(_) => {
                    anyhow::bail!("{case_name}: serialized namespace program needs recompilation")
                }
            },
        );

        for (format_name, round_tripped_program) in [
            ("JSON", json_program.clone()),
            ("binary", binary_program.clone()),
        ] {
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(round_tripped_program.clone());
                vm.set_data(engine.get_data())?;
                vm.set_execution_mode(mode);
                for (entrypoint, expected_json) in empty_expected_entries {
                    assert_eq!(
                        vm.execute_entry_point_by_name(entrypoint)?,
                        Value::from_json_str(expected_json)?,
                        "{case_name}: {format_name}/{mode:?} projection for {entrypoint}"
                    );
                }
            }
        }

        let runtime_data = Value::from_json_str(runtime_data_json)?;
        engine.add_data(runtime_data.clone())?;
        for (entrypoint, expected_json) in runtime_expected_entries {
            assert_eq!(
                engine.eval_rule((*entrypoint).to_string())?,
                Value::from_json_str(expected_json)?,
                "interpreter populated {case_name} projection for {entrypoint}"
            );
        }

        for (format_name, round_tripped_program) in
            [("JSON", json_program), ("binary", binary_program)]
        {
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(round_tripped_program.clone());
                vm.set_data(runtime_data.clone())?;
                vm.set_execution_mode(mode);
                for (entrypoint, expected_json) in runtime_expected_entries {
                    assert_eq!(
                        vm.execute_entry_point_by_name(entrypoint)?,
                        Value::from_json_str(expected_json)?,
                        "{case_name}: populated {format_name}/{mode:?} projection for {entrypoint}"
                    );
                }
            }
        }
    }

    Ok(())
}

fn verify_resumed_virtual_namespace_error_is_terminal_and_reusable(budgeted: bool) -> Result<()> {
    let entrypoint = "data.consumer.p";
    let probe_entrypoint = "data.consumer.probe";
    let mut engine = Engine::new();
    engine.add_policy(
        "lib-leaf.rego".to_string(),
        r#"
        package lib.a
        default x := [response | response := __builtin_host_await("leaf-payload", "leaf")]
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "lib-sibling.rego".to_string(),
        r#"
        package lib
        z := 1 / input.divisor
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        default p := [response | response := __builtin_host_await("fallback-payload", "fallback")]
        p := data.lib
        probe := __builtin_host_await("probe-payload", "fallback")
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint, probe_entrypoint])?;
    let data = engine.get_data();

    #[cfg(not(all(feature = "allocator-memory-limits", not(miri))))]
    assert!(
        !budgeted,
        "allocator budget case requires allocator-memory-limits"
    );

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);
        vm.set_strict_builtin_errors(true);
        vm.set_input(Value::from_json_str(r#"{"divisor":0}"#)?);
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        if budgeted {
            vm.set_memory_budget_config(Some(regorus::MemoryBudgetConfig {
                limit: core::num::NonZeroU64::new(64 * 1024 * 1024)
                    .unwrap_or(core::num::NonZeroU64::MIN),
            }));
        }
        if mode == ExecutionMode::RunToCompletion {
            vm.set_host_await_responses([
                (
                    Value::from("leaf"),
                    vec![
                        Value::from("failed-run-leaf"),
                        Value::from("fresh-run-leaf"),
                    ],
                ),
                (
                    Value::from("fallback"),
                    vec![Value::from("fallback-preserved")],
                ),
            ]);
        }

        let failure = if mode == ExecutionMode::RunToCompletion {
            vm.execute_entry_point_by_name(entrypoint)
                .expect_err("strict sibling division error must propagate through namespace lookup")
        } else {
            vm.execute_entry_point_by_name(entrypoint)?;
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason: SuspendReason::HostAwait { identifier, argument, .. },
                    ..
                } if identifier == &Value::from("leaf") && argument == &Value::from("leaf-payload")
            ));
            vm.resume(Some(Value::from("failed-run-leaf")))
                .expect_err("strict sibling division error must propagate after resume")
        };
        assert!(
            matches!(failure, VmError::InvalidDivision { .. }),
            "{mode:?}, budgeted={budgeted}: expected InvalidDivision, got {failure:?}"
        );
        assert_eq!(
            vm.execution_state(),
            &ExecutionState::Error {
                error: failure.clone()
            },
            "{mode:?}, budgeted={budgeted}: a propagated failure must be terminal and publish its error"
        );

        if mode == ExecutionMode::RunToCompletion {
            assert_eq!(
                vm.execute_entry_point_by_name(probe_entrypoint)?,
                Value::from("fallback-preserved"),
                "failed namespace evaluation must not consume the outer fallback response"
            );
        } else {
            vm.execute_entry_point_by_name(probe_entrypoint)?;
            assert!(
                matches!(
                    vm.execution_state(),
                    ExecutionState::Suspended {
                        reason: SuspendReason::HostAwait { identifier, argument, .. },
                        ..
                    } if identifier == &Value::from("fallback") && argument == &Value::from("probe-payload")
                ),
                "failed namespace evaluation must not leave or consume an outer fallback await"
            );
            assert_eq!(
                vm.resume(Some(Value::from("fallback-preserved")))?,
                Value::from("fallback-preserved")
            );
        }

        vm.set_input(Value::from_json_str(r#"{"divisor":1}"#)?);
        let expected = Value::from_json_str(r#"{"a":{"x":["fresh-run-leaf"]},"z":1}"#)?;
        if mode == ExecutionMode::RunToCompletion {
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                expected,
                "same VM should execute successfully after the propagated error"
            );
        } else {
            vm.execute_entry_point_by_name(entrypoint)?;
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason: SuspendReason::HostAwait { identifier, .. },
                    ..
                } if identifier == &Value::from("leaf")
            ));
            assert_eq!(vm.resume(Some(Value::from("fresh-run-leaf")))?, expected);
        }
    }

    Ok(())
}

#[test]
fn resumed_virtual_namespace_error_is_terminal_and_same_vm_is_reusable() -> Result<()> {
    verify_resumed_virtual_namespace_error_is_terminal_and_reusable(false)?;
    #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
    verify_resumed_virtual_namespace_error_is_terminal_and_reusable(true)?;
    Ok(())
}

#[test]
fn default_only_literal_function_is_not_a_document_value() -> Result<()> {
    let entrypoint = "data.consumer.bare";
    let call_entrypoint = "data.consumer.called";
    let mut engine = Engine::new();
    engine.add_policy(
        "lib.rego".to_string(),
        r#"
        package test
        default pick(_) := {"child": "literal"}
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        bare := data.test.pick
        called := data.test.pick("arg")
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint, call_entrypoint])?;
    let expected_call = Value::from_json_str(r#"{"child":"literal"}"#)?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(engine.get_data())?;
        vm.set_execution_mode(mode);
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            Value::Undefined,
            "{mode:?} bare references must not expose a literal default-only function"
        );
        assert_eq!(
            vm.execute_entry_point_by_name(call_entrypoint)?,
            expected_call,
            "{mode:?} actual function calls must still use literal defaults"
        );
    }

    Ok(())
}
