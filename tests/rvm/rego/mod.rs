// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use anyhow::Result;
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{
    generate_tabular_assembly_listing, AssemblyListingConfig, DeserializationResult, Program,
};
use regorus::rvm::tests::test_utils::test_round_trip_serialization;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, SuspendReason};
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
