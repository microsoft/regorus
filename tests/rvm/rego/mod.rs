// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use anyhow::Result;
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{generate_tabular_assembly_listing, AssemblyListingConfig, Program};
use regorus::rvm::tests::test_utils::test_round_trip_serialization;
use regorus::rvm::vm::RegoVM;
use regorus::test_utils::{check_output, process_value, value_or_vec_to_vec, ValueOrVec};
use regorus::{CompiledPolicy, Engine, Rc, Value};
use serde::{Deserialize, Serialize};
use std::fs;
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
    pub allow_interpreter_success: Option<bool>,
    pub allow_interpreter_incorrect_behavior: Option<bool>,
}

fn default_strict() -> bool {
    true
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    pub cases: Vec<TestCase>,
}

fn render_program_listing(program: &Program) -> String {
    let config = AssemblyListingConfig::default();
    generate_tabular_assembly_listing(program, &config)
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
) -> anyhow::Result<Value> {
    let results = compile_and_run_rvm_with_all_entry_points(
        compiled_policy,
        &[entrypoint],
        data,
        input,
        listing_out,
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
) -> anyhow::Result<Value> {
    let results = compile_and_run_rvm_with_all_entry_points(
        compiled_policy,
        entry_points,
        data,
        input,
        listing_out,
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
) -> anyhow::Result<Vec<Value>> {
    let program = Compiler::compile_from_policy(compiled_policy, entry_points)?;

    // Basic serialization sanity check keeps regressions visible in CI.
    test_round_trip_serialization(program.as_ref()).map_err(|e| anyhow::anyhow!(e))?;

    *listing_out = Some(render_program_listing(program.as_ref()));

    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(data.clone())?;
    vm.set_input(input.clone());

    let mut results = Vec::new();
    for (idx, _) in entry_points.iter().enumerate() {
        let result = if entry_points.len() == 1 {
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
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

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
        for (idx, module) in case.modules.iter().enumerate() {
            engine.add_policy(format!("rego_{idx}"), module.clone())?;
        }

        if let Some(data) = case.data {
            engine.add_data(data)?;
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
        let interpreter_result = engine.eval_rule(case.query.clone());

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
                    )
                } else {
                    compile_and_run_rvm(
                        &compiled_policy,
                        &case.query,
                        &data,
                        &input_value,
                        &mut last_listing,
                    )
                };

                match result {
                    Ok(actual_result) => {
                        match &interpreter_result {
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

                        let expected_results = value_or_vec_to_vec(expected_result.clone());
                        let actual_results = vec![actual_result];
                        check_output(&actual_results, &expected_results)?;
                    }
                    Err(e) => match &interpreter_result {
                        Ok(interpreter_value) => {
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
                        Err(err) => {
                            panic_with_listing!(
                                &last_listing,
                                &case.note,
                                "Both RVM and interpreter failed for case '{}' but a result was expected:\nInterpreter error: {:?}\nRVM error: {}",
                                case.note,
                                err,
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
                    )
                } else {
                    compile_and_run_rvm(
                        &compiled_policy,
                        &case.query,
                        &data,
                        &input_value,
                        &mut last_listing,
                    )
                };

                match result {
                    Ok(result) => match &interpreter_result {
                        Ok(interpreter_value) => {
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
                        Err(_) => {
                            panic_with_listing!(
                                &last_listing,
                                &case.note,
                                "Test case '{}' expected error '{}' but RVM succeeded while interpreter failed:\nRVM result: {}",
                                case.note,
                                expected_error,
                                serde_json::to_string_pretty(&result)?
                            );
                        }
                    },
                    Err(actual_error) => match &interpreter_result {
                        Ok(interpreter_value) => {
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
                        Err(_) => {
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
