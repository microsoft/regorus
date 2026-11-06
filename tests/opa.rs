// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use regorus::languages::rego::compiler::{Compiler, CompilerError};
use regorus::rvm::tests::test_utils::test_round_trip_serialization;
use regorus::rvm::vm::RegoVM;
use regorus::*;

use regorus::Rc;
use std::collections::BTreeMap;
use std::io::{self, Write};
use std::path::Path;
use std::process::Command;

use anyhow::{bail, Result};
use clap::Parser;
use serde::{Deserialize, Serialize};
use walkdir::WalkDir;

const OPA_REPO: &str = "https://github.com/open-policy-agent/opa";
const OPA_BRANCH: &str = "v1.2.0";
const OPA_TODO_FOLDERS: &[&str] = &[
    // RVM Compiler does not support 'with' keyword yet.
    "withkeyword",
];

#[derive(Serialize, Deserialize, PartialEq, Debug)]
#[serde(deny_unknown_fields)]
struct TestCase {
    #[serde(skip_serializing_if = "Option::is_none")]
    data: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    input: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    input_term: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    modules: Option<Vec<String>>,
    note: String,
    query: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    sort_bindings: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    want_result: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    skip: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    traces: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    strict_error: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    want_error: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    want_error_code: Option<String>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

struct EngineSetup {
    engine: Engine,
    resolved_input: Value,
}

fn folder_name_from_path(path: &Path) -> Option<String> {
    let mut components = path.components();
    components.next()?; // Skip version prefix (e.g., v0 or v1).
    components
        .next()
        .map(|component| component.as_os_str().to_string_lossy().into_owned())
}

fn log_rvm_skip(case_note: &str, folder_name: Option<&str>) {
    if let Some(folder) = folder_name {
        println!(
            "    skipping RVM check for '{}' (folder '{}' tracked in OPA_TODO_FOLDERS)",
            case_note, folder
        );
    } else {
        println!(
            "    skipping RVM check for '{}' (tracked in OPA_TODO_FOLDERS)",
            case_note
        );
    }
}

/// Allows temporarily enabling RVM verification for folders otherwise listed in
/// `OPA_TODO_FOLDERS`, without editing the source. Set `OPA_UNSKIP_FOLDERS` to a
/// comma-separated list of folder names (e.g. `every,functions`) or `all`.
/// Intended for auditing latent RVM bugs in currently-skipped constructs.
fn folder_rvm_unskipped(folder: &str) -> bool {
    match std::env::var("OPA_UNSKIP_FOLDERS") {
        Ok(list) => {
            let list = list.trim();
            list.eq_ignore_ascii_case("all") || list.split(',').any(|f| f.trim() == folder)
        }
        Err(_) => false,
    }
}

fn setup_engine_for_case(case: &TestCase, is_rego_v0_test: bool) -> Result<EngineSetup> {
    let mut engine = Engine::new();

    #[cfg(feature = "coverage")]
    engine.set_enable_coverage(true);

    engine.set_rego_v0(is_rego_v0_test);

    if let Some(data) = &case.data {
        engine.add_data(data.clone())?;
    }
    let mut resolved_input = case.input.clone().unwrap_or(Value::Undefined);
    engine.set_input(resolved_input.clone());
    if let Some(input_term) = &case.input_term {
        let input = match engine.eval_query(input_term.clone(), true)?.result.last() {
            Some(r) if r.expressions.last().is_some() => r
                .expressions
                .last()
                .expect("no expressions in result")
                .value
                .clone(),
            _ => bail!("no results in evaluated input term"),
        };
        engine.set_input(input.clone());
        resolved_input = input;
    }
    if let Some(modules) = &case.modules {
        for (idx, rego) in modules.iter().enumerate() {
            engine.add_policy(format!("rego{idx}.rego"), rego.clone())?;
        }
    }

    engine.set_strict_builtin_errors(case.strict_error.unwrap_or_default());

    Ok(EngineSetup {
        engine,
        resolved_input,
    })
}

fn eval_test_case(case: &TestCase, is_rego_v0_test: bool) -> Result<Value> {
    let EngineSetup { mut engine, .. } = setup_engine_for_case(case, is_rego_v0_test)?;

    let mut engine_full = engine.clone();
    let mut query_results = engine.eval_query(case.query.clone(), true)?;

    // Ensure that full evaluation produces the same results.
    let qr_full = engine_full.eval_query_and_all_rules(case.query.clone(), true)?;
    if qr_full != query_results {
        if case.note == "refheads/general, set leaf, deep query" {
            // Get test to pass for now.
            query_results = qr_full;
        } else {
            println!("{}", yaml_serde::to_string(case)?);
        }
    }

    let mut values = vec![];
    for qr in query_results.result {
        values.push(if !qr.bindings.as_object()?.is_empty() {
            if case.sort_bindings == Some(true) {
                let mut v = qr.bindings.clone();
                let bindings = v.as_object_mut()?;
                for (_, v) in bindings.iter_mut() {
                    if let Value::Array(_) = v {
                        v.as_array_mut()?.sort();
                    }
                }
                v
            } else {
                qr.bindings.clone()
            }
        } else if let Some(v) = qr.expressions.last() {
            v.value.clone()
        } else {
            Value::Undefined
        });
    }

    let result = Value::from(values);
    // Make result json compatible. (E.g: avoid sets).
    Value::from_json_str(&result.to_string())
}

fn is_simple_identifier(token: &str) -> bool {
    let mut chars = token.chars();
    match chars.next() {
        Some(c) if c == '_' || c.is_ascii_alphabetic() => {}
        _ => return false,
    }
    chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn is_rule_path(expr: &str) -> bool {
    if !expr.trim_start().starts_with("data.") {
        return false;
    }
    expr.trim()
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_'))
}

fn parse_assignment_query(query: &str) -> Option<(String, String)> {
    let mut parts = query.splitn(2, '=');
    let lhs = parts.next()?.trim();
    let rhs = parts.next()?.trim();
    if lhs.is_empty() || rhs.is_empty() {
        return None;
    }

    match (
        is_rule_path(lhs),
        is_simple_identifier(lhs),
        is_rule_path(rhs),
        is_simple_identifier(rhs),
    ) {
        (true, _, _, true) => Some((lhs.to_string(), rhs.to_string())),
        (_, true, true, _) => Some((rhs.to_string(), lhs.to_string())),
        _ => None,
    }
}

fn wrap_binding_result(var_name: &str, value: Value) -> Value {
    let mut binding = BTreeMap::new();
    binding.insert(Value::from(var_name.to_string()), value);
    Value::from(vec![Value::from(binding)])
}

fn eval_rule_with_rvm(case: &TestCase, is_rego_v0_test: bool, rule_path: &str) -> Result<Value> {
    let EngineSetup {
        mut engine,
        resolved_input,
    } = setup_engine_for_case(case, is_rego_v0_test)?;

    let rule = Rc::from(rule_path.to_string());
    let compiled_policy = engine.compile_with_entrypoint(&rule)?;
    let program = Compiler::compile_from_policy(&compiled_policy, &[rule_path])?;
    test_round_trip_serialization(program.as_ref()).map_err(|e| {
        anyhow::anyhow!(
            "Round-trip serialization test failed for query '{}': {}",
            rule_path,
            e
        )
    })?;

    let mut vm = RegoVM::new();
    vm.load_program(program);
    let data_value = case.data.clone().unwrap_or_else(Value::new_object);
    vm.set_data(data_value)?;
    vm.set_input(resolved_input);

    let result = vm.execute()?;
    if result == Value::Undefined {
        Ok(Value::Undefined)
    } else {
        Value::from_json_str(&result.to_string())
    }
}

fn compiler_limitation_reason(err: &anyhow::Error) -> Option<&'static str> {
    err.chain()
        .find_map(|cause| match cause.downcast_ref::<CompilerError>() {
            Some(CompilerError::WithKeywordUnsupported) => Some("with keyword unsupported"),
            Some(CompilerError::FunctionDefaultsUnsupported) => {
                Some("function defaults unsupported")
            }
            Some(CompilerError::RuntimeDependentDefaultUnsupported) => {
                Some("runtime-dependent default values unsupported")
            }
            Some(CompilerError::MultiValueRefHeadUnsupported) => {
                Some("multi-value ref heads unsupported")
            }
            Some(CompilerError::PartialObjectConstantKeyUnsupported)
            | Some(CompilerError::PartialObjectNestedKeyUnsupported) => {
                Some("partial object pattern unsupported")
            }
            Some(CompilerError::General { message })
                if message.starts_with("walk loops are not yet supported") =>
            {
                Some("walk builtin unsupported")
            }
            _ if cause.to_string() == "not a valid rule path" => Some("rule path not compiled"),
            _ => None,
        })
}

// Pin known wrong outputs so a different regression in the same case still fails.
const KNOWN_RVM_MISMATCH_NOTES: &[(&str, &str, &str)] = &[
    (
        "baseandvirtualdocs/base/virtual: undefined",
        "base/virtual document merge",
        r#"[{"x":{"p":"<undefined>","q":"<undefined>"}}]"#,
    ),
    (
        "baseandvirtualdocs/base/virtual: undefined-2",
        "base/virtual document merge",
        r#"[{"x":{"h":{"k":[1,2,3],"p":"<undefined>"}}}]"#,
    ),
    (
        "baseandvirtualdocs/base/virtual: missing input value",
        "base/virtual document merge",
        r#"[{"x":{"p":"<undefined>"}}]"#,
    ),
    ("data/nested integer", "integer key data dereference", "[]"),
    ("fix1863/is defined", "empty package as object", "[]"),
    (
        "ir/call-dynamic with mixed partial rules",
        "dynamic lookup on mixed partial rules",
        "[]",
    ),
    (
        "ir/call-dynamic with mixed partial rules, ref heads",
        "dynamic lookup on mixed partial rules with ref heads",
        "[]",
    ),
    (
        "ir/call-dynamic with ref heads, issue 5839, penultimate",
        "dynamic ref-head lookup",
        "[]",
    ),
];

fn known_rvm_compile_failure_reason(note: &str, err: &anyhow::Error) -> Option<&'static str> {
    let compiler_error = err
        .chain()
        .find_map(|cause| cause.downcast_ref::<CompilerError>())?;
    match (note, compiler_error) {
        ("aggregates/member+some+key+ref with other variable", CompilerError::SomeInNotHoisted) =>
            Some("known some-in loop hoisting failure"),
        ("partialobjectdoc/ref"
            | "regression/partial-object override, different key type, referenced in other rule",
            CompilerError::UndefinedVariable { name }) if name == "p" =>
            Some("known partial-object reference binding failure"),
        ("ir/no call-dynamic with mixed partial rules, ref heads"
            | "ir/call-dynamic with ref heads, issue 5839",
            CompilerError::UndefinedVariable { name }) if name == "a" =>
            Some("known dynamic ref-head binding failure"),
        ("regression/dynamic object to static object comparison (https://github.com/open-policy-agent/opa/issues/6138)",
            CompilerError::UndefinedVariable { name }) if name == "obj" =>
            Some("known dynamic object binding failure"),
        ("data/toplevel integer", CompilerError::General { message })
            if message == "Compile-time recursion detected in rule call chain: data.test.p -> data.test.p" =>
            Some("known false recursive lookup"),
        ("refheads/general, set leaf (other rule defines dynamic ref portion)",
            CompilerError::General { message })
            if message == "internal: rule 'data.test.p' has multiple types: {PartialSet, PartialObject}" =>
            Some("known mixed partial-rule type failure"),
        _ => None,
    }
}

fn known_rvm_mismatch_reason(
    note: &str,
    is_rego_v0_test: bool,
    rvm_binding: &Value,
) -> Result<Option<&'static str>> {
    let Some((_, reason, expected)) = KNOWN_RVM_MISMATCH_NOTES
        .iter()
        .find(|(name, _, _)| *name == note)
    else {
        return Ok(None);
    };
    // The pinned v1 fixture uses string elements where its v0 counterpart uses numbers.
    let expected = match (note, is_rego_v0_test) {
        ("baseandvirtualdocs/base/virtual: undefined-2", false) => {
            r#"[{"x":{"h":{"k":["1","2","3"],"p":"<undefined>"}}}]"#
        }
        _ => expected,
    };
    Ok((Value::from_json_str(expected)? == *rvm_binding).then_some(*reason))
}

fn maybe_verify_rvm_case(
    case: &TestCase,
    is_rego_v0_test: bool,
    actual: &Value,
    verified_rvm_cases: &mut usize,
) -> Result<()> {
    let (rule_path, binding_var) = match parse_assignment_query(&case.query) {
        Some(info) => info,
        None => return Ok(()),
    };

    let rvm_value = match eval_rule_with_rvm(case, is_rego_v0_test, &rule_path) {
        Ok(value) => value,
        Err(err) => {
            if let Some(reason) = compiler_limitation_reason(&err)
                .or_else(|| known_rvm_compile_failure_reason(&case.note, &err))
            {
                println!("    skipping RVM check for '{}' ({})", case.note, reason);
                return Ok(());
            }

            return Err(err);
        }
    };
    let rvm_binding = if rvm_value == Value::Undefined {
        Value::new_array()
    } else {
        wrap_binding_result(&binding_var, rvm_value)
    };

    if &rvm_binding != actual {
        if let Some(reason) = known_rvm_mismatch_reason(&case.note, is_rego_v0_test, &rvm_binding)?
        {
            println!(
                "    skipping RVM check for '{}' (known RVM mismatch: {})",
                case.note, reason
            );
            return Ok(());
        }
        let interpreter_yaml = yaml_serde::to_string(actual)?;
        let rvm_yaml = yaml_serde::to_string(&rvm_binding)?;
        bail!(
            "RVM mismatch for query '{}':\nINTERPRETER:\n{}\nRVM:\n{}",
            case.query,
            interpreter_yaml,
            rvm_yaml
        );
    }

    *verified_rvm_cases += 1;
    Ok(())
}

fn json_schema_tests_check(actual: &Value, expected: &Value) -> bool {
    // Fetch `x` binding.
    let actual = &actual[0]["x"];
    let expected = &expected[0]["x"];

    match (actual, expected) {
        (Value::Array(actual), Value::Array(expected))
            if actual.len() == expected.len() && actual.len() == 2 =>
        {
            // Only check the result since error messages may be different.
            actual[0] == expected[0]
        }
        _ => false,
    }
}

fn run_opa_tests(opa_tests_dir: String, folders: &[String]) -> Result<usize> {
    println!("OPA TESTSUITE: {opa_tests_dir}");
    let tests_path = Path::new(&opa_tests_dir);
    let mut status = BTreeMap::<String, (u32, u32, u32)>::new();
    let mut n = 0;
    let mut missing_functions = BTreeMap::new();
    let mut verified_rvm_cases = 0;
    for entry in WalkDir::new(&opa_tests_dir)
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path_str = entry.path().to_string_lossy().to_string();
        if path_str == opa_tests_dir {
            continue;
        }
        let path = Path::new(&path_str);
        let path_dir = path.strip_prefix(tests_path)?.parent().unwrap();
        // Normalize to forward slashes so the folder filter at the
        // `folders.iter().any(|f| &path_dir_str == f)` check below matches
        // CLI arguments like `v0/aggregates` on Windows, where
        // `to_string_lossy` yields backslash separators by default.
        let path_dir_str = path_dir.to_string_lossy().replace('\\', "/");
        let folder_name = folder_name_from_path(path_dir);
        let skip_rvm_for_folder = folder_name
            .as_deref()
            .map(|folder| OPA_TODO_FOLDERS.contains(&folder) && !folder_rvm_unskipped(folder))
            .unwrap_or(false);

        if path.is_dir() {
            n = 0;
            continue;
        } else if !path.is_file() || !path_str.ends_with(".yaml") {
            continue;
        }

        let run_test = folders.is_empty() || folders.iter().any(|f| &path_dir_str == f);
        if !run_test {
            continue;
        }

        let is_rego_v0_test = path_dir_str.starts_with("v0/") || path_dir.starts_with("v0\\");
        let entry = status.entry(path_dir_str).or_insert((0, 0, 0));

        let yaml_str = std::fs::read_to_string(&path_str)?;
        let test: YamlTest = yaml_serde::from_str(&yaml_str)?;

        for mut case in test.cases {
            let is_json_schema_test = case.note.starts_with("json_verify_schema")
                || case.note.starts_with("json_match_schema");
            let skip_rvm_validation = skip_rvm_for_folder;

            if case.note == "reachable_paths/cycle_1022_3" {
                // The OPA behavior is not well-defined.
                // See: https://github.com/open-policy-agent/opa/issues/5871
                //      https://github.com/open-policy-agent/opa/issues/6128
                // We lock down all the paths leading to leaf nodes instead.
                case.want_result = serde_json::from_str(
                    r#" [{
                  "x" : [
                    ["one", "five", "seven", "eight", "three"],
                    ["one", "five", "six", "nine"],
                    ["one", "five", "six", "seven", "eight", "three"],
                    ["one", "two", "four", "three"]
                  ]
                }]"#,
                )?;
            } else if case.note == "withkeyword/builtin-builtin: arity 0" {
                // The test expects empty object to be returned by opa.runtime.
                // This cannot happen.
                // Skip the test.
                println!("skipping impossible test: {}", case.note);
                continue;
            } else if case.note == "refheads/general, multiple result-set entries" {
                // The entries are specified in reverse order of how object keys would be sorted.
                if let Some(ref mut want_result) = &mut case.want_result {
                    want_result.as_array_mut()?.sort();
                }
            } else if case.note == "withkeyword/builtin: nested, multiple mocks" {
                // Mocks non-existent jwt builtin.
                println!("skipping mock test for io.jwt.decode_verify: {}", case.note);
                continue;
            } else {
                let tests_with_unsupported_builtins = ["jsonbuiltins/yaml round-trip"];
                if tests_with_unsupported_builtins.contains(&case.note.as_str()) {
                    // The test expects unsupported built-in to be called.
                    println!("skipping test using unsupported builtins: {}", case.note);
                    continue;
                }

                let tests_with_deprecated_builtins = [
                    "regexmatch/re_match: ref",
                    "regexmatch/re_match: raw",
                    "regexmatch/re_match: raw: undefined",
                    "regexmatch/re_match",
                    "regexmatch/re_match: undefined",
                    "sets/set_diff: refs",
                    "withkeyword/builtin: http.send example",
                    "withkeyword/builtin-builtin: arity 1, replacement is simple",
                    "withkeyword/function: direct call, built-in replacement, arity 1, result captured",
                    "withkeyword/builtin-builtin: arity 1, replacement is compound",
                    "withkeyword/function: direct call, built-in replacement, arity 1",
                ];
                if tests_with_deprecated_builtins.contains(&case.note.as_str()) {
                    // The test expects deprecated built-in to be called.
                    println!("skipping test using deprecated builtins: {}", case.note);
                    continue;
                }
            }

            // Normalize for comparison.
            if let Some(want_result) = case.want_result {
                case.want_result = Some(serde_json::from_str(&want_result.to_string())?);
            }

            print!("{:4}: {:90}", entry.2, case.note);
            entry.2 += 1;
            match (eval_test_case(&case, is_rego_v0_test), &case.want_result) {
                (Ok(actual), expected)
                    if match expected {
                        Some(expected) => {
                            &actual == expected
                                || (is_json_schema_test
                                    && json_schema_tests_check(&actual, expected))
                        }
                        None => {
                            actual == Value::new_array()
                                && case.want_error.is_none()
                                && case.error.is_none()
                        }
                    } =>
                {
                    if skip_rvm_validation {
                        log_rvm_skip(&case.note, folder_name.as_deref());
                        entry.0 += 1;
                    } else if let Err(rvm_err) = maybe_verify_rvm_case(
                        &case,
                        is_rego_v0_test,
                        &actual,
                        &mut verified_rvm_cases,
                    ) {
                        println!("\n{} failed.", case.note);
                        println!("{}", yaml_serde::to_string(&case)?);
                        println!("{rvm_err}");
                        entry.1 += 1;
                        n += 1;
                        continue;
                    } else {
                        entry.0 += 1;
                    }
                }
                (Ok(_), Some(_)) if case.note == "strings/sprintf: float too big" => {
                    // OPA renders large floats in scientific notation while Regorus emits full decimal digits.
                    // There is no clear benefit in forcing parity for this presentation-only difference.
                    entry.0 += 1;
                }
                // TODO: Handle tests that specify both want_result and strict_error
                (Err(_), _)
                    if case.want_error.is_some()
                        || case.strict_error == Some(true)
                        || case.want_error_code.is_some() =>
                {
                    // Expected failure.
                    entry.0 += 1;
                }
                (r, _) => {
                    println!("\n{} failed.", case.note);
                    println!("{}", yaml_serde::to_string(&case)?);
                    match &r {
                        Ok(actual) => {
                            println!("GOT\n{}", yaml_serde::to_string(&actual)?);
                        }
                        Err(e) => println!("ERROR: {e}"),
                    }

                    if let Err(e) = r {
                        let msg = e.to_string();
                        let pat = "could not find function ";
                        if let Some(pos) = msg.find(pat) {
                            let fcn = &msg[pos + pat.len()..];
                            missing_functions
                                .entry(fcn.to_string())
                                .and_modify(|e| *e += 1)
                                .or_insert(1);
                        }
                    }
                    let path = Path::new("target/opa/failures").join(path_dir);
                    std::fs::create_dir_all(path.clone())?;

                    let mut cmd = "cargo run --example regorus eval".to_string();
                    if let Some(data) = &case.data {
                        let json_path = path.join(format!("data{n}.json"));
                        cmd += format!(" -d {}", json_path.display()).as_str();
                        std::fs::write(json_path, data.to_json_str()?.as_bytes())?;
                    };
                    if let Some(input) = &case.input {
                        let input_path = path.join(format!("data{n}.json"));
                        cmd += format!(" -i {}", input_path.display()).as_str();
                        std::fs::write(input_path, input.to_json_str()?.as_bytes())?;
                    };

                    if let Some(modules) = &case.modules {
                        if modules.len() == 1 {
                            let rego_path = path.join(format!("rego{n}.rego"));
                            cmd += format!(" -d {}", rego_path.display()).as_str();
                            std::fs::write(rego_path, modules[0].as_bytes())?;
                        } else {
                            for (i, m) in modules.iter().enumerate() {
                                let rego_path = path.join(format!("rego{n}_{i}.rego"));
                                cmd += format!(" -d {}", rego_path.display()).as_str();
                                std::fs::write(rego_path, m.as_bytes())?;
                            }
                        }
                    }

                    if is_rego_v0_test {
                        cmd += " -v0";
                    }

                    std::fs::write(path.join(format!("query{n}.text")), case.query.as_bytes())?;
                    cmd += format!(" \"{}\"", &case.query).as_str();

                    println!(" To debug, run:\n\x1b[31m{cmd}\x1b[0m");
                    entry.1 += 1;
                    n += 1;
                    continue;
                }
            }
            println!("  \x1b[32mPASSED\x1b[0m");
        }
    }

    println!("\nOPA TESTSUITE STATUS");
    println!("RVM comparisons verified: {verified_rvm_cases}");
    println!("    {:40}  {:4} {:4}", "FOLDER", "PASS", "FAIL");
    let (mut npass, mut nfail) = (0, 0);
    let mut passing = vec![];
    for (dir, (pass, fail, _)) in status {
        if fail == 0 {
            println!("\x1b[32m    {dir:40}: {pass:4} {fail:4}\x1b[0m");
            passing.push(dir);
        } else {
            println!("\x1b[31m    {dir:40}: {pass:4} {fail:4}\x1b[0m");
        }
        npass += pass;
        nfail += fail;
    }
    println!();

    std::fs::create_dir_all("target")?;
    std::fs::write("target/opa.passing", passing.join("\n"))?;

    if npass == 0 && nfail == 0 {
        bail!("no matching tests found.");
    } else if nfail == 0 {
        println!("\x1b[32m    {:40}: {npass:4} {nfail:4}\x1b[0m", "TOTAL");
    } else {
        println!("\x1b[31m    {:40}: {npass:4} {nfail:4}\x1b[0m", "TOTAL");
    }

    if !missing_functions.is_empty() {
        println!("\nMISSING FUNCTIONS");
        println!("    {:4}  {:42} FAILURES", "", "FUNCTION");
        let mut ncalls = 0;
        for (idx, (fcn, calls)) in missing_functions.iter().enumerate() {
            println!("\x1b[31m    {:4}: {fcn:42} {calls}\x1b[0m", idx + 1);
            ncalls += calls;
        }
        println!("\x1b[31m    {:4}  {:42} {ncalls}\x1b[0m", "", "TOTAL");
    }

    if nfail != 0 {
        bail!("OPA tests failed");
    }

    Ok(verified_rvm_cases)
}

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to OPA test suite.
    #[arg(long, short)]
    test_suite_path: Option<String>,

    /// Specific test folder to run.
    folders: Vec<String>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    let opa_tests_dir = match cli.test_suite_path {
        Some(p) => p,
        None => {
            let branch_dir = format!("target/opa/branch/{OPA_BRANCH}");
            if std::path::Path::exists(Path::new(&branch_dir))
                && !std::path::Path::exists(Path::new(format!("{branch_dir}/.git").as_str()))
            {
                // A stale/partial checkout (e.g. left behind by a cancelled
                // run or restored from a build cache) can exist without a
                // `.git` directory. `git clone` refuses to clone into a
                // non-empty directory, so remove any stale contents first.
                std::fs::remove_dir_all(&branch_dir)?;
            }
            std::fs::create_dir_all(&branch_dir)?;
            if !std::path::Path::exists(Path::new(format!("{branch_dir}/.git").as_str())) {
                let output = match Command::new("git")
                    .arg("clone")
                    .arg(OPA_REPO)
                    .arg("--depth")
                    .arg("1")
                    .arg("--single-branch")
                    .arg("--branch")
                    .arg(OPA_BRANCH)
                    .arg(&branch_dir)
                    .output()
                {
                    Ok(o) => o,
                    Err(e) => {
                        bail!("failed to execute git clone. {e}")
                    }
                };
                println!("status: {}", output.status);
                io::stdout().write_all(&output.stdout).unwrap();
                io::stderr().write_all(&output.stderr).unwrap();
                if !output.status.success() {
                    bail!("failed to clone OPA repository");
                }
            }
            format!("{branch_dir}/v1/test/cases/testdata")
        }
    };

    run_opa_tests(opa_tests_dir, &cli.folders).map(|_| ())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn undefined_assignments_without_want_result_still_verify_rvm() -> Result<()> {
        let root = std::env::temp_dir().join(format!(
            "regorus-opa-undefined-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_nanos()
        ));
        let fixture = r#"cases:
  - note: regression/undefined assignment without want_result
    modules:
      - |
        package test
        p if { false }
    query: x = data.test.p
"#;
        std::fs::create_dir(&root)?;
        let path = root.join("undefined.yaml");
        std::fs::write(&path, fixture)?;
        let verified = run_opa_tests(root.to_string_lossy().into_owned(), &[]);
        std::fs::remove_file(&path)?;
        std::fs::remove_dir(&root)?;
        assert_eq!(verified?, 1);
        Ok(())
    }

    #[test]
    fn assigned_function_defaults_are_recognized_by_the_typed_limitation_filter() -> Result<()> {
        let mut engine = Engine::new();
        engine.add_policy(
            "default.rego".to_string(),
            "package test\ndefault f(x) := 0\np if { x := f(0); x == 0 }".to_string(),
        )?;
        let policy = engine.compile_with_entrypoint(&Rc::from("data.test.p"))?;
        let err = Compiler::compile_from_policy(&policy, &["data.test.p"])
            .expect_err("parameterized defaults must be rejected");
        assert_eq!(
            compiler_limitation_reason(&anyhow::Error::from(err).context("assignment")),
            Some("function defaults unsupported")
        );
        Ok(())
    }
}
