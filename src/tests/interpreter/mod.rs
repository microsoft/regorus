// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::env;

use crate::*;

use anyhow::{bail, Result};
use serde::{ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer};
use test_generator::test_resources;

// Process test value specified in json/yaml to interpret special encodings.
pub fn process_value(v: &Value) -> Result<Value> {
    match v {
        // Handle Undefined encoded as a string "#undefined"
        Value::String(s) if s.as_ref() == "#undefined" => Ok(Value::Undefined),

        // Handle set encoded as an object
        // set! :
        //   - item1
        //   - item2
        //   ...
        Value::Object(ref fields) if fields.len() == 1 && matches!(&v["set!"], Value::Array(_)) => {
            let mut set_value = Value::new_set();
            let set = set_value.as_set_mut()?;
            for item in v["set!"].as_array()? {
                set.insert(process_value(item)?);
            }
            Ok(set_value)
        }

        // Handle complex object specified explicitly:
        // object! :
        //  - key: ...
        //    value: ...
        Value::Object(fields) if fields.len() == 1 && matches!(&v["object!"], Value::Array(_)) => {
            let mut object_value = Value::new_object();
            let object = object_value.as_object_mut()?;
            for item in v["object!"].as_array()? {
                object.insert(process_value(&item["key"])?, process_value(&item["value"])?);
            }
            Ok(object_value)
        }

        // Recursively process arrays
        Value::Array(items) => {
            let mut array_value = Value::new_array();
            let array = array_value.as_array_mut()?;
            for item in items.iter() {
                array.push(process_value(item)?);
            }
            Ok(array_value)
        }

        // Recursively process objects
        Value::Object(fields) => {
            let mut object_value = Value::new_object();
            let object = object_value.as_object_mut()?;
            for (key, value) in fields.iter() {
                object.insert(process_value(key)?, process_value(value)?);
            }
            Ok(object_value)
        }

        Value::Set(_) => bail!("unexpected set in value read from json/yaml"),

        // Simple variants
        _ => Ok(v.clone()),
    }
}

fn match_values(computed: &Value, expected: &Value) -> Result<()> {
    if computed != expected {
        panic!(
            "{}",
            prettydiff::diff_chars(
                &serde_yaml::to_string(&expected)?,
                &serde_yaml::to_string(&computed)?
            )
        );
    }
    Ok(())
}

pub fn check_output(computed_results: &[Value], expected_results: &[Value]) -> Result<()> {
    if computed_results.len() != expected_results.len() {
        bail!(
            "the number of computed results ({}) and expected results ({}) is not equal",
            computed_results.len(),
            expected_results.len()
        );
    }

    for (n, expected_result) in expected_results.iter().enumerate() {
        let expected = match process_value(expected_result) {
            Ok(e) => e,
            _ => bail!("unable to process value :\n {expected_result:?}"),
        };

        if let Some(computed_result) = computed_results.get(n) {
            match match_values(computed_result, &expected) {
                Ok(()) => (),
                Err(e) => bail!("{e}"),
            }
        }
    }

    Ok(())
}

fn push_query_results(query_results: QueryResults, results: &mut Vec<Value>) {
    if query_results.result.len() == 1 {
        if let Some(query_result) = query_results.result.last() {
            if !query_result.bindings.is_empty_object() {
                results.push(query_result.bindings.clone());
            } else {
                for e in query_result.expressions.iter() {
                    results.push(e.value.clone());
                }
            }
        }
    } else {
        for r in query_results.result.iter() {
            if !r.bindings.is_empty_object() {
                results.push(r.bindings.clone());
            } else {
                results.push(Value::from_array(
                    r.expressions.iter().map(|e| e.value.clone()).collect(),
                ));
            }
        }
    }
}

pub fn eval_file(
    regos: &[String],
    data_opt: Option<Value>,
    input_opt: Option<ValueOrVec>,
    query: &str,
    enable_tracing: bool,
    strict: bool,
) -> Result<(Vec<Value>, Vec<String>)> {
    let mut engine: Engine = Engine::new();
    engine.set_rego_v0(true);
    engine.set_strict_builtin_errors(strict);
    engine.set_gather_prints(true);

    #[cfg(feature = "coverage")]
    engine.set_enable_coverage(true);

    let mut results = vec![];
    let mut files = vec![];

    for (idx, _) in regos.iter().enumerate() {
        files.push(format!("rego_{idx}"));
    }

    for (idx, file) in files.iter().enumerate() {
        let contents = regos[idx].as_str();
        engine.add_policy(file.to_string(), contents.to_string())?;
    }

    if let Some(data) = data_opt {
        engine.add_data(data)?;
    }

    let mut inputs = vec![];
    match input_opt {
        Some(ValueOrVec::Single(single_input)) => inputs.push(single_input),
        Some(ValueOrVec::Many(mut many_input)) => inputs.append(&mut many_input),
        _ => (),
    }

    let mut engine_full = engine.clone();

    if inputs.is_empty() {
        // Now eval the query.
        let r = engine.eval_query(query.to_string(), enable_tracing)?;
        let r_full = engine_full.eval_query_and_all_rules(query.to_string(), enable_tracing)?;
        if r != r_full {
            std::println!(
                "{}\n{}",
                serde_json::to_string_pretty(&r_full)?,
                serde_json::to_string_pretty(&r)?
            );
            assert_eq!(r_full, r);
        }

        push_query_results(r, &mut results);
    } else {
        for input in inputs {
            engine.set_input(input.clone());
            engine_full.set_input(input);

            // Now eval the query.
            let r = engine.eval_query(query.to_string(), enable_tracing)?;
            let r_full = engine_full.eval_query_and_all_rules(query.to_string(), enable_tracing)?;
            if r != r_full {
                std::println!(
                    "{}\n{}",
                    serde_json::to_string_pretty(&r_full)?,
                    serde_json::to_string_pretty(&r)?
                );
                assert_eq!(r_full, r);
            }

            push_query_results(r, &mut results);
        }
    }

    Ok((results, engine.take_prints()?))
}

#[derive(PartialEq, Debug)]
pub enum ValueOrVec {
    Single(Value),
    Many(Vec<Value>),
}

impl Serialize for ValueOrVec {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            ValueOrVec::Single(value) => value.serialize(serializer),
            ValueOrVec::Many(v) => {
                let mut map = serializer.serialize_map(Some(1))?;
                map.serialize_entry("many!", v)?;
                map.end()
            }
        }
    }
}

impl<'de> Deserialize<'de> for ValueOrVec {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = Value::deserialize(deserializer)?;

        match &value["many!"] {
            Value::Array(arr) => Ok(ValueOrVec::Many(arr.to_vec())),
            _ => Ok(ValueOrVec::Single(value)),
        }
    }
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestCase {
    data: Option<Value>,
    input: Option<ValueOrVec>,
    modules: Vec<String>,
    note: String,
    query: String,
    sort_bindings: Option<bool>,
    want_result: Option<ValueOrVec>,
    want_prints: Option<Vec<String>>,
    no_result: Option<bool>,
    skip: Option<bool>,
    error: Option<String>,
    traces: Option<bool>,
    want_error: Option<String>,
    want_error_code: Option<String>,
    #[serde(default = "default_strict")]
    strict: bool,
}

fn default_strict() -> bool {
    true
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn yaml_test_impl(file: &str) -> Result<()> {
    let yaml_str = std::fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    #[cfg(not(feature = "std"))]
    {
        // Skip tests that depend on bultins that need std feature.
        let skip = [
            "intn.yaml",
            "is_valid.yaml",
            "add_date.yaml",
            "date.yaml",
            "clock.yaml",
            "compare.yaml",
            "diff.yaml",
            "format.yaml",
            "globmatch.yaml",
            "now_ns.yaml",
            "parse_duration_ns.yaml",
            "parse_ns.yaml",
            "parse_rfc3339_ns.yaml",
            "weekday.yaml",
            "generate.yaml",
            "parse.yaml",
            "tests.yaml",
        ];
        for s in skip {
            if file.contains(s) {
                std::println!("skipped {file} in no_std mode.");
                return Ok(());
            }
        }
    }

    std::println!("running {file}");

    for case in test.cases {
        std::print!("case {} ", case.note);
        if case.skip == Some(true) {
            std::println!("skipped");
            continue;
        }

        match (&case.want_result, &case.error) {
            (Some(_), None) | (None, Some(_)) => (),
            _ if case.no_result != Some(true) => {
                panic!("either want_result, error or no_result must be specified in test case.")
            }
            _ => (),
        }

        let enable_tracing = case.traces.is_some() && case.traces.unwrap();

        match eval_file(
            &case.modules,
            case.data,
            case.input,
            case.query.as_str(),
            enable_tracing,
            case.strict,
        ) {
            Ok((results, prints)) => match case.want_result {
                Some(want_result) => {
                    let mut expected_results = vec![];
                    match want_result {
                        ValueOrVec::Single(single_result) => expected_results.push(single_result),
                        ValueOrVec::Many(mut many_result) => {
                            expected_results.append(&mut many_result)
                        }
                    }

                    check_output(&results, &expected_results)?;
                    if let Some(expected_prints) = case.want_prints {
                        assert_eq!(expected_prints.len(), prints.len());
                        for (idx, ep) in expected_prints.into_iter().enumerate() {
                            if ep != prints[idx] {
                                std::println!(
                                    "print mismatch :\n{}",
                                    prettydiff::diff_chars(&ep, &prints[idx])
                                );
                                panic!("exiting");
                            }
                        }
                    }
                }
                _ if case.no_result == Some(true) => (),
                _ => bail!("eval succeeded and did not produce any errors"),
            },
            Err(actual) => match &case.error {
                Some(expected) => {
                    let actual = actual.to_string();
                    if !actual.contains(expected) {
                        bail!(
                            "Error message\n`{}\n`\ndoes not contain `{}`",
                            actual,
                            expected
                        );
                    }
                    std::println!("{actual}");
                }
                _ => return Err(actual),
            },
        }

        std::println!("passed");
    }

    Ok(())
}

fn yaml_test(file: &str) -> Result<()> {
    #[cfg(not(feature = "rego-extensions"))]
    if file.contains("rego-extensions") {
        return Ok(());
    }

    match yaml_test_impl(file) {
        Ok(_) => Ok(()),
        Err(e) => {
            // If Err is returned, it doesn't always get printed by cargo test.
            // Therefore, panic with the error.
            panic!("{e}");
        }
    }
}

#[test]
fn yaml_test_basic() -> Result<()> {
    yaml_test("tests/interpreter/cases/basic_001.yaml")
}

#[test]
#[ignore = "intended for use by scripts/yaml-test-eval"]
fn one_yaml() -> Result<()> {
    let mut file = String::default();

    for a in env::args() {
        if a.ends_with(".yaml") {
            file = a;
        }
    }

    if file.is_empty() {
        bail!("missing <yaml-file>");
    }

    yaml_test(file.as_str())
}

#[test_resources("tests/interpreter/**/*.yaml")]
fn run(path: &str) {
    yaml_test(path).unwrap()
}

#[test]
fn test_get_data() -> Result<()> {
    let mut engine = Engine::new();

    // Merge { "x" : 1, "y" : {} }
    engine.add_data(Value::from_json_str(r#"{ "x" : 1, "y" : {}}"#)?)?;

    // Merge { "z" : 2 }
    engine.add_data(Value::from_json_str(r#"{ "z" : 2 }"#)?)?;

    // Add a policy
    engine.add_policy("policy.rego".to_string(), "package a".to_string())?;

    // Evaluate virtual data document. The virtual document includes all rules as well.
    let v_data = engine.eval_query("data".to_string(), false)?.result[0].expressions[0]
        .value
        .clone();
    // There must be an empty package.
    assert_eq!(v_data["a"], Value::new_object());

    // Get the data document.
    let data = engine.get_data();

    // There must NOT be any value of `a`.
    assert_eq!(data["a"], Value::Undefined);

    Ok(())
}
