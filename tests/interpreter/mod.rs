// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(test)]

use std::env;
use std::path::Path;

use anyhow::{bail, Result};
use regorus::*;
use serde::{ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer};
use test_generator::test_resources;
use walkdir::WalkDir;

mod cases;

// Process test value specified in json/yaml to interpret special encodings.
pub fn process_value(v: &Value) -> Result<Value> {
    match v {
        // Handle Undefined encoded as a string "#undefined"
        Value::String(s) if s == "#undefined" => Ok(Value::Undefined),

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

fn display_values(c: &Value, e: &Value) -> Result<String> {
    Ok(format!(
        "\nleft  = {}\nright = {}\n",
        serde_json::to_string_pretty(c)?,
        serde_json::to_string_pretty(e)?
    ))
}

// Helper function to match computed and expecte values.
// On mismatch, prints the failing sub-value instead of the whole value.
fn match_values_impl(computed: &Value, expected: &Value) -> Result<()> {
    match (&computed, &expected) {
        (Value::Array(a1), Value::Array(a2)) => {
            if a1.len() != a2.len() {
                bail!(
                    "array length mismatch: {} != {}{}",
                    a1.len(),
                    a2.len(),
                    display_values(computed, expected)?
                );
            }

            for (idx, v1) in a1.iter().enumerate() {
                match_values_impl(v1, &a2[idx])?;
            }
            Ok(())
        }

        (Value::Set(s1), Value::Set(s2)) => {
            if s1.len() != s2.len() {
                bail!(
                    "set length mismatch: {} != {}{}",
                    s1.len(),
                    s2.len(),
                    display_values(computed, expected)?
                );
            }

            let mut itr2 = s2.iter();
            for v1 in s1.iter() {
                match_values_impl(v1, itr2.next().unwrap())?;
            }
            Ok(())
        }

        (Value::Object(o1), Value::Object(o2)) => {
            if o1.len() != o2.len() {
                bail!(
                    "object length mismatch: {} != {}{}",
                    o1.len(),
                    o2.len(),
                    display_values(computed, expected)?
                );
            }

            let mut itr2 = o2.iter();
            for (k1, v1) in o1.iter() {
                let (k2, v2) = itr2.next().unwrap();
                match_values_impl(k1, k2)?;
                match_values_impl(v1, v2)?;
            }
            Ok(())
        }

        (Value::Number(n1), Value::Number(n2)) if n1 == n2 => Ok(()),
        (Value::String(s1), Value::String(s2)) if s1 == s2 => Ok(()),
        (Value::Bool(b1), Value::Bool(b2)) if b1 == b2 => Ok(()),
        (Value::Null, Value::Null) => Ok(()),
        (Value::Undefined, Value::Undefined) => Ok(()),

        _ => bail!("value mismatch: {}", display_values(computed, expected)?),
    }
}

fn match_values(computed: &Value, expected: &Value) -> Result<()> {
    match match_values_impl(computed, expected) {
        Ok(()) => Ok(()),
        Err(e) => bail!("\nmismatch in {}{}", display_values(computed, expected)?, e),
    }
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

fn query_results_to_value(query_results: QueryResults) -> Result<Value> {
    if let Some(query_result) = query_results.results.last() {
        if !query_result.bindings.is_empty_object() {
            return Ok(query_result.bindings.clone());
        } else {
            return match query_result.expressions.last() {
                Some(v) => Ok(v.clone()),
                _ => bail!("no expressions in query results"),
            };
        }
    }
    bail!("query result incomplete")
}

pub fn eval_file_first_rule(
    regos: &[String],
    data_opt: Option<Value>,
    input_opt: Option<ValueOrVec>,
    query: &str,
    enable_tracing: bool,
) -> Result<Vec<Value>> {
    let mut results = vec![];
    let mut files = vec![];
    let mut sources = vec![];
    let mut modules = vec![];
    let mut modules_ref = vec![];

    let query_source = regorus::Source {
        file: "<query.rego>",
        contents: query,
        lines: query.split('\n').collect(),
    };
    let query_span = regorus::Span {
        source: &query_source,
        line: 1,
        col: 1,
        start: 0,
        end: query.len() as u16,
    };
    let mut parser = regorus::Parser::new(&query_source)?;
    let query_node = parser.parse_query(query_span, "")?;
    let query_stmt_order = regorus::Analyzer::new().analyze_query_snippet(&modules, &query_node)?;
    for (idx, _) in regos.iter().enumerate() {
        files.push(format!("rego_{idx}"));
    }

    for (idx, file) in files.iter().enumerate() {
        let contents = regos[idx].as_str();
        sources.push(Source {
            file,
            contents,
            lines: contents.split('\n').collect(),
        });
    }

    for source in &sources {
        let mut parser = Parser::new(source)?;
        modules.push(parser.parse()?);
    }

    for m in &modules {
        modules_ref.push(m);
    }

    let analyzer = Analyzer::new();
    let schedule = analyzer.analyze(&modules)?;

    let mut interpreter = interpreter::Interpreter::new(modules_ref)?;
    if let Some(input) = input_opt {
        // if inputs are defined then first the evaluation if prepared
        interpreter.prepare_for_eval(Some(&schedule), &data_opt)?;

        // then all modules are evaluated for each input
        let mut inputs = vec![];
        match input {
            ValueOrVec::Single(single_input) => inputs.push(single_input),
            ValueOrVec::Many(mut many_input) => inputs.append(&mut many_input),
        }

        for input in inputs {
            if let Some(module) = &modules.get(0) {
                if let Some(rule) = &module.policy.get(0) {
                    interpreter.eval_rule_with_input(module, rule, &Some(input), enable_tracing)?;
                }
            }

            // Now eval the query.
            results.push(query_results_to_value(interpreter.eval_user_query(
                &query_node,
                &query_stmt_order,
                enable_tracing,
            )?)?);
        }
    } else {
        // it no input is defined then one evaluation of all modules is performed
        interpreter.eval(&data_opt, &None, enable_tracing, Some(&schedule))?;

        // Now eval the query.
        results.push(query_results_to_value(interpreter.eval_user_query(
            &query_node,
            &query_stmt_order,
            enable_tracing,
        )?)?);
    }

    Ok(results)
}

pub fn eval_file(
    regos: &[String],
    data_opt: Option<Value>,
    input_opt: Option<ValueOrVec>,
    query: &str,
    enable_tracing: bool,
) -> Result<Vec<Value>> {
    let mut results = vec![];
    let mut files = vec![];
    let mut sources = vec![];
    let mut modules = vec![];
    let mut modules_ref = vec![];

    let query_source = regorus::Source {
        file: "<query.rego>",
        contents: query,
        lines: query.split('\n').collect(),
    };
    let query_span = regorus::Span {
        source: &query_source,
        line: 1,
        col: 1,
        start: 0,
        end: query.len() as u16,
    };
    let mut parser = regorus::Parser::new(&query_source)?;
    let query_node = parser.parse_query(query_span, "")?;
    let query_stmt_order = regorus::Analyzer::new().analyze_query_snippet(&modules, &query_node)?;

    for (idx, _) in regos.iter().enumerate() {
        files.push(format!("rego_{idx}"));
    }

    for (idx, file) in files.iter().enumerate() {
        let contents = regos[idx].as_str();
        sources.push(Source {
            file,
            contents,
            lines: contents.split('\n').collect(),
        });
    }

    for source in &sources {
        let mut parser = Parser::new(source)?;
        modules.push(parser.parse()?);
    }

    for m in &modules {
        modules_ref.push(m);
    }

    let analyzer = Analyzer::new();
    let schedule = analyzer.analyze(&modules)?;

    let mut interpreter = interpreter::Interpreter::new(modules_ref)?;
    if let Some(input) = input_opt {
        // if inputs are defined then first the evaluation if prepared
        interpreter.prepare_for_eval(Some(&schedule), &data_opt)?;

        // then all modules are evaluated for each input
        let mut inputs = vec![];
        match input {
            ValueOrVec::Single(single_input) => inputs.push(single_input),
            ValueOrVec::Many(mut many_input) => inputs.append(&mut many_input),
        }

        for input in inputs {
            interpreter.eval_modules(&Some(input), enable_tracing)?;

            // Now eval the query.
            results.push(query_results_to_value(interpreter.eval_user_query(
                &query_node,
                &query_stmt_order,
                enable_tracing,
            )?)?);
        }
    } else {
        // it no input is defined then one evaluation of all modules is performed
        interpreter.eval(&data_opt, &None, enable_tracing, Some(&schedule))?;

        // Now eval the query.
        results.push(query_results_to_value(interpreter.eval_user_query(
            &query_node,
            &query_stmt_order,
            enable_tracing,
        )?)?);
    }

    Ok(results)
}

#[test]
#[ignore = "intended for use by scripts/rego-eval"]
fn one_file() -> Result<()> {
    env_logger::init();

    let mut file = String::default();
    let mut input = None;
    for a in env::args() {
        if a.ends_with(".rego") {
            file = a;
        } else if a.ends_with(".json") {
            let input_json = std::fs::read_to_string(&a)?;
            let value = Value::from_json_str(input_json.as_str())?;
            input = Some(value);
        }
    }

    if file.is_empty() {
        bail!("missing <policy.rego>");
    }

    let contents = std::fs::read_to_string(&file)?;

    let source = Source {
        file: file.as_str(),
        contents: contents.as_str(),
        lines: contents.split('\n').collect(),
    };
    let mut parser = Parser::new(&source)?;
    let modules = vec![parser.parse()?];

    let analyzer = Analyzer::new();
    let schedule = analyzer.analyze(&modules)?;

    let mut modules_ref = vec![];
    for m in &modules {
        modules_ref.push(m);
    }

    let mut interpreter = interpreter::Interpreter::new(modules_ref)?;
    interpreter.prepare_for_eval(Some(&schedule), &None)?;
    let results = interpreter.eval_modules(&input, true)?;
    println!("eval results:\n{}", serde_json::to_string_pretty(&results)?);

    Ok(())
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
    skip: Option<bool>,
    error: Option<String>,
    traces: Option<bool>,
    want_error: Option<String>,
    want_error_code: Option<String>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn yaml_test_impl(file: &str, is_opa_test: bool) -> Result<()> {
    let yaml_str = std::fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    println!("running {file}");

    for case in test.cases {
        print!("case {} ", case.note);
        if case.skip == Some(true) {
            println!("skipped");
            continue;
        }

        match (&case.want_result, &case.error) {
            (Some(_), None) | (None, Some(_)) => (),
            _ if is_opa_test => (),
            _ => panic!("either want_result or error must be specified in test case."),
        }

        let enable_tracing = case.traces.is_some() && case.traces.unwrap();

        match eval_file(
            &case.modules,
            case.data,
            case.input,
            case.query.as_str(),
            enable_tracing,
        ) {
            Ok(results) => match case.want_result {
                Some(want_result) => {
                    let mut expected_results = vec![];
                    match want_result {
                        ValueOrVec::Single(single_result) => expected_results.push(single_result),
                        ValueOrVec::Many(mut many_result) => {
                            expected_results.append(&mut many_result)
                        }
                    }

                    if is_opa_test {
                        // Convert value to json compatible representation.
                        let results =
                            Value::from_json_str(serde_json::to_string(&results)?.as_str())?;
                        dbg!((&results, &expected_results[0]));
                        match_values(&results, &expected_results[0])?;
                    } else {
                        check_output(&results, &expected_results)?;
                    }
                }
                _ => bail!("eval succeeded and did not produce any errors"),
            },
            Err(actual) if is_opa_test => {
                if case.want_error.is_none() && case.want_error_code.is_none() {
                    return Err(actual);
                }
                // opa test expects execution to fail and it did.
            }
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
                    println!("{actual}");
                }
                _ => return Err(actual),
            },
        }

        println!("passed");
    }

    Ok(())
}

fn yaml_test(file: &str, is_opa_test: bool) -> Result<()> {
    match yaml_test_impl(file, is_opa_test) {
        Ok(_) => Ok(()),
        Err(e) => {
            // If Err is returned, it doesn't always get printed by cargo test.
            // Therefore, panic with the error.
            panic!("{}", e);
        }
    }
}

#[test]
fn yaml_test_basic() -> Result<()> {
    yaml_test("tests/interpreter/cases/basic_001.yaml", false)
}

#[test]
#[ignore = "intended for use by scripts/yaml-test-eval"]
fn one_yaml() -> Result<()> {
    let mut file = String::default();
    let mut is_opa_test = false;

    for a in env::args() {
        if a.ends_with(".yaml") {
            file = a;
        } else if a == "opa-test" {
            is_opa_test = true;
        }
    }

    if file.is_empty() {
        bail!("missing <yaml-file>");
    }

    yaml_test(file.as_str(), is_opa_test)
}

#[test_resources("tests/interpreter/**/*.yaml")]
fn run(path: &str) {
    yaml_test(path, false).unwrap()
}

#[test]
#[ignore = "intended for running opa test suite"]
fn run_opa_tests() -> Result<()> {
    let mut failures = vec![];
    for a in env::args() {
        if !Path::new(&a).is_dir() {
            continue;
        }
        for entry in WalkDir::new(a)
            .sort_by_file_name()
            .into_iter()
            .filter_map(|e| e.ok())
        {
            let path = entry.path().to_string_lossy().to_string();
            if !Path::new(&path).is_file() || !path.ends_with(".yaml") {
                continue;
            }
            let yaml = path;
            match yaml_test_impl(yaml.as_str(), true) {
                Ok(_) => (),
                Err(e) => {
                    failures.push((yaml, e));
                }
            }
        }
    }

    if !failures.is_empty() {
        dbg!(failures);
        panic!("failed");
    }
    Ok(())
}
