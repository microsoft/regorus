// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::env;

use anyhow::{bail, Result};
use regorus::*;
use serde::{ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer};
use test_generator::test_resources;

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

fn push_query_results(query_results: QueryResults, results: &mut Vec<Value>) {
    if let Some(query_result) = query_results.result.last() {
        if !query_result.bindings.is_empty_object() {
            results.push(query_result.bindings.clone());
        } else if let Some(v) = query_result.expressions.last() {
            results.push(v["value"].clone());
        }
    }
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

    for (idx, _) in regos.iter().enumerate() {
        files.push(format!("rego_{idx}"));
    }

    for (idx, file) in files.iter().enumerate() {
        let contents = regos[idx].as_str();
        sources.push(Source::new(file.to_string(), contents.to_string()));
    }

    for source in &sources {
        let mut parser = Parser::new(source)?;
        modules.push(Ref::new(parser.parse()?));
    }

    let query_source = regorus::Source::new("<query.rego".to_string(), query.to_string());
    let query_span = regorus::Span {
        source: query_source.clone(),
        line: 1,
        col: 1,
        start: 0,
        end: query.len() as u16,
    };
    let mut parser = regorus::Parser::new(&query_source)?;
    let query_node = Ref::new(parser.parse_query(query_span, "")?);
    let query_schedule = regorus::Analyzer::new().analyze_query_snippet(&modules, &query_node)?;

    let analyzer = Analyzer::new();
    let schedule = analyzer.analyze(&modules)?;

    let mut interpreter = interpreter::Interpreter::new(&modules)?;
    if let Some(input) = input_opt {
        // if inputs are defined then first the evaluation if prepared
        interpreter.prepare_for_eval(Some(schedule), &data_opt)?;

        // then all modules are evaluated for each input
        let mut inputs = vec![];
        match input {
            ValueOrVec::Single(single_input) => inputs.push(single_input),
            ValueOrVec::Many(mut many_input) => inputs.append(&mut many_input),
        }

        for input in inputs {
            interpreter.eval_modules(&Some(input), enable_tracing)?;

            // Now eval the query.
            push_query_results(
                interpreter.eval_user_query(&query_node, &query_schedule, enable_tracing)?,
                &mut results,
            );
        }
    } else {
        // it no input is defined then one evaluation of all modules is performed
        interpreter.eval(&data_opt, &None, enable_tracing, Some(schedule))?;

        // Now eval the query.
        push_query_results(
            interpreter.eval_user_query(&query_node, &query_schedule, enable_tracing)?,
            &mut results,
        );
    }

    Ok(results)
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

fn yaml_test_impl(file: &str) -> Result<()> {
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

                    check_output(&results, &expected_results)?;
                }
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
                    println!("{actual}");
                }
                _ => return Err(actual),
            },
        }

        println!("passed");
    }

    Ok(())
}

fn yaml_test(file: &str) -> Result<()> {
    match yaml_test_impl(file) {
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
