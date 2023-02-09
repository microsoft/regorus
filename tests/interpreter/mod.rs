// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(test)]

use std::env;

use anyhow::{bail, Result};
use rego_rs::*;
use serde::{Deserialize, Serialize};
use test_generator::test_resources;
//use walkdir::WalkDir;

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

pub fn assert_match(computed: Value, expected: Value) {
    let expected = match process_value(&expected) {
        Ok(e) => e,
        _ => panic!("unable to process value :\n {expected:?}"),
    };
    match match_values(&computed, &expected) {
        Ok(()) => (),
        Err(e) => panic!("{}", e),
    }
}

pub fn eval_file(
    regos: &[String],
    data: Option<Value>,
    input: Option<Value>,
    query: &str,
) -> Result<Value> {
    let mut files = vec![];
    let mut sources = vec![];
    let mut modules = vec![];
    let mut modules_ref = vec![];
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

    // First eval the modules.
    let mut interpreter = interpreter::Interpreter::new(modules_ref)?;
    interpreter.eval(&data, &input)?;

    // Now eval the query.
    let source = Source {
        file: "<query.rego>",
        contents: query,
        lines: query.split('\n').collect(),
    };
    let mut parser = Parser::new(&source)?;
    let expr = parser.parse_membership_expr()?;
    interpreter.eval_query_snippet(&expr)
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
    let tree = parser.parse()?;
    let mut interpreter = interpreter::Interpreter::new(vec![&tree])?;
    let results = interpreter.eval(&None, &input)?;
    println!("eval results:\n{}", serde_json::to_string_pretty(&results)?);
    Ok(())
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestCase {
    data: Value,
    input: Option<Value>,
    modules: Vec<String>,
    note: String,
    query: String,
    sort_bindings: Option<bool>,
    want_result: Option<Value>,
    skip: Option<bool>,
    error: Option<String>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn yaml_test_impl(file: &str) -> Result<()> {
    let yaml_str = std::fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    println!("running {}", file);
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

        // First eval the modules.
        match eval_file(
            &case.modules,
            Some(case.data),
            case.input,
            case.query.as_str(),
        ) {
            Ok(results) => match case.want_result {
                Some(want_result) => assert_match(results, want_result),
                _ => panic!("eval succeeded and did not produce any errors"),
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
            break;
        }
    }

    if file.is_empty() {
        bail!("missing <policy.rego>");
    }

    yaml_test(file.as_str())
}

/*
fn run_yaml_tests_in(folder: &str) -> Result<()> {
    let mut total = 0;

    for entry in WalkDir::new(folder)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path = entry
            .path()
            .to_str()
            .ok_or_else(|| anyhow!("failed to convert path to utf8 {:?}", entry.path()))?;
        if !path.ends_with(".yaml") {
            continue;
        }

        total += 1;
        yaml_test(path)?;
    }

    println!("{} yaml tests passed.", total);
    Ok(())
}

#[test]
fn run_yaml_tests() -> Result<()> {
    run_yaml_tests_in("tests/interpreter")
}
*/

#[test_resources("tests/interpreter/**/*.yaml")]
fn run(path: &str) {
    yaml_test(path).unwrap()
}
