// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Shared test utilities for YAML-based test cases

use crate::*;
use anyhow::{bail, Result};
use serde::{ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer};

/// Process test value specified in json/yaml to interpret special encodings.
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

/// Match computed and expected values with pretty diff output
pub fn match_values(computed: &Value, expected: &Value) -> Result<()> {
    if computed != expected {
        panic!(
            "Values do not match:\nExpected: {:?}\nActual: {:?}",
            expected, computed
        );
    }
    Ok(())
}

/// Check output results against expected results
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

/// Support for single value or multiple values in test input/output
#[derive(PartialEq, Debug, Clone)]
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

/// Standard test case structure for YAML tests
#[derive(Serialize, Deserialize, PartialEq, Debug)]
pub struct TestCase {
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
    /// Allow interpreter to succeed when RVM fails with conflict detection
    pub allow_interpreter_success: Option<bool>,
    /// Allow interpreter to produce incorrect results when RVM produces correct results
    pub allow_interpreter_incorrect_behavior: Option<bool>,
}

fn default_strict() -> bool {
    true
}

/// Standard YAML test file structure
#[derive(Serialize, Deserialize, PartialEq, Debug)]
pub struct YamlTest {
    pub cases: Vec<TestCase>,
}

/// Convert ValueOrVec to a vector of Values
pub fn value_or_vec_to_vec(value_or_vec: ValueOrVec) -> Vec<Value> {
    match value_or_vec {
        ValueOrVec::Single(single_result) => vec![single_result],
        ValueOrVec::Many(many_result) => many_result,
    }
}
