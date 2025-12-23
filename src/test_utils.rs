// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch, clippy::unused_trait_names)]

//! Shared helpers for YAML-driven integration tests.

use crate::Value;
use alloc::{vec, vec::Vec};
use anyhow::{bail, Result};
use serde::{ser::SerializeMap, Deserialize, Deserializer, Serialize, Serializer};

/// Support single or multiple values inside YAML fixtures.
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

/// Convert any YAML-described value into an engine `Value`, handling helper encodings.
pub fn process_value(v: &Value) -> Result<Value> {
    match v {
        Value::String(s) if s.as_ref() == "#undefined" => Ok(Value::Undefined),
        Value::Object(ref fields) if fields.len() == 1 && matches!(&v["set!"], Value::Array(_)) => {
            let mut set_value = Value::new_set();
            let set = set_value.as_set_mut()?;
            for item in v["set!"].as_array()? {
                set.insert(process_value(item)?);
            }
            Ok(set_value)
        }
        Value::Object(fields) if fields.len() == 1 && matches!(&v["object!"], Value::Array(_)) => {
            let mut object_value = Value::new_object();
            let object = object_value.as_object_mut()?;
            for item in v["object!"].as_array()? {
                let key = process_value(&item["key"])?;
                let value = process_value(&item["value"])?;
                object.insert(key, value);
            }
            Ok(object_value)
        }
        Value::Array(items) => {
            let mut array_value = Value::new_array();
            let array = array_value.as_array_mut()?;
            for item in items.iter() {
                array.push(process_value(item)?);
            }
            Ok(array_value)
        }
        Value::Object(fields) => {
            let mut object_value = Value::new_object();
            let object = object_value.as_object_mut()?;
            for (key, value) in fields.iter() {
                object.insert(process_value(key)?, process_value(value)?);
            }
            Ok(object_value)
        }
        Value::Set(_) => bail!("unexpected set in value read from json/yaml"),
        _ => Ok(v.clone()),
    }
}

/// Diff-friendly equality helper used by multiple YAML suites.
pub fn match_values(computed: &Value, expected: &Value) -> Result<()> {
    if computed != expected {
        let expected_yaml = serde_yaml::to_string(expected)?;
        let computed_yaml = serde_yaml::to_string(computed)?;
        bail!("expected:\n{}computed:\n{}", expected_yaml, computed_yaml);
    }
    Ok(())
}

/// Compare two result sets after normalizing special encodings.
pub fn check_output(computed_results: &[Value], expected_results: &[Value]) -> Result<()> {
    if computed_results.len() != expected_results.len() {
        bail!(
            "the number of computed results ({}) and expected results ({}) is not equal",
            computed_results.len(),
            expected_results.len()
        );
    }

    for (n, expected_result) in expected_results.iter().enumerate() {
        let expected = process_value(expected_result)?;
        if let Some(computed_result) = computed_results.get(n) {
            match_values(computed_result, &expected)?;
        }
    }

    Ok(())
}

/// Normalise helper enum to plain vectors for downstream assertions.
pub fn value_or_vec_to_vec(value_or_vec: ValueOrVec) -> Vec<Value> {
    match value_or_vec {
        ValueOrVec::Single(single_result) => vec![single_result],
        ValueOrVec::Many(many_result) => many_result,
    }
}
