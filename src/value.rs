// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::fmt;
use std::collections::{BTreeMap, BTreeSet};
use std::ops;
use std::rc::Rc;

use anyhow::{anyhow, Result};
use ordered_float::OrderedFloat;
use serde::de::{self, Deserializer};
use serde::ser::{SerializeMap, Serializer};
use serde::{Deserialize, Serialize};

// TODO: rego uses BigNum which has arbitrary precision. But there seems
// to be some bugs with it e.g ((a + b) -a) == b doesn't return true for large
// values of a and b.
// Json doesn't specify a limit on precision, but in practice double (f64) seems
// to be enough to support most use cases and portability too.
// See discussions in jq's repository.
// For now we use OrderedFloat<f64>. We can't use f64 directly since it doesn't
// implement Ord trait.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Number(pub OrderedFloat<f64>);

impl Serialize for Number {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let n_f64 = self.0 .0;
        let n_i64 = n_f64 as i64;
        let n_u64 = n_f64 as u64;

        if n_u64 as f64 == n_f64 {
            serializer.serialize_u64(n_u64)
        } else if n_i64 as f64 == n_f64 {
            serializer.serialize_i64(n_i64)
        } else {
            serializer.serialize_f64(n_f64)
        }
    }
}

struct NumberVisitor;
impl<'de> de::Visitor<'de> for NumberVisitor {
    type Value = Number;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "a json number")
    }

    fn visit_f64<E>(self, v: f64) -> Result<Self::Value, E> {
        Ok(Number(OrderedFloat(v)))
    }

    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E> {
        Ok(Number(OrderedFloat(v as f64)))
    }

    fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E> {
        Ok(Number(OrderedFloat(v as f64)))
    }
}

impl<'de> Deserialize<'de> for Number {
    fn deserialize<D>(deserializer: D) -> Result<Number, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_f64(NumberVisitor)
    }
}

impl fmt::Display for Number {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// We cannot use serde_json::Value because Rego has set type and object's key can be
// other rego values.
// BTree is more efficient that a hast table. Another alternative is a sorted vector.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
#[serde(untagged)]
pub enum Value {
    // Json data types. serde will automatically map json to these variants.
    Null,
    Bool(bool),
    String(String),
    Number(Number),
    Array(Rc<Vec<Value>>),
    Object(Rc<BTreeMap<Value, Value>>),

    // Extra rego data type
    Set(Rc<BTreeSet<Value>>),

    // Indicate that a value is undefined
    Undefined,
}

impl Serialize for Value {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::Error;
        match self {
            Value::Null => serializer.serialize_none(),
            Value::Bool(b) => serializer.serialize_bool(*b),
            Value::String(s) => serializer.serialize_str(s.as_str()),
            Value::Number(n) => n.serialize(serializer),
            Value::Array(a) => a.serialize(serializer),
            Value::Object(fields) => {
                let mut map = serializer.serialize_map(Some(fields.len()))?;
                for (k, v) in fields.iter() {
                    match k {
                        Value::String(_) => map.serialize_entry(k, v)?,
                        _ => {
                            let key_str = serde_json::to_string(k).map_err(Error::custom)?;
                            map.serialize_entry(&key_str, v)?
                        }
                    }
                }
                map.end()
            }

            // display set as an array
            Value::Set(s) => s.serialize(serializer),

            // display undefined as a special string
            Value::Undefined => serializer.serialize_str("<undefined>"),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match serde_json::to_string(self) {
            Ok(s) => write!(f, "{s}"),
            Err(_e) => Err(std::fmt::Error),
        }
    }
}

impl Value {
    pub fn new_object() -> Value {
        Value::from_map(BTreeMap::new())
    }

    pub fn new_set() -> Value {
        Value::from_set(BTreeSet::new())
    }

    pub fn new_array() -> Value {
        Value::from_array(vec![])
    }

    pub fn from_json_str(json: &str) -> Result<Value> {
        Ok(serde_json::from_str(json)?)
    }

    pub fn to_json_str(&self) -> Result<String> {
        Ok(serde_json::to_string_pretty(self)?)
    }
}

impl Value {
    pub fn from_f64(v: f64) -> Value {
        Value::Number(Number(OrderedFloat(v)))
    }

    pub fn from_array(a: Vec<Value>) -> Value {
        Value::Array(Rc::new(a))
    }

    pub fn from_set(s: BTreeSet<Value>) -> Value {
        Value::Set(Rc::new(s))
    }

    pub fn from_map(m: BTreeMap<Value, Value>) -> Value {
        Value::Object(Rc::new(m))
    }

    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }

    pub fn is_undefined(&self) -> bool {
        matches!(self, Value::Null)
    }

    pub fn as_bool(&self) -> Result<&bool> {
        match self {
            Value::Bool(b) => Ok(b),
            _ => Err(anyhow!("not a bool")),
        }
    }

    pub fn as_bool_mut(&mut self) -> Result<&mut bool> {
        match self {
            Value::Bool(b) => Ok(b),
            _ => Err(anyhow!("not a bool")),
        }
    }

    pub fn as_string(&self) -> Result<&String> {
        match self {
            Value::String(s) => Ok(s),
            _ => Err(anyhow!("not a string")),
        }
    }

    pub fn as_string_mut(&mut self) -> Result<&mut String> {
        match self {
            Value::String(s) => Ok(s),
            _ => Err(anyhow!("not a string")),
        }
    }

    pub fn as_number(&self) -> Result<&Number> {
        match self {
            Value::Number(n) => Ok(n),
            _ => Err(anyhow!("not a number")),
        }
    }

    pub fn as_number_mut(&mut self) -> Result<&mut Number> {
        match self {
            Value::Number(n) => Ok(n),
            _ => Err(anyhow!("not a number")),
        }
    }

    pub fn as_array(&self) -> Result<&Vec<Value>> {
        match self {
            Value::Array(a) => Ok(a),
            _ => Err(anyhow!("not an array")),
        }
    }

    pub fn as_array_mut(&mut self) -> Result<&mut Vec<Value>> {
        match self {
            Value::Array(a) => Ok(Rc::make_mut(a)),
            _ => Err(anyhow!("not an array")),
        }
    }

    pub fn as_set(&self) -> Result<&BTreeSet<Value>> {
        match self {
            Value::Set(s) => Ok(s),
            _ => Err(anyhow!("not a set")),
        }
    }

    pub fn as_set_mut(&mut self) -> Result<&mut BTreeSet<Value>> {
        match self {
            Value::Set(s) => Ok(Rc::make_mut(s)),
            _ => Err(anyhow!("not a set")),
        }
    }

    pub fn as_object(&self) -> Result<&BTreeMap<Value, Value>> {
        match self {
            Value::Object(m) => Ok(m),
            _ => Err(anyhow!("not an object")),
        }
    }

    pub fn as_object_mut(&mut self) -> Result<&mut BTreeMap<Value, Value>> {
        match self {
            Value::Object(m) => Ok(Rc::make_mut(m)),
            _ => Err(anyhow!("not an object")),
        }
    }
}

impl ops::Index<usize> for Value {
    type Output = Value;

    fn index(&self, index: usize) -> &Self::Output {
        match self.as_array() {
            Ok(a) if index < a.len() => &a[index],
            _ => &Value::Undefined,
        }
    }
}

impl ops::Index<&str> for Value {
    type Output = Value;

    fn index(&self, key: &str) -> &Self::Output {
        &self[&Value::String(key.to_owned())]
    }
}

impl ops::Index<&String> for Value {
    type Output = Value;

    fn index(&self, key: &String) -> &Self::Output {
        &self[&Value::String(key.clone())]
    }
}

impl ops::Index<&Value> for Value {
    type Output = Value;

    fn index(&self, key: &Value) -> &Self::Output {
        match (self, &key) {
            (Value::Object(o), _) => match &o.get(key) {
                Some(v) => v,
                _ => &Value::Undefined,
            },
            (Value::Array(a), Value::Number(n)) => {
                let index = n.0 .0 as usize;
                if index < a.len() {
                    &a[index]
                } else {
                    &Value::Undefined
                }
            }
            _ => &Value::Undefined,
        }
    }
}
