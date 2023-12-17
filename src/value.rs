// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::number::Number;

use core::fmt;
use std::collections::{BTreeMap, BTreeSet};
use std::ops;
use std::rc::Rc;
use std::str::FromStr;

use anyhow::{anyhow, bail, Result};
use serde::de::{self, Deserializer, MapAccess, SeqAccess, Visitor};
use serde::ser::{SerializeMap, Serializer};
use serde::{Deserialize, Serialize};

// We cannot use serde_json::Value because Rego has set type and object's key can be
// other rego values.
// BTree is more efficient than a hash table. Another alternative is a sorted vector.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Value {
    // Json data types. serde will automatically map json to these variants.
    Null,
    Bool(bool),
    Number(Number),
    String(Rc<str>),
    Array(Rc<Vec<Value>>),

    // Extra rego data type
    Set(Rc<BTreeSet<Value>>),

    Object(Rc<BTreeMap<Value, Value>>),

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
            Value::String(s) => serializer.serialize_str(s.as_ref()),
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

struct ValueVisitor;

impl<'de> Visitor<'de> for ValueVisitor {
    type Value = Value;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a value")
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Value::Null)
    }

    fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Value::Bool(v))
    }

    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Value::from(v))
    }

    fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Value::from(v))
    }

    fn visit_u128<E>(self, v: u128) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Value::from(v))
    }

    fn visit_i128<E>(self, v: i128) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Value::from(v))
    }

    fn visit_f64<E>(self, v: f64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Value::from(Number::from(v)))
    }

    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Value::String(s.to_string().into()))
    }

    fn visit_string<E>(self, s: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Value::String(s.into()))
    }

    fn visit_seq<V>(self, mut visitor: V) -> Result<Self::Value, V::Error>
    where
        V: SeqAccess<'de>,
    {
        let mut arr = vec![];
        while let Some(v) = visitor.next_element()? {
            arr.push(v);
        }
        Ok(Value::from(arr))
    }

    fn visit_map<V>(self, mut visitor: V) -> Result<Self::Value, V::Error>
    where
        V: MapAccess<'de>,
    {
        if let Some((key, value)) = visitor.next_entry()? {
            if let (Value::String(k), Value::String(v)) = (&key, &value) {
                if k.as_ref() == "$serde_json::private::Number" {
                    match Number::from_str(v) {
                        Ok(n) => return Ok(Value::from(n)),
                        _ => return Err(de::Error::custom("failed to read big number")),
                    }
                }
            }
            let mut map = BTreeMap::new();
            map.insert(key, value);
            while let Some((key, value)) = visitor.next_entry()? {
                map.insert(key, value);
            }
            Ok(Value::from(map))
        } else {
            Ok(Value::new_object())
        }
    }
}

impl<'de> Deserialize<'de> for Value {
    fn deserialize<D>(deserializer: D) -> Result<Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(ValueVisitor)
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
        Value::from(BTreeMap::new())
    }

    pub fn new_set() -> Value {
        Value::from(BTreeSet::new())
    }

    pub fn new_array() -> Value {
        Value::from(vec![])
    }

    pub fn from_json_str(json: &str) -> Result<Value> {
        Ok(serde_json::from_str(json)?)
    }

    pub fn to_json_str(&self) -> Result<String> {
        Ok(serde_json::to_string_pretty(self)?)
    }

    pub fn from_json_file(path: &String) -> Result<Value> {
        match std::fs::read_to_string(path) {
            Ok(c) => Self::from_json_str(c.as_str()),
            Err(e) => bail!("Failed to read {path}. {e}"),
        }
    }

    #[cfg(feature = "yaml")]
    pub fn from_yaml_str(yaml: &str) -> Result<Value> {
        Ok(serde_yaml::from_str(yaml)?)
    }

    #[cfg(feature = "yaml")]
    pub fn from_yaml_file(path: &String) -> Result<Value> {
        match std::fs::read_to_string(path) {
            Ok(c) => Self::from_yaml_str(c.as_str()),
            Err(e) => bail!("Failed to read {path}. {e}"),
        }
    }
}

impl From<u128> for Value {
    fn from(n: u128) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<i128> for Value {
    fn from(n: i128) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<u64> for Value {
    fn from(n: u64) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<i64> for Value {
    fn from(n: i64) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<f64> for Value {
    fn from(n: f64) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<usize> for Value {
    fn from(n: usize) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<Number> for Value {
    fn from(n: Number) -> Self {
        Value::Number(n)
    }
}

impl From<Vec<Value>> for Value {
    fn from(a: Vec<Value>) -> Self {
        Value::Array(Rc::new(a))
    }
}

impl From<BTreeSet<Value>> for Value {
    fn from(s: BTreeSet<Value>) -> Self {
        Value::Set(Rc::new(s))
    }
}

impl From<BTreeMap<Value, Value>> for Value {
    fn from(s: BTreeMap<Value, Value>) -> Self {
        Value::Object(Rc::new(s))
    }
}

impl Value {
    pub fn from_array(a: Vec<Value>) -> Value {
        Value::from(a)
    }

    pub fn from_set(s: BTreeSet<Value>) -> Value {
        Value::from(s)
    }

    pub fn from_map(m: BTreeMap<Value, Value>) -> Value {
        Value::from(m)
    }

    pub fn is_null(&self) -> bool {
        matches!(self, Value::Null)
    }

    pub fn is_undefined(&self) -> bool {
        matches!(self, Value::Null)
    }

    pub fn is_empty_object(&self) -> bool {
        self == &Value::new_object()
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

    pub fn as_string(&self) -> Result<&Rc<str>> {
        match self {
            Value::String(s) => Ok(s),
            _ => Err(anyhow!("not a string")),
        }
    }

    pub fn as_string_mut(&mut self) -> Result<&mut Rc<str>> {
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

impl Value {
    pub fn make_or_get_value_mut<'a>(&'a mut self, paths: &[&str]) -> Result<&'a mut Value> {
        if paths.is_empty() {
            return Ok(self);
        }

        let key = Value::String(paths[0].into());
        if self == &Value::Undefined {
            *self = Value::new_object();
        }
        if let Value::Object(map) = self {
            if map.get(&key).is_none() {
                Rc::make_mut(map).insert(key.clone(), Value::Undefined);
            }
        }

        match self {
            Value::Object(map) => match Rc::make_mut(map).get_mut(&key) {
                Some(v) if paths.len() == 1 => Ok(v),
                Some(v) => Self::make_or_get_value_mut(v, &paths[1..]),
                _ => bail!("internal error: unexpected"),
            },
            Value::Undefined if paths.len() > 1 => {
                *self = Value::new_object();
                Self::make_or_get_value_mut(self, paths)
            }
            Value::Undefined => Ok(self),
            _ => bail!("internal error: make: not an selfect {self:?}"),
        }
    }

    pub fn merge(&mut self, mut new: Value) -> Result<()> {
        if self == &new {
            return Ok(());
        }
        match (self, &mut new) {
            (v @ Value::Undefined, _) => *v = new,
            (Value::Set(ref mut set), Value::Set(new)) => {
                Rc::make_mut(set).append(Rc::make_mut(new))
            }
            (Value::Object(map), Value::Object(new)) => {
                for (k, v) in new.iter() {
                    match map.get(k) {
                        Some(pv) if *pv != *v => {
                            bail!(
                                "value for key `{}` generated multiple times: `{}` and `{}`",
                                serde_json::to_string_pretty(&k)?,
                                serde_json::to_string_pretty(&pv)?,
                                serde_json::to_string_pretty(&v)?,
                            )
                        }
                        _ => Rc::make_mut(map).insert(k.clone(), v.clone()),
                    };
                }
            }
            _ => bail!("error: could not merge value"),
        };
        Ok(())
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
        &self[&Value::String(key.into())]
    }
}

impl ops::Index<&String> for Value {
    type Output = Value;

    fn index(&self, key: &String) -> &Self::Output {
        &self[&Value::String(key.clone().into())]
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
            (Value::Set(s), _) => match s.get(key) {
                Some(v) => v,
                _ => &Value::Undefined,
            },
            (Value::Array(a), Value::Number(n)) => match n.as_u64() {
                Some(index) if (index as usize) < a.len() => &a[index as usize],
                _ => &Value::Undefined,
            },
            _ => &Value::Undefined,
        }
    }
}
