// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::number::Number;

use alloc::collections::{BTreeMap, BTreeSet};
use core::fmt;
use core::ops;

use core::convert::AsRef;
use core::str::FromStr;

use anyhow::{anyhow, bail, Result};
use serde::de::{self, Deserializer, MapAccess, SeqAccess, Visitor};
use serde::ser::{SerializeMap, Serializer};
use serde::{Deserialize, Serialize};

use crate::*;

/// A value in a Rego document.
///
/// Value is similar to a [`serde_json::value::Value`], but has the following additional
/// capabilities:
///    - [`Value::Set`] variant to represent sets.
///    - [`Value::Undefined`] variant to represent absence of value.
//     - [`Value::Object`] keys can be other values, not just strings.
///    - [`Value::Number`] has at least 100 digits of precision for computations.
///
/// Value can be efficiently cloned due to the use of reference counting.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Value {
    /// JSON null.
    Null,

    /// JSON boolean.
    Bool(bool),

    /// JSON number.
    /// At least 100 digits of precision.
    Number(Number),

    /// JSON string.
    String(Rc<str>),

    /// JSON array.
    Array(Rc<Vec<Value>>),

    /// A set of values.
    /// No JSON equivalent.
    /// Sets are serialized as arrays in JSON.
    Set(Rc<BTreeSet<Value>>),

    /// An object.
    /// Unlike JSON, keys can be any value, not just string.
    Object(Rc<BTreeMap<Value, Value>>),

    /// Undefined value.
    /// Used to indicate the absence of a value.
    Undefined,
}

#[doc(hidden)]
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

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
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

#[doc(hidden)]
impl<'de> Deserialize<'de> for Value {
    fn deserialize<D>(deserializer: D) -> Result<Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(ValueVisitor)
    }
}

impl fmt::Display for Value {
    /// Display a value.
    ///
    /// A value is displayed by serializing it to JSON using serde_json::to_string.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from("hello");
    /// assert_eq!(format!("{v}"), "\"hello\"");
    /// # Ok(())
    /// # }
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match serde_json::to_string(self) {
            Ok(s) => write!(f, "{s}"),
            Err(_e) => Err(fmt::Error),
        }
    }
}

impl Value {
    /// Create an empty [`Value::Array`]
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let obj = Value::new_array();
    /// assert_eq!(obj.as_array().expect("not an array").len(), 0);
    /// # Ok(())
    /// # }
    /// ```
    pub fn new_array() -> Value {
        Value::from(vec![])
    }

    /// Create an empty [`Value::Object`]
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let obj = Value::new_object();
    /// assert_eq!(obj.as_object().expect("not an object").len(), 0);
    /// # Ok(())
    /// # }
    /// ```
    pub fn new_object() -> Value {
        Value::from(BTreeMap::new())
    }

    /// Create an empty [`Value::Set`]
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let obj = Value::new_set();
    /// assert_eq!(obj.as_set().expect("not a set").len(), 0);
    /// # Ok(())
    /// # }
    /// ```
    pub fn new_set() -> Value {
        Value::from(BTreeSet::new())
    }
}

impl Value {
    /// Deserialize a [`Value`] from JSON.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let json = r#"
    /// [
    ///   null, true, false,
    ///   "hello", 12345,
    ///   { "name" : "regorus" }
    /// ]"#;
    ///
    /// // Deserialize json.
    /// let value = Value::from_json_str(json)?;
    ///
    /// // Assert outer array.
    /// let array = value.as_array().expect("not an array");
    ///
    /// // Assert elements.
    /// assert_eq!(array[0], Value::Null);
    /// assert_eq!(array[1], Value::from(true));
    /// assert_eq!(array[2], Value::from(false));
    /// assert_eq!(array[3], Value::from("hello"));
    /// assert_eq!(array[4], Value::from(12345u64));
    /// let obj = array[5].as_object().expect("not an object");
    /// assert_eq!(obj.len(), 1);
    /// assert_eq!(obj[&Value::from("name")], Value::from("regorus"));
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_json_str(json: &str) -> Result<Value> {
        serde_json::from_str(json).map_err(anyhow::Error::msg)
    }

    /// Deserialize a [`Value`] from a file containing JSON.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let value = Value::from_json_file("tests/aci/input.json")?;
    ///
    /// // Convert the value back to json.
    /// let json_str = value.to_json_str()?;
    ///
    /// assert_eq!(json_str.trim(), std::fs::read_to_string("tests/aci/input.json")?.trim());
    /// # Ok(())
    /// # }
    /// ```
    #[cfg(feature = "std")]
    pub fn from_json_file<P: AsRef<std::path::Path>>(path: P) -> Result<Value> {
        match std::fs::read_to_string(&path) {
            Ok(c) => Self::from_json_str(c.as_str()),
            Err(e) => bail!("Failed to read {}. {e}", path.as_ref().display()),
        }
    }

    /// Serialize a value to JSON.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let value = Value::from_json_file("tests/aci/input.json")?;
    ///
    /// // Convert the value back to json.
    /// let json_str = value.to_json_str()?;
    ///
    /// assert_eq!(json_str.trim(), std::fs::read_to_string("tests/aci/input.json")?.trim());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Sets are serialized as arrays.
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeSet;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut set = BTreeSet::new();
    /// set.insert(Value::from("Hello"));
    /// set.insert(Value::from(1u64));
    ///
    /// let set_value = Value::from(set);
    ///
    /// assert_eq!(
    ///  set_value.to_json_str()?,
    ///  r#"
    ///[
    ///   1,
    ///   "Hello"
    ///]"#.trim());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Non string keys of objects are serialized to json first and the serialized string representation
    /// is emitted as the key.
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeMap;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut obj = BTreeMap::new();
    /// obj.insert(Value::from("Hello"), Value::from("World"));
    /// obj.insert(Value::from([Value::from(1u64)].to_vec()), Value::Null);
    ///
    /// let obj_value = Value::from(obj);
    ///
    /// assert_eq!(
    ///  obj_value.to_json_str()?,
    ///  r#"
    ///{
    ///   "Hello": "World",
    ///   "[1]": null
    ///}"#.trim());
    /// # Ok(())
    /// # }
    /// ```
    pub fn to_json_str(&self) -> Result<String> {
        serde_json::to_string_pretty(self).map_err(anyhow::Error::msg)
    }

    /// Deserialize a value from YAML.
    /// Note: Deserialization from YAML does not support arbitrary precision numbers.
    #[cfg(feature = "yaml")]
    pub fn from_yaml_str(yaml: &str) -> Result<Value> {
        Ok(serde_yaml::from_str(yaml)?)
    }

    /// Deserialize a value from a file containing YAML.
    /// Note: Deserialization from YAML does not support arbitrary precision numbers.
    #[cfg(feature = "std")]
    #[cfg(feature = "yaml")]
    pub fn from_yaml_file(path: &String) -> Result<Value> {
        match std::fs::read_to_string(path) {
            Ok(c) => Self::from_yaml_str(c.as_str()),
            Err(e) => bail!("Failed to read {path}. {e}"),
        }
    }
}

impl From<bool> for Value {
    /// Create a [`Value::Bool`] from `bool`.
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeSet;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(Value::from(true), Value::Bool(true));
    /// # Ok(())
    /// # }
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl From<String> for Value {
    /// Create a [`Value::String`] from `string`.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(Value::from("Hello".to_string()), Value::String("Hello".into()));
    /// # Ok(())
    /// # }
    fn from(s: String) -> Self {
        Value::String(s.into())
    }
}

impl From<&str> for Value {
    /// Create a [`Value::String`] from `&str`.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(Value::from("Hello"), Value::String("Hello".into()));
    /// # Ok(())
    /// # }
    fn from(s: &str) -> Self {
        Value::String(s.into())
    }
}

impl From<u128> for Value {
    /// Create a [`Value::Number`] from `u128`.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(
    ///   Value::from(340_282_366_920_938_463_463_374_607_431_768_211_455u128).as_u128()?,
    ///   340_282_366_920_938_463_463_374_607_431_768_211_455u128);
    /// # Ok(())
    /// # }
    fn from(n: u128) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<i128> for Value {
    /// Create a [`Value::Number`] from `i128`.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(
    ///   Value::from(-170141183460469231731687303715884105728i128).as_i128()?,
    ///   -170141183460469231731687303715884105728i128);
    /// # Ok(())
    /// # }
    fn from(n: i128) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<u64> for Value {
    /// Create a [`Value::Number`] from `u64`.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(
    ///   Value::from(0u64),
    ///   Value::from_json_str("0")?);
    /// # Ok(())
    /// # }
    fn from(n: u64) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<i64> for Value {
    /// Create a [`Value::Number`] from `i64`.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(
    ///   Value::from(0i64),
    ///   Value::from_json_str("0")?);
    /// # Ok(())
    /// # }
    fn from(n: i64) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<u32> for Value {
    /// Create a [`Value::Number`] from `u32`.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(
    ///   Value::from(0u32),
    ///   Value::from_json_str("0")?);
    /// # Ok(())
    /// # }
    fn from(n: u32) -> Self {
        Value::Number(Number::from(n as u64))
    }
}

impl From<i32> for Value {
    /// Create a [`Value::Number`] from `i32`.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(
    ///   Value::from(0i32),
    ///   Value::from_json_str("0")?);
    /// # Ok(())
    /// # }
    fn from(n: i32) -> Self {
        Value::Number(Number::from(n as i64))
    }
}

impl From<f64> for Value {
    /// Create a [`Value::Number`] from `f64`.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(
    ///   Value::from(3.141592653589793),
    ///   Value::from_numeric_string("3.141592653589793")?);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// Note, f64 can store only around 15 digits of precision whereas [`Value::Number`]
    /// can store arbitrary precision. Adding an extra digit to the f64 literal in the above
    /// example causes loss of precision and the Value created from f64 does not match the
    /// Value parsed from numeric string (which is more precise).
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// // The last digit is lost in f64.
    /// assert_ne!(
    ///   Value::from(3.1415926535897932),
    ///   Value::from_numeric_string("3.141592653589793232")?);
    ///
    /// // The value, in this case is equal to parsing the json number with last digit omitted.
    /// assert_ne!(
    ///   Value::from(3.1415926535897932),
    ///   Value::from_numeric_string("3.14159265358979323")?);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// If precision is important, it is better to construct numeric values from strings instead
    /// of f64 when possible.
    /// See [Value::from_numeric_string]
    fn from(n: f64) -> Self {
        Value::Number(Number::from(n))
    }
}

impl From<serde_json::Value> for Value {
    /// Create a [`Value`] from [`serde_json::Value`].
    ///
    /// Returns [`Value::Undefined`] in case of error.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let json_v = serde_json::json!({ "x":10, "y": 20 });
    /// let v = Value::from(json_v);
    ///
    /// assert_eq!(v["x"].as_u64()?, 10);
    /// assert_eq!(v["y"].as_u64()?, 20);
    /// # Ok(())
    /// # }
    fn from(v: serde_json::Value) -> Self {
        match serde_json::from_value(v) {
            Ok(v) => v,
            _ => Value::Undefined,
        }
    }
}

#[cfg(feature = "yaml")]
impl From<serde_yaml::Value> for Value {
    /// Create a [`Value`] from [`serde_yaml::Value`].
    ///
    /// Returns [`Value::Undefined`] in case of error.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let yaml = "
    ///   x: 10
    ///   y: 20
    /// ";
    /// let yaml_v : serde_yaml::Value = serde_yaml::from_str(&yaml).unwrap();
    /// let v = Value::from(yaml_v);
    ///
    /// assert_eq!(v["x"].as_u64()?, 10);
    /// assert_eq!(v["y"].as_u64()?, 20);
    /// # Ok(())
    /// # }
    fn from(v: serde_yaml::Value) -> Self {
        match serde_yaml::from_value(v) {
            Ok(v) => v,
            _ => Value::Undefined,
        }
    }
}

impl Value {
    /// Create a [`Value::Number`] from a string containing numeric representation of a number.
    ///
    /// This is the preferred way for creating arbitrary precision numbers.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from_numeric_string("3.14159265358979323846264338327950288419716939937510")?;
    ///
    /// println!("{}", v.to_json_str()?);
    /// // Prints 3.1415926535897932384626433832795028841971693993751 if serde_json/arbitrary_precision feature is enabled.
    /// // Prints 3.141592653589793 if serde_json/arbitrary_precision is not enabled.
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_numeric_string(s: &str) -> Result<Value> {
        Ok(Value::Number(
            Number::from_str(s).map_err(|_| anyhow!("not a valid numeric string"))?,
        ))
    }
}

impl From<usize> for Value {
    /// Create a [`Value::Number`] from `usize`.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// assert_eq!(
    ///   Value::from(0usize),
    ///   Value::from_json_str("0")?);
    /// # Ok(())
    /// # }
    fn from(n: usize) -> Self {
        Value::Number(Number::from(n))
    }
}

#[doc(hidden)]
impl From<Number> for Value {
    fn from(n: Number) -> Self {
        Value::Number(n)
    }
}

impl From<Vec<Value>> for Value {
    /// Create a [`Value::Array`] from a [`Vec<Value>`].
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let strings = [ "Hello", "World" ];
    ///
    /// let v = Value::from(strings.iter().map(|s| Value::from(*s)).collect::<Vec<Value>>());
    /// assert_eq!(v[0], Value::from(strings[0]));
    /// assert_eq!(v[1], Value::from(strings[1]));
    /// # Ok(())
    /// # }
    fn from(a: Vec<Value>) -> Self {
        Value::Array(Rc::new(a))
    }
}

impl From<BTreeSet<Value>> for Value {
    /// Create a [`Value::Set`] from a [`BTreeSet<Value>`].
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeSet;
    /// # fn main() -> anyhow::Result<()> {
    /// let strings = [ "Hello", "World" ];
    /// let v = Value::from(strings
    ///            .iter()
    ///            .map(|s| Value::from(*s))
    ///            .collect::<BTreeSet<Value>>());
    ///
    /// let mut iter = v.as_set()?.iter();
    /// assert_eq!(iter.next(), Some(&Value::from(strings[0])));
    /// assert_eq!(iter.next(), Some(&Value::from(strings[1])));
    /// # Ok(())
    /// # }
    fn from(s: BTreeSet<Value>) -> Self {
        Value::Set(Rc::new(s))
    }
}

impl From<BTreeMap<Value, Value>> for Value {
    /// Create a [`Value::Object`] from a [`BTreeMap<Value>`].
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeMap;
    /// # fn main() -> anyhow::Result<()> {
    /// let strings = [ ("Hello", "World") ];
    /// let v = Value::from(strings
    ///            .iter()
    ///            .map(|(k,v)| (Value::from(*k), Value::from(*v)))
    ///            .collect::<BTreeMap<Value, Value>>());
    ///
    /// let mut iter = v.as_object()?.iter();
    /// assert_eq!(iter.next(), Some((&Value::from(strings[0].0), &Value::from(strings[0].1))));
    /// # Ok(())
    /// # }
    fn from(s: BTreeMap<Value, Value>) -> Self {
        Value::Object(Rc::new(s))
    }
}

impl Value {
    pub(crate) fn from_array(a: Vec<Value>) -> Value {
        Value::from(a)
    }

    pub(crate) fn from_set(s: BTreeSet<Value>) -> Value {
        Value::from(s)
    }

    pub(crate) fn from_map(m: BTreeMap<Value, Value>) -> Value {
        Value::from(m)
    }

    pub(crate) fn is_empty_object(&self) -> bool {
        self == &Value::new_object()
    }
}

impl Value {
    /// Cast value to [`& bool`] if [`Value::Bool`].
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from(true);
    /// assert_eq!(v.as_bool()?, &true);
    /// # Ok(())
    /// # }
    pub fn as_bool(&self) -> Result<&bool> {
        match self {
            Value::Bool(b) => Ok(b),
            _ => Err(anyhow!("not a bool")),
        }
    }

    /// Cast value to [`&mut bool`] if [`Value::Bool`].
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut v = Value::from(true);
    /// *v.as_bool_mut()? = false;
    /// # Ok(())
    /// # }
    pub fn as_bool_mut(&mut self) -> Result<&mut bool> {
        match self {
            Value::Bool(b) => Ok(b),
            _ => Err(anyhow!("not a bool")),
        }
    }

    /// Cast value to [`& u128`] if [`Value::Number`].
    ///
    /// Error is raised if the value is not a number or if the numeric value
    /// does not fit in a u128.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from(10);
    /// assert_eq!(v.as_u128()?, 10u128);
    ///
    /// let v = Value::from(-10);
    /// assert!(v.as_u128().is_err());
    /// # Ok(())
    /// # }
    pub fn as_u128(&self) -> Result<u128> {
        match self {
            Value::Number(b) => {
                if let Some(n) = b.as_u128() {
                    return Ok(n);
                }
                bail!("not a u128");
            }
            _ => Err(anyhow!("not a u128")),
        }
    }

    /// Cast value to [`& i128`] if [`Value::Number`].
    ///
    /// Error is raised if the value is not a number or if the numeric value
    /// does not fit in a i128.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from(-10);
    /// assert_eq!(v.as_i128()?, -10i128);
    ///
    /// let v = Value::from_numeric_string("11111111111111111111111111111111111111111111111111")?;
    /// assert!(v.as_i128().is_err());
    /// # Ok(())
    /// # }
    pub fn as_i128(&self) -> Result<i128> {
        match self {
            Value::Number(b) => {
                if let Some(n) = b.as_i128() {
                    return Ok(n);
                }
                bail!("not a i128");
            }
            _ => Err(anyhow!("not a i128")),
        }
    }

    /// Cast value to [`& u64`] if [`Value::Number`].
    ///
    /// Error is raised if the value is not a number or if the numeric value
    /// does not fit in a u64.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from(10);
    /// assert_eq!(v.as_u64()?, 10u64);
    ///
    /// let v = Value::from(-10);
    /// assert!(v.as_u64().is_err());
    /// # Ok(())
    /// # }
    pub fn as_u64(&self) -> Result<u64> {
        match self {
            Value::Number(b) => {
                if let Some(n) = b.as_u64() {
                    return Ok(n);
                }
                bail!("not a u64");
            }
            _ => Err(anyhow!("not a u64")),
        }
    }

    /// Cast value to [`& i64`] if [`Value::Number`].
    ///
    /// Error is raised if the value is not a number or if the numeric value
    /// does not fit in a i64.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from(-10);
    /// assert_eq!(v.as_i64()?, -10i64);
    ///
    /// let v = Value::from(340_282_366_920_938_463_463_374_607_431_768_211_455u128);
    /// assert!(v.as_i64().is_err());
    /// # Ok(())
    /// # }
    pub fn as_i64(&self) -> Result<i64> {
        match self {
            Value::Number(b) => {
                if let Some(n) = b.as_i64() {
                    return Ok(n);
                }
                bail!("not an i64");
            }
            _ => Err(anyhow!("not an i64")),
        }
    }

    /// Cast value to [`& f64`] if [`Value::Number`].
    /// Error is raised if the value is not a number or if the numeric value
    /// does not fit in a i64.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from(-10);
    /// assert_eq!(v.as_f64()?, -10f64);
    ///
    /// let v = Value::from(340_282_366_920_938_463_463_374_607_431_768_211_455u128);
    /// assert!(v.as_i64().is_err());
    /// # Ok(())
    /// # }
    pub fn as_f64(&self) -> Result<f64> {
        match self {
            Value::Number(b) => {
                if let Some(n) = b.as_f64() {
                    return Ok(n);
                }
                bail!("not a f64");
            }
            _ => Err(anyhow!("not a f64")),
        }
    }

    /// Cast value to [`& Rc<str>`] if [`Value::String`].
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from("Hello");
    /// assert_eq!(v.as_string()?.as_ref(), "Hello");
    /// # Ok(())
    /// # }
    pub fn as_string(&self) -> Result<&Rc<str>> {
        match self {
            Value::String(s) => Ok(s),
            _ => Err(anyhow!("not a string")),
        }
    }

    /// Cast value to [`&mut Rc<str>`] if [`Value::String`].
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut v = Value::from("Hello");
    /// *v.as_string_mut()? = "World".into();
    /// # Ok(())
    /// # }
    pub fn as_string_mut(&mut self) -> Result<&mut Rc<str>> {
        match self {
            Value::String(s) => Ok(s),
            _ => Err(anyhow!("not a string")),
        }
    }

    #[doc(hidden)]
    pub fn as_number(&self) -> Result<&Number> {
        match self {
            Value::Number(n) => Ok(n),
            _ => Err(anyhow!("not a number")),
        }
    }

    #[doc(hidden)]
    pub fn as_number_mut(&mut self) -> Result<&mut Number> {
        match self {
            Value::Number(n) => Ok(n),
            _ => Err(anyhow!("not a number")),
        }
    }

    /// Cast value to [`& Vec<Value>`] if [`Value::Array`].
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from([Value::from("Hello")].to_vec());
    /// assert_eq!(v.as_array()?[0], Value::from("Hello"));
    /// # Ok(())
    /// # }
    pub fn as_array(&self) -> Result<&Vec<Value>> {
        match self {
            Value::Array(a) => Ok(a),
            _ => Err(anyhow!("not an array")),
        }
    }

    /// Cast value to [`&mut Vec<Value>`] if [`Value::Array`].
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut v = Value::from([Value::from("Hello")].to_vec());
    /// v.as_array_mut()?.push(Value::from("World"));
    /// # Ok(())
    /// # }
    pub fn as_array_mut(&mut self) -> Result<&mut Vec<Value>> {
        match self {
            Value::Array(a) => Ok(Rc::make_mut(a)),
            _ => Err(anyhow!("not an array")),
        }
    }

    /// Cast value to [`& BTreeSet<Value>`] if [`Value::Set`].
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeSet;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from(
    ///    [Value::from("Hello")]
    ///        .iter()
    ///        .cloned()
    ///        .collect::<BTreeSet<Value>>(),
    /// );
    /// assert_eq!(v.as_set()?.first(), Some(&Value::from("Hello")));
    /// # Ok(())
    /// # }
    pub fn as_set(&self) -> Result<&BTreeSet<Value>> {
        match self {
            Value::Set(s) => Ok(s),
            _ => Err(anyhow!("not a set")),
        }
    }

    /// Cast value to [`&mut BTreeSet<Value>`] if [`Value::Set`].
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeSet;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut v = Value::from(
    ///    [Value::from("Hello")]
    ///        .iter()
    ///        .cloned()
    ///        .collect::<BTreeSet<Value>>(),
    /// );
    /// v.as_set_mut()?.insert(Value::from("World"));
    /// # Ok(())
    /// # }
    pub fn as_set_mut(&mut self) -> Result<&mut BTreeSet<Value>> {
        match self {
            Value::Set(s) => Ok(Rc::make_mut(s)),
            _ => Err(anyhow!("not a set")),
        }
    }

    /// Cast value to [`& BTreeMap<Value, Value>`] if [`Value::Object`].
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeMap;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from(
    ///    [(Value::from("Hello"), Value::from("World"))]
    ///        .iter()
    ///        .cloned()
    ///        .collect::<BTreeMap<Value, Value>>(),
    /// );
    /// assert_eq!(
    ///    v.as_object()?.iter().next(),
    ///    Some((&Value::from("Hello"), &Value::from("World"))),
    /// );
    /// # Ok(())
    /// # }
    pub fn as_object(&self) -> Result<&BTreeMap<Value, Value>> {
        match self {
            Value::Object(m) => Ok(m),
            _ => Err(anyhow!("not an object")),
        }
    }

    /// Cast value to [`&mut BTreeMap<Value, Value>`] if [`Value::Object`].
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeMap;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut v = Value::from(
    ///    [(Value::from("Hello"), Value::from("World"))]
    ///        .iter()
    ///        .cloned()
    ///        .collect::<BTreeMap<Value, Value>>(),
    /// );
    /// v.as_object_mut()?.insert(Value::from("Good"), Value::from("Bye"));
    /// # Ok(())
    /// # }
    pub fn as_object_mut(&mut self) -> Result<&mut BTreeMap<Value, Value>> {
        match self {
            Value::Object(m) => Ok(Rc::make_mut(m)),
            _ => Err(anyhow!("not an object")),
        }
    }
}

impl Value {
    pub(crate) fn make_or_get_value_mut<'a>(&'a mut self, paths: &[&str]) -> Result<&'a mut Value> {
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

    pub(crate) fn merge(&mut self, mut new: Value) -> Result<()> {
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
                                serde_json::to_string_pretty(&k).map_err(anyhow::Error::msg)?,
                                serde_json::to_string_pretty(&pv).map_err(anyhow::Error::msg)?,
                                serde_json::to_string_pretty(&v).map_err(anyhow::Error::msg)?,
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

impl ops::Index<&Value> for Value {
    type Output = Value;

    /// Index a [`Value`] using a [`Value`].
    ///
    /// [`Value::Undefined`] is returned
    /// - If the index not valid for the collection.
    /// - If the value being indexed is not an array, set or object.
    ///
    /// Sets can be indexed only by elements within the set.
    ///
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeMap;
    /// # fn main() -> anyhow::Result<()> {
    ///
    /// let arr = Value::from([Value::from("Hello")].to_vec());
    /// // Index an array.
    /// assert_eq!(arr[&Value::from(0)].as_string()?.as_ref(), "Hello");
    /// assert_eq!(arr[&Value::from(10)], Value::Undefined);
    ///
    /// let mut set = Value::new_set();
    /// set.as_set_mut()?.insert(Value::from(100));
    /// set.as_set_mut()?.insert(Value::from("Hello"));
    ///
    /// // Index a set.
    /// let item = Value::from("Hello");
    /// assert_eq!(&set[&item], &item);
    /// assert_eq!(&set[&Value::from(10)], &Value::Undefined);
    ///
    /// let mut obj = Value::new_object();
    /// obj.as_object_mut()?.insert(Value::from("Hello"), Value::from("World"));
    /// obj.as_object_mut()?.insert(Value::new_array(), Value::from("bye"));
    ///
    /// // Index an object.
    /// assert_eq!(&obj[Value::from("Hello")].as_string()?.as_ref(), &"World");
    /// assert_eq!(&obj[Value::from("hllo")], &Value::Undefined);
    /// // Index using non-string key.
    /// assert_eq!(&obj[&Value::new_array()].as_string()?.as_ref(), &"bye");
    ///
    /// // Index a non-collection.
    /// assert_eq!(&Value::Null[&Value::from(1)], &Value::Undefined);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// This is the preferred way of indexing a value.
    /// Since constructing a value may be a costly operation (e.g. Value::String),
    /// the caller can construct the index value once and use it many times.
    ///`
    fn index(&self, key: &Value) -> &Self::Output {
        match (self, key) {
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

impl<T> ops::Index<T> for Value
where
    Value: From<T>,
{
    type Output = Value;

    /// Index a [`Value`].
    ///
    ///
    /// A [`Value`] is constructed from the index which is then used for indexing.
    ///
    /// ```
    /// # use regorus::*;
    /// # use std::collections::BTreeMap;
    /// # fn main() -> anyhow::Result<()> {
    /// let v = Value::from(
    ///    [(Value::from("Hello"), Value::from("World")),
    ///     (Value::from(1), Value::from(2))]
    ///        .iter()
    ///        .cloned()
    ///        .collect::<BTreeMap<Value, Value>>(),
    /// );
    ///
    /// assert_eq!(&v["Hello"].as_string()?.as_ref(), &"World");
    /// assert_eq!(&v[1].as_u64()?, &2u64);
    /// # Ok(())
    /// # }
    fn index(&self, key: T) -> &Self::Output {
        &self[&Value::from(key)]
    }
}
