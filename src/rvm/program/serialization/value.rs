// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::str::FromStr as _;
use serde::de::{self, EnumAccess, VariantAccess as _, Visitor};
use serde::ser::{SerializeSeq as _, SerializeTuple as _};
use serde::{Deserialize, Serialize};

use crate::number::Number;
use crate::value::Value;

const VARIANT_NULL: u32 = 0;
const VARIANT_BOOL: u32 = 1;
const VARIANT_NUMBER_STRING: u32 = 2;
const VARIANT_STRING: u32 = 3;
const VARIANT_ARRAY: u32 = 4;
const VARIANT_SET: u32 = 5;
const VARIANT_OBJECT: u32 = 6;
const VARIANT_UNDEFINED: u32 = 7;
const VARIANT_NUMBER_I64: u32 = 8;
const VARIANT_NUMBER_U64: u32 = 9;
const VARIANT_NUMBER_F64: u32 = 10;

/// Wrapper type for zero-copy binary serialization of a `Value`.
/// Keeps references into the original data so collections and strings are not cloned.
pub struct BinaryValueRef<'a>(pub &'a Value);

impl<'a> Serialize for BinaryValueRef<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match *self.0 {
            Value::Null => serializer.serialize_unit_variant("BinaryValue", VARIANT_NULL, "Null"),
            Value::Bool(b) => {
                serializer.serialize_newtype_variant("BinaryValue", VARIANT_BOOL, "Bool", &b)
            }
            Value::Number(ref n) => {
                if let Some(value) = n.as_i64() {
                    serializer.serialize_newtype_variant(
                        "BinaryValue",
                        VARIANT_NUMBER_I64,
                        "NumberI64",
                        &value,
                    )
                } else if let Some(value) = n.as_u64() {
                    serializer.serialize_newtype_variant(
                        "BinaryValue",
                        VARIANT_NUMBER_U64,
                        "NumberU64",
                        &value,
                    )
                } else if let Some(value) = n.as_f64() {
                    serializer.serialize_newtype_variant(
                        "BinaryValue",
                        VARIANT_NUMBER_F64,
                        "NumberF64",
                        &value,
                    )
                } else {
                    serializer.serialize_newtype_variant(
                        "BinaryValue",
                        VARIANT_NUMBER_STRING,
                        "Number",
                        &n.format_scientific(),
                    )
                }
            }
            Value::String(ref s) => serializer.serialize_newtype_variant(
                "BinaryValue",
                VARIANT_STRING,
                "String",
                s.as_ref(),
            ),
            Value::Array(ref items) => serializer.serialize_newtype_variant(
                "BinaryValue",
                VARIANT_ARRAY,
                "Array",
                &BinaryValueSlice(items.as_slice()),
            ),
            Value::Set(ref items) => serializer.serialize_newtype_variant(
                "BinaryValue",
                VARIANT_SET,
                "Set",
                &BinarySetRef(items.as_ref()),
            ),
            Value::Object(ref entries) => serializer.serialize_newtype_variant(
                "BinaryValue",
                VARIANT_OBJECT,
                "Object",
                &BinaryObjectRef(entries.as_ref()),
            ),
            Value::Undefined => {
                serializer.serialize_unit_variant("BinaryValue", VARIANT_UNDEFINED, "Undefined")
            }
        }
    }
}

/// Slice wrapper allowing zero-copy serialization of value collections.
pub struct BinaryValueSlice<'a>(pub &'a [Value]);

impl<'a> Serialize for BinaryValueSlice<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for value in self.0 {
            seq.serialize_element(&BinaryValueRef(value))?;
        }
        seq.end()
    }
}

struct BinarySetRef<'a>(&'a BTreeSet<Value>);

impl<'a> Serialize for BinarySetRef<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for value in self.0.iter() {
            seq.serialize_element(&BinaryValueRef(value))?;
        }
        seq.end()
    }
}

struct BinaryObjectRef<'a>(&'a BTreeMap<Value, Value>);

impl<'a> Serialize for BinaryObjectRef<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for (key, value) in self.0.iter() {
            seq.serialize_element(&BinaryEntryRef(key, value))?;
        }
        seq.end()
    }
}

struct BinaryEntryRef<'a>(&'a Value, &'a Value);

impl<'a> Serialize for BinaryEntryRef<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut tuple = serializer.serialize_tuple(2)?;
        tuple.serialize_element(&BinaryValueRef(self.0))?;
        tuple.serialize_element(&BinaryValueRef(self.1))?;
        tuple.end()
    }
}

/// Owned counterpart used during deserialization.
#[derive(Debug, Clone)]
pub struct BinaryValue(pub Value);

impl BinaryValue {
    fn into_value(self) -> Value {
        self.0
    }
}

const BINARY_VARIANTS: &[&str] = &[
    "Null",
    "Bool",
    "Number",
    "String",
    "Array",
    "Set",
    "Object",
    "Undefined",
    "NumberI64",
    "NumberU64",
    "NumberF64",
];

#[derive(Deserialize)]
#[serde(rename_all = "PascalCase")]
enum BinaryVariant {
    Null,
    Bool,
    Number,
    String,
    Array,
    Set,
    Object,
    Undefined,
    NumberI64,
    NumberU64,
    NumberF64,
}

struct BinaryValueVisitor;

impl<'de> Visitor<'de> for BinaryValueVisitor {
    type Value = BinaryValue;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a BinaryValue enum")
    }

    fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
    where
        A: EnumAccess<'de>,
    {
        match data.variant()? {
            (BinaryVariant::Null, variant) => {
                variant.unit_variant()?;
                Ok(BinaryValue(Value::Null))
            }
            (BinaryVariant::Bool, variant) => {
                let value = variant.newtype_variant::<bool>()?;
                Ok(BinaryValue(Value::from(value)))
            }
            (BinaryVariant::Number, variant) => {
                let numeric = variant.newtype_variant::<&'de str>()?;
                let number = Number::from_str(numeric).map_err(|_| {
                    de::Error::custom(format!("Invalid numeric string '{numeric}'"))
                })?;
                Ok(BinaryValue(Value::from(number)))
            }
            (BinaryVariant::NumberI64, variant) => {
                let value = variant.newtype_variant::<i64>()?;
                Ok(BinaryValue(Value::from(value)))
            }
            (BinaryVariant::NumberU64, variant) => {
                let value = variant.newtype_variant::<u64>()?;
                Ok(BinaryValue(Value::from(value)))
            }
            (BinaryVariant::NumberF64, variant) => {
                let value = variant.newtype_variant::<f64>()?;
                Ok(BinaryValue(Value::from(value)))
            }
            (BinaryVariant::String, variant) => {
                let s = variant.newtype_variant::<&'de str>()?;
                Ok(BinaryValue(Value::from(s)))
            }
            (BinaryVariant::Array, variant) => {
                let items: Vec<BinaryValue> = variant.newtype_variant()?;
                let values: Vec<Value> = items.into_iter().map(BinaryValue::into_value).collect();
                Ok(BinaryValue(Value::from(values)))
            }
            (BinaryVariant::Set, variant) => {
                let items: Vec<BinaryValue> = variant.newtype_variant()?;
                let mut set = BTreeSet::new();
                for item in items {
                    set.insert(item.into_value());
                }
                Ok(BinaryValue(Value::from(set)))
            }
            (BinaryVariant::Object, variant) => {
                let entries: Vec<(BinaryValue, BinaryValue)> = variant.newtype_variant()?;
                let mut map = BTreeMap::new();
                for (key, value) in entries {
                    map.insert(key.into_value(), value.into_value());
                }
                Ok(BinaryValue(Value::from(map)))
            }
            (BinaryVariant::Undefined, variant) => {
                variant.unit_variant()?;
                Ok(BinaryValue(Value::Undefined))
            }
        }
    }
}

impl<'de> Deserialize<'de> for BinaryValue {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_enum("BinaryValue", BINARY_VARIANTS, BinaryValueVisitor)
    }
}

pub fn binaries_to_values(binaries: Vec<BinaryValue>) -> Result<Vec<Value>, String> {
    Ok(binaries.into_iter().map(BinaryValue::into_value).collect())
}

pub fn binary_to_value(binary: BinaryValue) -> Result<Value, String> {
    Ok(binary.into_value())
}
