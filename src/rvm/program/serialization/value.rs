// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::str::FromStr as _;
use serde::de::{self, DeserializeSeed, EnumAccess, SeqAccess, VariantAccess as _, Visitor};
use serde::ser::{SerializeSeq as _, SerializeTuple as _};
use serde::{Deserialize, Serialize};

use crate::number::Number;
use crate::value::Value;
use crate::value::{Object, Set};

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
        crate::utils::depth::check_value(self.0, crate::utils::depth::MAX_DEPTH)
            .map_err(serde::ser::Error::custom)?;
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

struct BinarySetRef<'a>(&'a Set);

impl<'a> Serialize for BinarySetRef<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for value in self.0.iter_sorted() {
            seq.serialize_element(&BinaryValueRef(value))?;
        }
        seq.end()
    }
}

struct BinaryObjectRef<'a>(&'a Object);

impl<'a> Serialize for BinaryObjectRef<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.0.len()))?;
        for (key, value) in self.0.iter_sorted() {
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

struct BinaryValueVisitor(usize);

#[derive(Clone, Copy)]
struct BinarySeed(usize);

impl<'de> DeserializeSeed<'de> for BinarySeed {
    type Value = BinaryValue;

    fn deserialize<D: serde::Deserializer<'de>>(
        self,
        deserializer: D,
    ) -> Result<Self::Value, D::Error> {
        deserializer.deserialize_enum("BinaryValue", BINARY_VARIANTS, BinaryValueVisitor(self.0))
    }
}

struct BinaryItems {
    remaining: usize,
    entries: bool,
}

impl<'de> DeserializeSeed<'de> for BinaryItems {
    type Value = Value;

    fn deserialize<D: serde::Deserializer<'de>>(self, deserializer: D) -> Result<Value, D::Error> {
        deserializer.deserialize_seq(self)
    }
}

impl<'de> Visitor<'de> for BinaryItems {
    type Value = Value;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("binary value entries")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut access: A) -> Result<Value, A::Error> {
        let remaining = crate::utils::depth::descend(self.remaining).map_err(de::Error::custom)?;
        if self.entries {
            let mut output = Object::new();
            while let Some((key, value)) = access.next_element_seed(BinaryEntrySeed(remaining))? {
                output.insert(key.0, value.0);
                crate::utils::limits::check_memory_limit_if_needed().map_err(de::Error::custom)?;
            }
            let output = output.into_value();
            crate::utils::limits::check_memory_limit_if_needed().map_err(de::Error::custom)?;
            Ok(output)
        } else {
            let mut output = Vec::new();
            while let Some(value) = access.next_element_seed(BinarySeed(remaining))? {
                output.push(value.0);
                crate::utils::limits::check_memory_limit_if_needed().map_err(de::Error::custom)?;
            }
            Ok(Value::from(output))
        }
    }
}

struct BinaryEntrySeed(usize);

impl<'de> DeserializeSeed<'de> for BinaryEntrySeed {
    type Value = (BinaryValue, BinaryValue);

    fn deserialize<D: serde::Deserializer<'de>>(
        self,
        deserializer: D,
    ) -> Result<Self::Value, D::Error> {
        deserializer.deserialize_tuple(2, self)
    }
}

impl<'de> Visitor<'de> for BinaryEntrySeed {
    type Value = (BinaryValue, BinaryValue);

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a binary key/value pair")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let key = access
            .next_element_seed(BinarySeed(self.0))?
            .ok_or_else(|| de::Error::invalid_length(0, &self))?;
        let value = access
            .next_element_seed(BinarySeed(self.0))?
            .ok_or_else(|| de::Error::invalid_length(1, &self))?;
        Ok((key, value))
    }
}

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
                // A hand-made or stale blob can carry a number that every ingress path rejects.
                // `Value::from(f64)` cannot report that (it yields `Value::Null`), and a
                // non-finite number in a loaded program has no JSON representation and is ordered
                // outside the finite domain, so reject the blob instead of loading it.
                if !value.is_finite() {
                    return Err(de::Error::custom(format!(
                        "invalid non-finite number in serialized program: {value}"
                    )));
                }
                Ok(BinaryValue(Value::from(value)))
            }
            (BinaryVariant::String, variant) => {
                let s = variant.newtype_variant::<&'de str>()?;
                Ok(BinaryValue(Value::from(s)))
            }
            (BinaryVariant::Array, variant) => {
                let value = variant.newtype_variant_seed(BinaryItems {
                    remaining: self.0,
                    entries: false,
                })?;
                Ok(BinaryValue(value))
            }
            (BinaryVariant::Set, variant) => {
                let items = variant.newtype_variant_seed(BinaryItems {
                    remaining: self.0,
                    entries: false,
                })?;
                let set: BTreeSet<Value> = items
                    .as_array()
                    .map_err(de::Error::custom)?
                    .iter()
                    .cloned()
                    .collect();
                Ok(BinaryValue(Value::from(set)))
            }
            (BinaryVariant::Object, variant) => {
                let object = variant.newtype_variant_seed(BinaryItems {
                    remaining: self.0,
                    entries: true,
                })?;
                Ok(BinaryValue(object))
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
        BinarySeed(crate::utils::depth::MAX_DEPTH).deserialize(deserializer)
    }
}

pub fn binaries_to_values(binaries: Vec<BinaryValue>) -> Result<Vec<Value>, String> {
    Ok(binaries.into_iter().map(BinaryValue::into_value).collect())
}

pub fn binary_to_value(binary: BinaryValue) -> Result<Value, String> {
    Ok(binary.into_value())
}

#[cfg(test)]
mod tests {
    #![allow(clippy::expect_used)] // tests expect()/expect_err() to assert deserialization results

    use super::*;
    use alloc::vec;

    #[test]
    #[cfg(feature = "std")]
    #[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
    fn collection_depth_roundtrips() {
        if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
            crate::value::tests::native_depth_support::run_in_subprocess(
                "rvm::program::serialization::value::tests::collection_depth_roundtrips",
            );
            return;
        }
        std::thread::Builder::new()
            .stack_size(1_500_000)
            .spawn(|| {
                for depth in [32, 33] {
                    for kind in 0..4 {
                        let value = (0..depth).fold(Value::Null, |value, _| match kind {
                            0 => Value::from(vec![value]),
                            1 => Value::from(BTreeSet::from([value])),
                            2 => Value::from(alloc::collections::BTreeMap::from([(
                                Value::from("k"),
                                value,
                            )])),
                            _ => Value::from(alloc::collections::BTreeMap::from([(
                                value,
                                Value::Null,
                            )])),
                        });
                        let mut bytes = match kind {
                            0 => [4, 1].repeat(depth),
                            1 => [5, 1].repeat(depth),
                            2 => [6, 1, 3, 1, b'k'].repeat(depth),
                            _ => [6, 1].repeat(depth),
                        };
                        bytes.push(0);
                        if kind == 3 {
                            bytes.extend(vec![0; depth]);
                        }
                        let encoded = postcard::to_allocvec(&BinaryValueRef(&value));
                        let decoded = postcard::from_bytes::<BinaryValue>(&bytes);
                        if depth == 32 {
                            assert_eq!(encoded.expect("bounded encoding"), bytes);
                            assert_eq!(decoded.expect("bounded decoding").0, value);
                            postcard::from_bytes::<BinaryValue>(
                                bytes.get(..bytes.len().saturating_sub(1)).expect("prefix"),
                            )
                            .expect_err("incomplete collection");
                        } else {
                            encoded.expect_err("encoding requires bounded values");
                            decoded.expect_err("decoding requires bounded values");
                        }
                    }
                }
            })
            .expect("worker starts")
            .join()
            .expect("worker completes");
    }

    /// A blob is untrusted input: the `NumberF64` variant must not be able to put a non-finite
    /// `Number` into the loaded program. The value has no JSON representation and
    /// `Value::from(f64)` would silently turn it into `Value::Null`, so the load must fail instead.
    ///
    /// The bytes are forged rather than produced by `BinaryValueRef`: this crate's serializer
    /// cannot emit a non-finite `NumberF64` because `Number::as_f64` rejects non-finite, which
    /// sends such a value to the `Number` string variant (`format_scientific` -> "inf") that
    /// `Number::from_str` already rejects. The guard below is what closes the hand-made-blob path.
    ///
    /// Removing the `is_finite` check makes each forged blob deserialize (as `Value::Null`) and
    /// this test fail.
    #[test]
    fn non_finite_float_in_a_blob_is_rejected() {
        let forged_number_f64 = |value: f64| {
            let mut bytes = vec![u8::try_from(VARIANT_NUMBER_F64).expect("variant fits in u8")];
            bytes.extend_from_slice(&value.to_le_bytes());
            bytes
        };

        for value in [f64::INFINITY, f64::NEG_INFINITY, f64::NAN] {
            // postcard maps a custom `de::Error` to `DeserializeError::SerdeDeCustom` and drops
            // the text, so the observable contract is simply that the load fails.
            postcard::from_bytes::<BinaryValue>(&forged_number_f64(value))
                .expect_err(&format!("a blob carrying {value} must not load"));
        }

        // Teeth: a finite f64 still round-trips.
        let bytes =
            postcard::to_allocvec(&BinaryValueRef(&Value::from(1.5_f64))).expect("serializing 1.5");
        let value: BinaryValue = postcard::from_bytes(&bytes).expect("loading 1.5");
        assert_eq!(value.into_value(), Value::from(1.5_f64));
    }
}
