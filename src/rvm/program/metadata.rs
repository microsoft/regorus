// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Program metadata types and serialization bridge.
//!
//! [`ProgramMetadata`] stores compiler provenance, source-language identity,
//! and arbitrary key-value annotations alongside the compiled bytecode.
//!
//! Annotations are kept as regorus [`Value`](crate::value::Value) at runtime
//! for zero-cost access via `LoadMetadata`.  For binary serialization the
//! values are converted through [`MetadataValue`] — a postcard/bincode-safe
//! enum that avoids `deserialize_any`.

use crate::Rc;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use serde::{Deserialize, Serialize};

/// Program compilation metadata.
///
/// Annotations are stored as [`Value`](crate::value::Value) at runtime for
/// zero-cost access via `LoadMetadata`.  Serialization converts through
/// [`MetadataValue`] — a postcard/bincode-safe enum that avoids
/// `deserialize_any`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProgramMetadata {
    /// Compiler version that generated this program
    pub compiler_version: String,
    /// Compilation timestamp
    pub compiled_at: String,
    /// Source policy information
    pub source_info: String,
    /// Optimization level used
    pub optimization_level: u8,
    /// Source language that was compiled (e.g. "rego", "azure_policy", "cedar")
    #[serde(default)]
    pub language: String,
    /// Language-specific and user-defined annotations for indexing and introspection.
    /// Stored as `Value` for direct runtime use; serialized via `MetadataValue`.
    #[serde(
        default,
        serialize_with = "metadata_serde::serialize_annotations",
        deserialize_with = "metadata_serde::deserialize_annotations"
    )]
    pub annotations: BTreeMap<String, crate::value::Value>,
}

impl ProgramMetadata {
    /// Convert the full metadata struct into a regorus `Value` for runtime access.
    pub fn to_value(&self) -> crate::value::Value {
        use crate::value::Value;

        let mut obj = BTreeMap::new();
        obj.insert(
            Value::String("compiler_version".into()),
            Value::String(self.compiler_version.as_str().into()),
        );
        obj.insert(
            Value::String("compiled_at".into()),
            Value::String(self.compiled_at.as_str().into()),
        );
        obj.insert(
            Value::String("source_info".into()),
            Value::String(self.source_info.as_str().into()),
        );
        obj.insert(
            Value::String("optimization_level".into()),
            Value::from(i64::from(self.optimization_level)),
        );
        obj.insert(
            Value::String("language".into()),
            Value::String(self.language.as_str().into()),
        );

        if !self.annotations.is_empty() {
            let mut annotations_obj = BTreeMap::new();
            for (k, v) in &self.annotations {
                annotations_obj.insert(Value::String(k.as_str().into()), v.clone());
            }
            obj.insert(
                Value::String("annotations".into()),
                Value::Object(Rc::new(annotations_obj)),
            );
        }

        Value::Object(Rc::new(obj))
    }
}

// ── MetadataValue: postcard-safe serialization bridge ────────────────────────

/// A postcard-compatible, recursive value type used exclusively for serializing
/// program metadata annotations.
///
/// Unlike `serde_json::Value` or regorus `Value`, this enum uses explicit variant
/// tags and does not rely on `deserialize_any`, making it safe for use with
/// non-self-describing formats such as postcard and bincode.
///
/// At runtime, annotations are stored as `Value` for zero-cost access.
/// This type is only used during `Serialize` / `Deserialize` of `ProgramMetadata`.
///
/// # Lossy mappings
///
/// [`Null`](crate::value::Value::Null) and [`Undefined`](crate::value::Value::Undefined)
/// are mapped to [`MetadataValue::String("")`](MetadataValue::String) because metadata
/// annotations have no need for null semantics.  A round-trip through
/// `from_value` → `to_value` will therefore turn `Null`/`Undefined` into an
/// empty string.
///
/// Floating-point numbers are truncated to `i64` because metadata annotations
/// are expected to contain only integer counts, flags, and identifiers —
/// fractional values are not anticipated.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum MetadataValue {
    /// A string value
    String(String),
    /// A set of unique strings (sorted)
    StringSet(BTreeSet<String>),
    /// A boolean value
    Bool(bool),
    /// A 64-bit signed integer (floats are truncated to i64)
    Integer(i64),
    /// An ordered list of metadata values (recursive)
    List(Vec<MetadataValue>),
    /// A string-keyed map of metadata values (recursive)
    Map(BTreeMap<String, MetadataValue>),
}

impl MetadataValue {
    /// Convert a regorus `Value` into a `MetadataValue` for serialization.
    ///
    /// Values that cannot be represented exactly are mapped on a best-effort
    /// basis:
    /// - **Null / Undefined** → empty string (metadata has no null concept)
    /// - **Float** → truncated to `i64` (metadata is integer-only)
    /// - **Non-string object keys** → `Display`-formatted strings
    pub fn from_value(value: &crate::value::Value) -> Self {
        use crate::value::Value;
        match *value {
            Value::String(ref s) => MetadataValue::String(String::from(s.as_ref())),
            Value::Bool(b) => MetadataValue::Bool(b),
            Value::Number(ref n) => {
                // Try integer first, fall back to f64 truncation
                n.as_i64().map_or_else(
                    || {
                        n.as_f64().map_or(MetadataValue::Integer(0), |f| {
                            // Deliberate truncation of f64 to i64 for metadata storage.
                            // Metadata annotations are expected to be integer-valued;
                            // fractional values are not anticipated.
                            #[expect(clippy::as_conversions)]
                            let i = f as i64;
                            MetadataValue::Integer(i)
                        })
                    },
                    MetadataValue::Integer,
                )
            }
            Value::Array(ref arr) => {
                MetadataValue::List(arr.iter().map(MetadataValue::from_value).collect())
            }
            Value::Set(ref set) => {
                // If all elements are strings, use StringSet; otherwise List
                let all_strings = set.iter().all(|v| matches!(*v, Value::String(_)));
                if all_strings {
                    MetadataValue::StringSet(
                        set.iter()
                            .filter_map(|v| match *v {
                                Value::String(ref s) => Some(String::from(s.as_ref())),
                                _ => None,
                            })
                            .collect(),
                    )
                } else {
                    MetadataValue::List(set.iter().map(MetadataValue::from_value).collect())
                }
            }
            Value::Object(ref obj) => {
                let mut map = BTreeMap::new();
                for (k, v) in obj.iter() {
                    let key = match *k {
                        Value::String(ref s) => String::from(s.as_ref()),
                        ref other => alloc::format!("{}", other),
                    };
                    map.insert(key, MetadataValue::from_value(v));
                }
                MetadataValue::Map(map)
            }
            // Null and Undefined have no metadata representation; map to empty string.
            Value::Null | Value::Undefined => MetadataValue::String(String::new()),
        }
    }

    /// Convert this `MetadataValue` into a regorus `Value`.
    pub fn to_value(&self) -> crate::value::Value {
        use crate::value::Value;
        match *self {
            MetadataValue::String(ref s) => Value::String(s.as_str().into()),
            MetadataValue::StringSet(ref set) => {
                let mut bset = alloc::collections::BTreeSet::new();
                for s in set {
                    bset.insert(Value::String(s.as_str().into()));
                }
                Value::Set(Rc::new(bset))
            }
            MetadataValue::Bool(b) => Value::Bool(b),
            MetadataValue::Integer(n) => Value::from(n),
            MetadataValue::List(ref list) => {
                let values: Vec<Value> = list.iter().map(MetadataValue::to_value).collect();
                Value::Array(Rc::new(values))
            }
            MetadataValue::Map(ref map) => {
                let mut obj = BTreeMap::new();
                for (k, v) in map {
                    obj.insert(Value::String(k.as_str().into()), v.to_value());
                }
                Value::Object(Rc::new(obj))
            }
        }
    }
}

/// Serde helpers for `annotations: BTreeMap<String, Value>`.
/// Serializes via `BTreeMap<String, MetadataValue>` to stay postcard-compatible.
mod metadata_serde {
    use super::*;

    pub fn serialize_annotations<S>(
        annotations: &BTreeMap<String, crate::value::Value>,
        serializer: S,
    ) -> core::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::Serialize as _;
        let bridge: BTreeMap<String, MetadataValue> = annotations
            .iter()
            .map(|(k, v)| (k.clone(), MetadataValue::from_value(v)))
            .collect();
        bridge.serialize(serializer)
    }

    pub fn deserialize_annotations<'de, D>(
        deserializer: D,
    ) -> core::result::Result<BTreeMap<String, crate::value::Value>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let bridge: BTreeMap<String, MetadataValue> = BTreeMap::deserialize(deserializer)?;
        Ok(bridge.into_iter().map(|(k, v)| (k, v.to_value())).collect())
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;
    use crate::value::Value;
    use alloc::collections::BTreeSet;

    /// Round-trip: Value → MetadataValue → Value must be equivalent for
    /// all lossless variants (strings, bools, integers, arrays, objects).
    ///
    /// Note: Null and Undefined are intentionally lossy — they round-trip
    /// to empty string.  See [`MetadataValue`] doc for rationale.
    fn assert_round_trip(original: &Value, expected: &Value) {
        let mv = MetadataValue::from_value(original);
        let recovered = mv.to_value();
        assert_eq!(
            &recovered, expected,
            "round-trip failed for {original:?} → {mv:?} → {recovered:?}"
        );
    }

    #[test]
    fn round_trip_string() {
        let v = Value::String("hello".into());
        assert_round_trip(&v, &v);
    }

    #[test]
    fn round_trip_bool() {
        assert_round_trip(&Value::Bool(true), &Value::Bool(true));
        assert_round_trip(&Value::Bool(false), &Value::Bool(false));
    }

    #[test]
    fn round_trip_integer() {
        let v = Value::from(42_i64);
        assert_round_trip(&v, &v);
    }

    #[test]
    fn round_trip_array() {
        let v = Value::from_json_str(r#"[1, "two", true]"#).unwrap();
        assert_round_trip(&v, &v);
    }

    #[test]
    fn round_trip_string_set() {
        let mut set = BTreeSet::new();
        set.insert(Value::String("a".into()));
        set.insert(Value::String("b".into()));
        let v = Value::Set(Rc::new(set));
        assert_round_trip(&v, &v);
    }

    #[test]
    fn round_trip_object() {
        let v = Value::from_json_str(r#"{"key": "value", "n": 7}"#).unwrap();
        assert_round_trip(&v, &v);
    }

    #[test]
    fn null_maps_to_empty_string() {
        let mv = MetadataValue::from_value(&Value::Null);
        assert_eq!(mv, MetadataValue::String(String::new()));
    }

    #[test]
    fn undefined_maps_to_empty_string() {
        let mv = MetadataValue::from_value(&Value::Undefined);
        assert_eq!(mv, MetadataValue::String(String::new()));
    }

    #[test]
    fn mixed_set_uses_list() {
        let mut set = BTreeSet::new();
        set.insert(Value::String("a".into()));
        set.insert(Value::from(1_i64));
        let v = Value::Set(Rc::new(set));
        let mv = MetadataValue::from_value(&v);
        assert!(
            matches!(mv, MetadataValue::List(_)),
            "mixed-type set should produce List, got {mv:?}"
        );
    }

    #[test]
    fn float_truncated_to_integer() {
        let v = Value::from(1.23_f64);
        let mv = MetadataValue::from_value(&v);
        assert_eq!(mv, MetadataValue::Integer(1));
    }

    #[test]
    fn to_value_optimization_level_is_integer() {
        let meta = ProgramMetadata {
            compiler_version: String::new(),
            compiled_at: String::new(),
            source_info: String::new(),
            optimization_level: 2,
            language: String::new(),
            annotations: BTreeMap::new(),
        };
        let val = meta.to_value();
        // optimization_level must be emitted as an integer Value, not float.
        let key = Value::String("optimization_level".into());
        let opt = val.as_object().unwrap().get(&key).unwrap().clone();
        assert_eq!(opt, Value::from(2_i64));
    }

    #[test]
    fn serde_annotations_round_trip() {
        let mut annotations = BTreeMap::new();
        annotations.insert(String::from("flag"), Value::Bool(true));
        annotations.insert(String::from("count"), Value::from(42_i64));
        annotations.insert(String::from("name"), Value::String("test".into()));

        let meta = ProgramMetadata {
            compiler_version: String::from("1.0"),
            compiled_at: String::from("now"),
            source_info: String::from("test"),
            optimization_level: 1,
            language: String::from("rego"),
            annotations,
        };

        // Round-trip through postcard (the format we care about).
        let bytes = postcard::to_allocvec(&meta).unwrap();
        let recovered: ProgramMetadata = postcard::from_bytes(&bytes).unwrap();

        assert_eq!(meta.annotations.len(), recovered.annotations.len());
        for (k, v) in &meta.annotations {
            assert_eq!(
                recovered.annotations.get(k).unwrap(),
                v,
                "annotation {k:?} mismatch after round-trip"
            );
        }
    }
}
