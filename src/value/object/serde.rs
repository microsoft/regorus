// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Serde `Serialize`/`Deserialize` impls for [`Object`].

use alloc::string::ToString as _;
use core::fmt;

use serde::de::{Deserialize, Deserializer, Error as _, MapAccess, Visitor};
use serde::ser::{Serialize, SerializeMap as _, Serializer};

use super::Object;
use crate::value::Value;

impl Serialize for Object {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::Error;
        let mut map = serializer.serialize_map(Some(self.len()))?;
        // Sorted iteration: canonical JSON.
        for (k, v) in self.iter_sorted() {
            match *k {
                Value::String(_) => map.serialize_entry(k, v)?,
                _ => {
                    // Non-string keys are stringified via serde_json::to_string
                    // so the resulting JSON has valid string keys.
                    let key_str = serde_json::to_string(k).map_err(Error::custom)?;
                    map.serialize_entry(&key_str, v)?;
                }
            }
        }
        map.end()
    }
}

struct ObjectVisitor;

impl<'de> Visitor<'de> for ObjectVisitor {
    type Value = Object;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a map of Value to Value")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut obj = Object::new();
        while let Some((k, v)) = access.next_entry::<Value, Value>()? {
            obj.insert(k, v);
            crate::utils::limits::check_memory_limit_if_needed()
                .map_err(|err| A::Error::custom(err.to_string()))?;
        }
        Ok(obj)
    }
}

impl<'de> Deserialize<'de> for Object {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_map(ObjectVisitor)
    }
}
