// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Serde `Serialize`/`Deserialize` impls for [`Object`].

use alloc::string::ToString as _;
use core::fmt;

use serde::de::{Deserialize, Deserializer, Error as _, MapAccess, Visitor};
use serde::ser::{Serialize, SerializeMap as _, Serializer};

use super::Object;
use crate::value::{
    serialization_child_budget, SerializeWithBudget, Value, MAX_SERIALIZATION_CONTAINERS,
};

impl Serialize for Object {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        SerializeWithBudget {
            value: self,
            remaining: MAX_SERIALIZATION_CONTAINERS,
        }
        .serialize(serializer)
    }
}

impl Serialize for SerializeWithBudget<'_, Object> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::Error;
        let remaining = serialization_child_budget::<S::Error>(self.remaining)?;
        let mut map = serializer.serialize_map(Some(self.value.len()))?;
        // Sorted iteration: canonical JSON.
        for (k, v) in self.value.iter_sorted() {
            let value = SerializeWithBudget {
                value: v,
                remaining,
            };
            match *k {
                Value::String(_) => map.serialize_entry(
                    &SerializeWithBudget {
                        value: k,
                        remaining,
                    },
                    &value,
                )?,
                _ => {
                    // Non-string keys retain their compact JSON string encoding.
                    let key_str = k.json_string(false).map_err(Error::custom)?;
                    map.serialize_entry(&key_str, &value)?;
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
        let seed = crate::value::ValueSeed(crate::utils::depth::MAX_DEPTH.saturating_sub(1), None);
        while let Some(k) = access.next_key_seed(seed)? {
            let v = access.next_value_seed(seed)?;
            // Key-only interning: dedup key `Rc<str>` allocations across objects
            // parsed within the same interning session. String *values* are left
            // untouched.
            #[cfg(feature = "std")]
            let k = match k {
                Value::String(rc) => Value::String(crate::value::interning::intern_key(rc)),
                other => other,
            };
            obj.insert(k, v);
            crate::utils::limits::check_memory_limit_if_needed()
                .map_err(|err| A::Error::custom(err.to_string()))?;
        }
        let obj = obj.freeze();
        // `freeze` allocates compact boxed-slice storage after the final insert; keep this
        // fallible deserialization path honest under allocator memory limits.
        crate::utils::limits::check_memory_limit_if_needed()
            .map_err(|err| A::Error::custom(err.to_string()))?;
        Ok(obj)
    }
}

impl<'de> Deserialize<'de> for Object {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_map(ObjectVisitor)
    }
}
