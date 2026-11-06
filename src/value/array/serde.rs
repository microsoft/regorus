// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Serde `Serialize`/`Deserialize` impls for [`Array`].

use core::fmt;

use serde::de::{Deserialize, Deserializer, Error as _, SeqAccess, Visitor};
use serde::ser::{Serialize, Serializer};

use super::Array;
use crate::value::{
    serialization_child_budget, SerializeWithBudget, Value, MAX_SERIALIZATION_CONTAINERS,
};

impl Serialize for Array {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        SerializeWithBudget {
            value: self,
            remaining: MAX_SERIALIZATION_CONTAINERS,
            limit_error: None,
        }
        .serialize(serializer)
    }
}

impl Serialize for SerializeWithBudget<'_, Array> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let remaining = serialization_child_budget::<S::Error>(self.remaining, self.limit_error)?;
        serializer.collect_seq(self.value.iter().map(|value| SerializeWithBudget {
            value,
            remaining,
            limit_error: self.limit_error,
        }))
    }
}

struct ArrayVisitor;

impl<'de> Visitor<'de> for ArrayVisitor {
    type Value = Array;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a sequence of Values")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut array = Array::new();
        while let Some(v) = access.next_element::<Value>()? {
            array.push(v);
            crate::utils::limits::check_memory_limit_if_needed().map_err(A::Error::custom)?;
        }
        Ok(array)
    }
}

impl<'de> Deserialize<'de> for Array {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_seq(ArrayVisitor)
    }
}
