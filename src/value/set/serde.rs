// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Serde `Serialize`/`Deserialize` impls for [`Set`].

use core::fmt;

use serde::de::{Deserialize, Deserializer, Error as _, SeqAccess, Visitor};
use serde::ser::{Serialize, Serializer};

use super::Set;
use crate::value::Value;

impl Serialize for Set {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // Sets serialize as JSON arrays. Sorted iteration: canonical output.
        serializer.collect_seq(self.iter_sorted())
    }
}

struct SetVisitor;

impl<'de> Visitor<'de> for SetVisitor {
    type Value = Set;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a sequence of Values")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
        let mut set = Set::new();
        while let Some(v) = access.next_element::<Value>()? {
            set.insert(v);
            crate::utils::limits::check_memory_limit_if_needed().map_err(A::Error::custom)?;
        }
        Ok(set)
    }
}

impl<'de> Deserialize<'de> for Set {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_seq(SetVisitor)
    }
}
