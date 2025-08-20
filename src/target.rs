// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(dead_code)]
use crate::{Rc, Schema, Value, Vec};
use alloc::collections::BTreeMap;
use serde::Deserialize;

mod deserialize;
mod error;
mod resource_schema_selector;

type String = Rc<str>;

use deserialize::{deserialize_effects, deserialize_resource_schemas};
pub use error::TargetError;

/// A target defines the domain for which a set of policies are written.
/// It specifies the types of input resources, possible policy effects,
/// and configuration for policy evaluation.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Target {
    /// Name of the target domain
    /// A Rego module can specify a target by defining a rule named `__target__`:
    ///       __target__ = "my_target"
    pub name: String,

    /// Description of what this target is for
    pub description: Option<String>,

    /// Version of the target
    pub version: String,

    /// Types of input resources that policies can evaluate
    #[serde(deserialize_with = "deserialize_resource_schemas")]
    pub resource_schemas: Vec<Rc<Schema>>,

    /// The discriminator property that can be used to select
    /// a specific resource schema
    pub resource_schema_selector: String,

    /// Set of effects that policies can produce
    #[serde(deserialize_with = "deserialize_effects")]
    pub effects: BTreeMap<String, Rc<Schema>>,
    /// Lookup table for resource schemas by discrimiator values.
    #[serde(skip)]
    pub resource_schema_lookup: BTreeMap<Value, Rc<Schema>>,

    /// Resource chemas that cannot be distinguished by the discriminator
    #[serde(skip)]
    pub default_resource_schema: Option<Rc<Schema>>,
}

impl Target {
    pub fn from_json_str(json: &str) -> Result<Self, TargetError> {
        let mut target: Target = serde_json::from_str(json).map_err(TargetError::from)?;

        // Validate that resource schemas is not empty
        if target.resource_schemas.is_empty() {
            return Err(TargetError::EmptyResourceSchemas(
                "Target must have at least one resource schema defined".into(),
            ));
        }

        if target.effects.is_empty() {
            return Err(TargetError::EmptyEffectSchemas(
                "Target must have at least one effect defined".into(),
            ));
        }

        resource_schema_selector::populate_target_lookup_fields(&mut target)?;
        Ok(target)
    }
}

#[cfg(test)]
mod tests {
    mod deserialize;
}
