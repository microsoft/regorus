// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::unused_trait_names)]

use crate::registry::instances::{EFFECT_SCHEMA_REGISTRY, RESOURCE_SCHEMA_REGISTRY};
use crate::{format, Rc, Schema, Vec};
use alloc::collections::BTreeMap;
use serde::de::{Deserializer, Error};
use serde::Deserialize;
type String = Rc<str>;

/// Deserialize resource schemas from either an array of schemas or schema names.
/// If specified as schema names, look them up from RESOURCE_SCHEMA_REGISTRY.
pub fn deserialize_resource_schemas<'de, D>(deserializer: D) -> Result<Vec<Rc<Schema>>, D::Error>
where
    D: Deserializer<'de>,
{
    let array: Vec<serde_json::Value> = Vec::deserialize(deserializer)
        .map_err(|e| D::Error::custom(format!("Failed to deserialize resource_schemas: {}", e)))?;

    let mut schemas = Vec::new();

    for item in array.into_iter() {
        let schema =
            if let Some(name) = item.as_str() {
                // Look up schema by name in the registry
                RESOURCE_SCHEMA_REGISTRY.get(name).ok_or_else(|| {
                    D::Error::custom(format!("Resource schema '{}' not found in registry", name))
                })?
            } else {
                // Treat as a direct schema definition
                Rc::new(Schema::deserialize(item.clone()).map_err(|e| {
                    D::Error::custom(format!("Failed to deserialize schema: {}", e))
                })?)
            };

        // Assert that the schema represents an object type
        if !matches!(schema.as_type(), crate::schema::Type::Object { .. }) {
            return Err(D::Error::custom("Resource schema must be an object type"));
        }

        schemas.push(schema);
    }

    Ok(schemas)
}

/// Deserialize effects from either an object of schemas or schema names.
/// If specified as schema names, look them up from EFFECT_SCHEMA_REGISTRY.
pub fn deserialize_effects<'de, D>(
    deserializer: D,
) -> Result<BTreeMap<String, Rc<Schema>>, D::Error>
where
    D: Deserializer<'de>,
{
    let object: BTreeMap<String, serde_json::Value> = BTreeMap::deserialize(deserializer)
        .map_err(|e| D::Error::custom(format!("Failed to deserialize effects: {}", e)))?;

    let mut effects = BTreeMap::new();

    for (key, item) in object.into_iter() {
        if let Some(name) = item.as_str() {
            // Look up schema by name in the registry
            let schema = EFFECT_SCHEMA_REGISTRY.get(name).ok_or_else(|| {
                D::Error::custom(format!("Effect schema '{}' not found in registry", name))
            })?;
            effects.insert(key, schema);
        } else {
            // Treat as a direct schema definition
            let schema = Schema::deserialize(item.clone())
                .map_err(|e| D::Error::custom(format!("Failed to deserialize schema: {}", e)))?;
            effects.insert(key, Rc::new(schema));
        }
    }

    Ok(effects)
}
