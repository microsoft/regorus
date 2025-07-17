// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::schema::*;
use crate::*;
use anyhow::{bail, Result};
use dashmap::DashMap;
use serde::{Deserialize, Serialize};

use lazy_static::lazy_static;
use std::collections::HashMap;

#[derive(Deserialize, Serialize, Debug, Default)]
#[serde(rename_all = "camelCase")]
pub struct Target {
    /// Target identifier.
    id: String,

    /// Schemas of the entities that will be validated
    /// via policies written for this target.
    resource_types: HashMap<String, Schema>,

    /// Schemas of the effects that policies can return.
    effects: HashMap<String, Schema>,
}

lazy_static! {
    static ref TARGETS: DashMap<String, Rc<Target>> = DashMap::new();
}

pub fn add_target(target_json: &str) -> Result<()> {
    let target: Target = serde_json::from_str(target_json)?;
    if let dashmap::Entry::Vacant(vacant_entry) = TARGETS.entry(target.id.clone()) {
        vacant_entry.insert(Rc::new(target));
    } else {
        bail!("Target {} already exists.", target.id);
    }

    Ok(())
}

pub fn remove_target(target_id: &str) -> Result<()> {
    TARGETS.remove(target_id);

    Ok(())
}

#[allow(dead_code)]
pub fn get_target(target_id: &str) -> Option<Rc<Target>> {
    TARGETS.get(target_id).map(|r| r.value().clone())
}
