// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::ptr;
use core::sync::atomic::{AtomicPtr, Ordering};

use crate::builtins;

use lazy_static::lazy_static;

use super::catalog::{BuiltinCatalog, BuiltinGroupConfig};
use super::spec::{BuiltinSpec, BuiltinTableError};

const DEFAULT_BUILTINS_JSON: &str = include_str!("./builtins.json");

#[derive(Default)]
pub(super) struct BuiltinTable {
    entries: BTreeMap<String, BuiltinSpec>,
}

impl BuiltinTable {
    fn from_json(json: &str) -> Result<Self, BuiltinTableError> {
        let mut catalog: BuiltinCatalog = serde_json::from_str(json)?;

        if !catalog.builtins.is_empty() {
            catalog.groups.push(BuiltinGroupConfig {
                name: "default".to_owned(),
                requires: Vec::new(),
                builtins: catalog.builtins,
            });
            catalog.builtins = Vec::new();
        }

        let mut entries = BTreeMap::new();

        for group in catalog.groups.into_iter() {
            if !group.is_enabled()? {
                continue;
            }

            for builtin in group.builtins.iter() {
                let spec = BuiltinSpec::from_config(&builtin.name, builtin)?;
                if entries.insert(builtin.name.clone(), spec).is_some() {
                    return Err(BuiltinTableError::DuplicateBuiltin(builtin.name.clone()));
                }
            }
        }

        Ok(BuiltinTable { entries })
    }

    fn lookup(&self, name: &str) -> Option<BuiltinSpec> {
        self.entries.get(name).cloned()
    }
}

lazy_static! {
    static ref DEFAULT_TABLE: BuiltinTable = BuiltinTable::from_json(DEFAULT_BUILTINS_JSON)
        .expect("failed to load default builtin specifications");
}

static CUSTOM_TABLE: AtomicPtr<BuiltinTable> = AtomicPtr::new(ptr::null_mut());

pub fn override_builtin_table(json: &str) -> Result<(), BuiltinTableError> {
    let table = Box::new(BuiltinTable::from_json(json)?);
    set_custom_table(Some(table));
    Ok(())
}

pub fn reset_builtin_table() {
    set_custom_table(None);
}

fn set_custom_table(table: Option<Box<BuiltinTable>>) {
    let new_ptr = match table {
        Some(table) => Box::into_raw(table),
        None => ptr::null_mut(),
    };

    let old_ptr = CUSTOM_TABLE.swap(new_ptr, Ordering::SeqCst);
    if !old_ptr.is_null() {
        // Safety: pointer was created with Box::into_raw.
        unsafe { drop(Box::from_raw(old_ptr)) };
    }
}

fn active_table() -> &'static BuiltinTable {
    let custom_ptr = CUSTOM_TABLE.load(Ordering::SeqCst);
    if custom_ptr.is_null() {
        &DEFAULT_TABLE
    } else {
        // Safety: pointer originates from Box::into_raw and lives until reset/override.
        unsafe { &*custom_ptr }
    }
}

pub fn lookup(name: &str) -> Option<BuiltinSpec> {
    if let Some(spec) = active_table().lookup(name) {
        return Some(spec);
    }

    if let Some((_, nargs)) = builtins::BUILTINS.get(name) {
        return Some(BuiltinSpec::fallback(*nargs));
    }

    None
}
