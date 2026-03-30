// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Key casing restoration from alias metadata.

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use crate::Value;

use super::super::obj_map::{make_array, make_value, new_map, obj_insert, val_str, ROOT_FIELDS};
use super::super::types::ResolvedEntry;

fn insert_default_casing(map: &mut BTreeMap<String, String>) {
    for &field in ROOT_FIELDS {
        map.insert(field.to_ascii_lowercase(), field.to_string());
    }

    // Canonical casing for standard nested root-field object members that are
    // not described by alias metadata but still need round-trip restoration.
    for canonical in [
        "principalId",
        "tenantId",
        "userAssignedIdentities",
        "promotionCode",
        "createdBy",
        "createdByType",
        "createdAt",
        "lastModifiedBy",
        "lastModifiedByType",
        "lastModifiedAt",
    ] {
        map.entry(canonical.to_ascii_lowercase())
            .or_insert_with(|| canonical.to_string());
    }
}

/// Build the default casing map used when alias metadata is unavailable.
pub fn default_casing_map() -> BTreeMap<String, String> {
    let mut map = BTreeMap::new();
    insert_default_casing(&mut map);
    map
}

/// Build a mapping from lowercase key → original-cased key from alias entries.
pub fn build_casing_map(entries: &BTreeMap<String, ResolvedEntry>) -> BTreeMap<String, String> {
    let mut map = BTreeMap::new();
    insert_default_casing(&mut map);

    for entry in entries.values() {
        for segment in entry.short_name.split('.') {
            let clean = segment.replace("[*]", "");
            if !clean.is_empty() {
                map.entry(clean.to_ascii_lowercase())
                    .or_insert_with(|| clean.to_string());
            }
        }

        for segment in entry.default_path.split('.') {
            let clean = segment.replace("[*]", "");
            if !clean.is_empty() && !clean.eq_ignore_ascii_case("properties") {
                map.entry(clean.to_ascii_lowercase())
                    .or_insert_with(|| clean.to_string());
            }
        }

        // Also include segments from all version-specific ARM paths so
        // casing can be restored correctly for versioned aliases.
        for (_ver, path) in &entry.versioned_paths {
            for segment in path.split('.') {
                let clean = segment.replace("[*]", "");
                if !clean.is_empty() && !clean.eq_ignore_ascii_case("properties") {
                    map.entry(clean.to_ascii_lowercase())
                        .or_insert_with(|| clean.to_string());
                }
            }
        }
    }

    map
}

/// Restore the original casing of a key using the casing map.
pub fn restore_casing(key: &str, casing_map: &BTreeMap<String, String>) -> String {
    casing_map
        .get(&key.to_ascii_lowercase())
        .cloned()
        .unwrap_or_else(|| key.to_string())
}

/// Recursively restore key casing in a JSON value.
pub fn denormalize_value(value: &Value, casing_map: &BTreeMap<String, String>) -> Value {
    match value {
        Value::Object(obj) => {
            let mut result = new_map();
            for (k, v) in obj.iter() {
                if let Some(key_s) = val_str(k) {
                    let restored_key = restore_casing(key_s, casing_map);
                    obj_insert(&mut result, &restored_key, denormalize_value(v, casing_map));
                }
            }
            make_value(result)
        }
        Value::Array(arr) => {
            let items: Vec<Value> = arr
                .iter()
                .map(|v| denormalize_value(v, casing_map))
                .collect();
            make_array(items)
        }
        _ => value.clone(),
    }
}
