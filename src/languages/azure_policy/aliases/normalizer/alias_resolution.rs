// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Per-alias path resolution: reads values from versioned ARM paths and places
//! them at alias short name paths in the normalized output.

use alloc::string::String;

use crate::Value;

use super::super::obj_map::remove_element_field;
use super::super::obj_map::{
    collision_safe_key, is_root_field_collision, obj_contains, obj_insert, obj_remove,
    set_nested_lowercased, ObjMap,
};
use super::super::types::ResolvedAliases;
use super::element_remap::apply_element_remap_precomputed;
use super::flatten::normalize_value;

/// Apply per-alias path resolution to the normalized result.
///
/// Uses precomputed element remaps and array renames from [`ResolvedAliases`]
/// when `api_version` is `None` (the common case). Falls back to dynamic
/// computation when a specific `api_version` is provided.
pub fn apply_alias_entries(
    result: &mut ObjMap,
    raw: &Value,
    aliases: &ResolvedAliases,
    api_version: Option<&str>,
) {
    let entries = &aliases.entries;
    let sub_resource_set = &aliases.sub_resource_arrays;

    for (lc_key, entry) in entries {
        if entry.is_wildcard {
            continue;
        }

        // Skip sub-resource array root entries.
        if sub_resource_set.contains(lc_key.as_str()) {
            continue;
        }

        // Use precomputed segments for all paths (default and versioned).
        let segments = entry.select_path_segments(api_version);
        let value = navigate_arm_path_segments(raw, segments);

        if let Some(value) = value {
            let value = normalize_value(&value, &entry.short_name, None);

            let target = if is_root_field_collision(&entry.short_name, &entry.default_path) {
                collision_safe_key(&entry.short_name)
            } else {
                entry.short_name.clone()
            };
            set_nested_lowercased(result, &target, value);
        }
    }

    // Look up precomputed aggregates: default or per-version.
    let agg = api_version.map_or(&aliases.default_aggregates, |ver| {
        let ver_lc = ver.to_ascii_lowercase();
        aliases
            .versioned_aggregates
            .get(&ver_lc)
            .unwrap_or(&aliases.default_aggregates)
    });

    for remap in &agg.element_remaps {
        apply_element_remap_precomputed(result, remap);
        // Remove the original ARM field so the normalized output only has the
        // alias short name.  Without this, the stale source key survives and
        // casing restoration during denormalization can produce a duplicate.
        remove_element_field(result, &remap.array_chain, &remap.source_field);
    }

    for (source_lc, target_lc) in &agg.array_renames_normalize {
        if !obj_contains(result, target_lc.as_str()) {
            if let Some(val) = obj_remove(result, source_lc.as_str()) {
                obj_insert(result, target_lc, val);
            }
        }
    }
}

/// Navigate an ARM path using precomputed segments (avoids per-call split).
fn navigate_arm_path_segments(value: &Value, segments: &[String]) -> Option<Value> {
    let mut current = value;
    for segment in segments {
        current = current
            .as_object()
            .ok()?
            .get(&Value::from(segment.as_str()))?;
    }
    Some(current.clone())
}
