// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Per-alias path resolution: reads values from versioned ARM paths and places
//! them at alias short name paths in the normalized output.

use crate::Value;

use super::super::obj_map::remove_element_field;
use super::super::obj_map::{
    get_value_path_segments, obj_contains, obj_insert, obj_remove, set_nested, ObjMap,
};
use super::super::types::ResolvedAliases;
use super::element_remap::apply_element_remap_precomputed;
use super::flatten::normalize_value;

/// Apply per-alias path resolution to the normalized result.
///
/// Uses precomputed aggregates from [`ResolvedAliases`], selecting the
/// version-specific set when `api_version` is `Some` or the default
/// aggregates otherwise.  All work is driven by pre-built operation
/// lists; no per-call dynamic computation is required.
pub fn apply_alias_entries(
    result: &mut ObjMap,
    raw: &Value,
    aliases: &ResolvedAliases,
    api_version: Option<&str>,
) {
    let agg = aliases.select_aggregates(api_version);

    for op in &agg.scalar_aliases_normalize {
        let value = get_value_path_segments(raw, &op.arm_path_segments).cloned();

        if let Some(value) = value {
            let value = normalize_value(&value, &op.short_name, None);
            set_nested(result, &op.normalized_path, value, true);
        }
    }

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
