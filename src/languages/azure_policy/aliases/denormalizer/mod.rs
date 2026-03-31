// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Normalized `input.resource` → ARM JSON reverse transformation.

pub(crate) mod casing;
pub(crate) mod sub_resource;

#[cfg(test)]
mod tests;

use crate::Value;

use crate::Rc;

use super::obj_map::{
    extract_type_field, find_key_ci, get_path_exact_or_ci, make_value, new_map,
    obj_get_exact_or_ci, obj_insert, remove_element_field, set_nested, val_str, ROOT_FIELDS,
};
use super::types::ResolvedAliases;
use super::AliasRegistry;

use super::normalizer::{apply_element_remap, ElementRemap};

use casing::{default_casing_map, denormalize_value, restore_casing};

/// Denormalize a normalized resource back to ARM JSON structure.
pub fn denormalize(
    normalized: &Value,
    registry: Option<&AliasRegistry>,
    api_version: Option<&str>,
) -> Value {
    let aliases = registry.and_then(|r| extract_type_field(normalized).and_then(|rt| r.get(rt)));
    denormalize_with_aliases(normalized, aliases, api_version)
}

/// Internal denormalization with pre-resolved alias data.
pub fn denormalize_with_aliases(
    normalized: &Value,
    aliases: Option<&ResolvedAliases>,
    api_version: Option<&str>,
) -> Value {
    let obj = match normalized.as_object() {
        Ok(o) => o,
        Err(_) => return normalized.clone(),
    };

    let selected_agg = aliases.map(|a| a.select_aggregates(api_version));
    let default_cm = default_casing_map();
    let casing_map = aliases.map_or(&default_cm, |a| &a.casing_map);
    let is_data_plane =
        extract_type_field(normalized).is_some_and(|t| t.to_ascii_lowercase().contains(".data/"));

    let mut result = new_map();
    let mut properties = new_map();

    // Phase 1: Root fields → ARM root with original casing.
    for &field in ROOT_FIELDS {
        let lc = field.to_ascii_lowercase();
        let found = obj_get_exact_or_ci(obj, &lc);
        if let Some(val) = found {
            let restored = denormalize_value(val, casing_map);
            obj_insert(&mut result, field, restored);
        }
    }

    // Phase 2a: Non-aliased, non-root fields.
    for (key, val) in obj.iter() {
        let key_s = match val_str(key) {
            Some(s) => s,
            None => continue,
        };
        if ROOT_FIELDS.iter().any(|f| f.eq_ignore_ascii_case(key_s)) {
            continue;
        }

        let lookup_key = key_s.strip_prefix("_p_").unwrap_or(key_s);
        let lookup_key_lc = lookup_key.to_ascii_lowercase();
        let has_alias = selected_agg.is_some_and(|agg| {
            agg.alias_owned_normalized_roots
                .contains(lookup_key_lc.as_str())
        });
        if has_alias {
            continue;
        }

        let denorm_val = denormalize_value(val, casing_map);

        if key_s.starts_with("_p_") {
            let restored = restore_casing(lookup_key, casing_map);
            obj_insert(&mut properties, &restored, denorm_val);
        } else if is_data_plane {
            let restored = restore_casing(key_s, casing_map);
            obj_insert(&mut result, &restored, denorm_val);
        } else {
            let restored = restore_casing(key_s, casing_map);
            obj_insert(&mut properties, &restored, denorm_val);
        }
    }

    // Phase 2b: Aliased scalar fields → versioned ARM paths.
    if let Some(agg) = selected_agg {
        for op in &agg.scalar_aliases_denormalize {
            let segments: alloc::vec::Vec<&str> = op
                .normalized_path_segments
                .iter()
                .map(|segment| segment.as_str())
                .collect();
            let val = get_path_exact_or_ci(obj, &segments);
            let val = match val {
                Some(v) => v,
                None => continue,
            };

            let denorm_val = denormalize_value(val, casing_map);

            if op.write_to_properties {
                let props_path = op
                    .arm_path
                    .strip_prefix("properties.")
                    .unwrap_or(&op.arm_path);
                set_nested(&mut properties, props_path, denorm_val, false);
            } else {
                set_nested(&mut result, &op.arm_path, denorm_val, false);
            }
        }

        // Phase 2c + 2d: Use precomputed renames/remaps.
        // Phase 2c: Precomputed array base renames.
        for (alias_base_lc, arm_base) in &agg.array_renames_denormalize {
            if let Some(key) = find_key_ci(&properties, alias_base_lc) {
                if let Some(val) = properties.remove(&key) {
                    obj_insert(&mut properties, arm_base, val);
                }
            }
        }

        // Phase 2d: Precomputed reverse element-level field remaps.
        // target_field is already stored with original ARM casing.
        for rev in &agg.reverse_element_remaps {
            let remap = ElementRemap {
                array_chain: rev.array_chain.clone(),
                source_field: rev.source_field.clone(),
                target_field: rev.target_field.clone(),
            };
            apply_element_remap(&mut properties, &remap, false);
            remove_element_field(&mut properties, &rev.array_chain, &rev.cleanup_field);
        }
    }

    // Phase 3: Re-wrap sub-resource array elements.
    if let Some(agg) = selected_agg {
        if !agg.sub_resource_rewraps.is_empty() {
            sub_resource::rewrap_precomputed_sub_resource_arrays(
                &mut properties,
                &agg.sub_resource_rewraps,
            );
        }
    }

    // Phase 4: Attach properties to result.
    if !properties.is_empty() {
        let props_key = Value::from("properties");
        if let Some(Value::Object(existing_rc)) = result.get_mut(&props_key) {
            let existing = Rc::make_mut(existing_rc);
            for (k, v) in properties {
                existing.entry(k).or_insert(v);
            }
        } else {
            obj_insert(&mut result, "properties", make_value(properties));
        }
    }

    make_value(result)
}
