// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Normalized `input.resource` → ARM JSON reverse transformation.

mod casing;
pub(crate) mod helpers;
mod sub_resource;

#[cfg(test)]
mod tests;

use alloc::collections::BTreeSet;

use crate::Value;

use crate::Rc;

use super::obj_map::{
    extract_type_field, is_root_field_collision, make_value, new_map, obj_insert,
    set_nested_verbatim, val_str, ROOT_FIELDS,
};
use super::types::ResolvedAliases;
use super::AliasRegistry;

use super::normalizer::{apply_element_remap, ElementRemap};

use casing::{build_casing_map, default_casing_map, denormalize_value, restore_casing};
use helpers::find_key_ci;

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

    let entries = aliases.map(|a| &a.entries);
    let casing_map = entries
        .map(build_casing_map)
        .unwrap_or_else(default_casing_map);
    let empty_set = BTreeSet::new();
    let sub_resource_set = aliases.map_or(&empty_set, |a| &a.sub_resource_arrays);

    let is_data_plane =
        extract_type_field(normalized).is_some_and(|t| t.to_ascii_lowercase().contains(".data/"));

    let mut result = new_map();
    let mut properties = new_map();

    // Phase 1: Root fields → ARM root with original casing.
    for &field in ROOT_FIELDS {
        let lc = field.to_ascii_lowercase();
        // Fast-path: direct BTreeMap lookup (O(log N)) for the common case
        // where normalized input was produced by our normalizer with lowercase keys.
        // Falls back to linear case-insensitive scan for externally-supplied mixed-case input.
        let lc_key = Value::String(Rc::from(lc.as_str()));
        let found = obj.get(&lc_key).or_else(|| {
            obj.iter()
                .find(|(k, _)| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case(&lc)))
                .map(|(_, v)| v)
        });
        if let Some(val) = found {
            let restored = denormalize_value(val, &casing_map);
            obj_insert(&mut result, field, restored);
        }
    }

    // What phases 2a, 2b and 2c write, in order; later phases look for plain
    // aliases at their ARM paths, and wrap only arrays still flattened.
    let mut writes = sub_resource::Writes::default();

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
        let has_alias = entries.is_some_and(|e| e.contains_key(lookup_key_lc.as_str()));
        if has_alias {
            continue;
        }

        let denorm_val = denormalize_value(val, &casing_map);

        if key_s.starts_with("_p_") {
            let restored = restore_casing(lookup_key, &casing_map);
            writes.record_key(false, &restored, lookup_key, key_s);
            obj_insert(&mut properties, &restored, denorm_val);
        } else if is_data_plane {
            let restored = restore_casing(key_s, &casing_map);
            writes.record_key(true, &restored, key_s, key_s);
            obj_insert(&mut result, &restored, denorm_val);
        } else {
            let restored = restore_casing(key_s, &casing_map);
            writes.record_key(false, &restored, key_s, key_s);
            obj_insert(&mut properties, &restored, denorm_val);
        }
    }

    // Phase 2b: Aliased scalar fields → versioned ARM paths.
    if let Some(entries) = entries {
        for (lc_key, entry) in entries {
            if entry.is_wildcard {
                continue;
            }

            if sub_resource_set.contains(lc_key.as_str()) {
                continue;
            }

            let normalized_key = if is_root_field_collision(&entry.short_name, &entry.default_path)
            {
                alloc::format!("_p_{}", entry.short_name.to_ascii_lowercase())
            } else {
                lc_key.clone()
            };

            // Fast-path: direct BTreeMap lookup for lowercase keys,
            // with case-insensitive fallback for mixed-case external input.
            let nk_val = Value::String(Rc::from(normalized_key.as_str()));
            let found = obj.get(&nk_val).map(|v| (&nk_val, v)).or_else(|| {
                obj.iter().find(|(k, _)| {
                    val_str(k).is_some_and(|s| s.eq_ignore_ascii_case(&normalized_key))
                })
            });
            let Some((read, val)) = found.and_then(|(k, v)| Some((val_str(k)?, v))) else {
                continue;
            };

            let arm_path = entry.select_path(api_version);
            let denorm_val = denormalize_value(val, &casing_map);

            // A write refused by a non-object on the way leaves no value.
            if let Some(props_path) = arm_path.strip_prefix("properties.") {
                if set_nested_verbatim(&mut properties, props_path, denorm_val) {
                    writes.record_alias(false, props_path, lc_key, read);
                }
            } else if set_nested_verbatim(&mut result, arm_path, denorm_val) {
                writes.record_alias(true, arm_path, lc_key, read);
            }
        }

        // Phase 2c + 2d: Use precomputed renames/remaps.
        // Look up versioned aggregates when api_version is provided,
        // falling back to default aggregates.
        if let Some(aliases) = aliases {
            let agg = api_version.map_or(&aliases.default_aggregates, |ver| {
                let ver_lc = ver.to_ascii_lowercase();
                aliases
                    .versioned_aggregates
                    .get(&ver_lc)
                    .unwrap_or(&aliases.default_aggregates)
            });

            // Phase 2c: Precomputed array base renames.
            for (alias_base_lc, arm_base) in &agg.array_renames_denormalize {
                if let Some(key) = find_key_ci(&properties, alias_base_lc) {
                    if let Some(val) = properties.remove(key.as_ref()) {
                        obj_insert(&mut properties, arm_base, val);
                        // The normalizer flattened and remapped this value under its ARM name.
                        let read = writes
                            .read_at(&key)
                            .unwrap_or_else(|| alloc::string::String::from(&*key));
                        writes.record_key(false, arm_base, arm_base, &read);
                    }
                }
            }

            // Phase 2d: Precomputed reverse element-level field remaps.
            for rev in &agg.reverse_element_remaps {
                let remap = ElementRemap {
                    array_chain: rev.array_chain.clone(),
                    source_field: rev.source_field.clone(),
                    target_field: if rev.target_field.contains('.') {
                        rev.target_field
                            .split('.')
                            .map(|segment| restore_casing(segment, &casing_map))
                            .collect::<alloc::vec::Vec<_>>()
                            .join(".")
                    } else {
                        restore_casing(&rev.target_field, &casing_map)
                    },
                };
                // Follow an outer array phase 2b moved to its ARM path.
                // Otherwise phase 2a wrote it: at the root of a data-plane
                // resource when the alias's arrays are there under the same
                // names, else in `properties`.
                let (at_root, array_chain) =
                    sub_resource::redirect_chain(&remap.array_chain, entries, api_version, &writes)
                        .unwrap_or_else(|| {
                            (is_data_plane && rev.at_root, remap.array_chain.clone())
                        });
                // Another alias's value replaced this one there; it was not
                // remapped with this alias's names.
                // Check the keys the remap will reach, so an older write to an
                // exact ancestor does not hide a later write that differs in case.
                if let (Some(outer), Some(name)) = (array_chain.first(), remap.array_chain.first())
                {
                    let map = if at_root { &result } else { &properties };
                    let outer: alloc::vec::Vec<&str> =
                        outer.iter().map(|key| key.as_str()).collect();
                    let reached = sub_resource::output_keys(map, &outer);
                    if writes.replaced(at_root, &reached, name) {
                        continue;
                    }
                }
                let map = if at_root {
                    &mut result
                } else {
                    &mut properties
                };
                let remap = ElementRemap {
                    array_chain,
                    ..remap
                };
                apply_element_remap(map, &remap, false);
            }
        }
    }

    // Phase 3: Re-wrap sub-resource array elements.
    if let Some(aliases) = aliases {
        if !aliases.sub_resource_arrays.is_empty() {
            let cx = sub_resource::Context {
                entries: &aliases.entries,
                api_version,
                writes: &writes,
                is_data_plane,
                casing_map: &casing_map,
                normalized: obj,
            };
            sub_resource::rewrap_sub_resource_arrays(
                &mut result,
                &mut properties,
                &aliases.sub_resource_arrays,
                &cx,
            );
        }
    }

    // Phase 4: Attach properties to result.
    if !properties.is_empty() {
        if let Some(Value::Object(existing_rc)) = result.get_mut("properties") {
            // Merge directly into the Object, avoiding full ObjMap round-trip.
            let existing = Rc::make_mut(existing_rc);
            for (k, v) in properties {
                existing.get_or_insert_with(Value::String(k), || v);
            }
        } else {
            obj_insert(&mut result, "properties", make_value(properties));
        }
    }

    make_value(result)
}
