// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! ARM JSON → normalized `input.resource` transformation.
//!
//! The normalizer flattens `properties` wrappers from raw ARM resource JSON so
//! that alias short names become direct paths into the normalized structure.

mod alias_resolution;
mod element_remap;
mod flatten;

// Re-export items used by the denormalizer.
pub(crate) use element_remap::apply_element_remap_reverse;

use crate::Value;

use super::obj_map::{
    extract_type_field, make_value, new_map, obj_contains, obj_insert, val_str, ObjMap, ROOT_FIELDS,
};
use super::types::ResolvedAliases;
use super::AliasRegistry;

use flatten::{lowercase_object_keys, normalize_value};

/// Normalize a raw ARM resource JSON value into the `input.resource` structure.
///
/// The resource type is extracted from the `type` field of `arm_resource` and
/// used to look up alias entries in the registry.
pub fn normalize(
    arm_resource: &Value,
    registry: Option<&AliasRegistry>,
    api_version: Option<&str>,
) -> Value {
    let aliases = registry.and_then(|r| extract_type_field(arm_resource).and_then(|rt| r.get(rt)));
    normalize_with_aliases(arm_resource, aliases, api_version)
}

/// Internal normalization with pre-resolved alias data.
///
/// Core implementation used by [`normalize`] after looking up the alias
/// entries from the registry.  Also used directly in unit tests.
pub fn normalize_with_aliases(
    arm_resource: &Value,
    aliases: Option<&ResolvedAliases>,
    api_version: Option<&str>,
) -> Value {
    let obj = match arm_resource.as_object() {
        Ok(o) => o,
        Err(_) => return arm_resource.clone(),
    };

    let sub_arrays_ref = aliases.map(|a| &a.sub_resource_arrays);
    let mut result = new_map();

    let is_data_plane =
        extract_type_field(arm_resource).is_some_and(|t| t.to_ascii_lowercase().contains(".data/"));

    if is_data_plane {
        for (key, val) in obj {
            let key_s = match val_str(key) {
                Some(s) => s,
                None => continue,
            };
            if key_s.eq_ignore_ascii_case("properties") {
                continue;
            }
            let lc_key = key_s.to_ascii_lowercase();
            let val =
                if key_s.eq_ignore_ascii_case("tags") || key_s.eq_ignore_ascii_case("identity") {
                    lowercase_object_keys(val)
                } else {
                    normalize_value(val, key_s, sub_arrays_ref)
                };
            obj_insert(&mut result, &lc_key, val);
        }
        merge_properties(obj, &mut result, sub_arrays_ref);
    } else {
        // Copy root-level fields (keys lowercased).
        for &field in ROOT_FIELDS {
            let found = obj
                .iter()
                .find(|(k, _)| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case(field)))
                .map(|(_, v)| v);
            if let Some(val) = found {
                let val = if field.eq_ignore_ascii_case("tags")
                    || field.eq_ignore_ascii_case("identity")
                {
                    // Keep these shallow to avoid lowercasing dynamic nested-map
                    // keys such as userAssignedIdentities member names.
                    lowercase_object_keys(val)
                } else {
                    normalize_value(val, field, sub_arrays_ref)
                };
                obj_insert(&mut result, &field.to_ascii_lowercase(), val);
            }
        }
        merge_properties(obj, &mut result, sub_arrays_ref);
    }

    // Per-alias path resolution.
    if let Some(aliases) = aliases {
        alias_resolution::apply_alias_entries(&mut result, arm_resource, aliases, api_version);
    }

    make_value(result)
}

/// Merge `properties` fields into the result map, skipping keys that already
/// exist.
fn merge_properties(
    obj: &alloc::collections::BTreeMap<Value, Value>,
    result: &mut ObjMap,
    sub_arrays: Option<&alloc::collections::BTreeSet<alloc::string::String>>,
) {
    let props_val = obj
        .iter()
        .find(|(k, _)| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case("properties")))
        .map(|(_, v)| v);
    if let Some(Value::Object(props)) = props_val {
        for (key, val) in props.iter() {
            let key_s = match val_str(key) {
                Some(s) => s,
                None => continue,
            };
            let lc_key = key_s.to_ascii_lowercase();
            if obj_contains(result, &lc_key) {
                continue;
            }
            let normalized = normalize_value(val, key_s, sub_arrays);
            obj_insert(result, &lc_key, normalized);
        }
    }
}

/// Wrap a normalized resource into the full `input` envelope.
///
/// Produces: `{ "resource": <normalized>, "context": <context>, "parameters": <params> }`
pub fn build_input_envelope(
    normalized_resource: Value,
    context: Option<Value>,
    parameters: Option<Value>,
) -> Value {
    let mut envelope = new_map();
    obj_insert(&mut envelope, "resource", normalized_resource);
    obj_insert(
        &mut envelope,
        "context",
        context.unwrap_or_else(|| make_value(new_map())),
    );
    obj_insert(
        &mut envelope,
        "parameters",
        parameters.unwrap_or_else(|| make_value(new_map())),
    );
    make_value(envelope)
}
