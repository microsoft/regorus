// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Azure Policy alias resolution and ARM resource normalization.
//!
//! This module provides:
//! - [`types`]: Data types for deserializing production alias catalogs
//! - [`normalizer`]: ARM JSON → normalized `input.resource` transformation
//!
//! # Overview
//!
//! Azure Policy aliases are short names for ARM JSON paths. For example,
//! `Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly` maps to the
//! ARM path `properties.supportsHttpsTrafficOnly`.
//!
//! The normalizer transforms raw ARM resource JSON into a flat structure where
//! alias short names are direct paths. This means the compiler and VM never
//! need to know about aliases — the normalizer handles the translation once
//! before evaluation.

pub mod denormalizer;
pub mod normalizer;
pub(crate) mod obj_map;
pub mod types;

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use anyhow::Result;

use types::{
    AliasEntry, AliasPath, DataPolicyManifest, PrecomputedRemap, PrecomputedReverseRemap,
    ProviderAliases, ResolvedAliases, ResolvedEntry, VersionedAggregates,
};

use obj_map::{collision_safe_key, is_root_field_collision};

/// Registry of resolved alias data, keyed by fully-qualified resource type
/// (case-insensitive, stored lowercase).
#[derive(Debug, Clone, Default)]
pub struct AliasRegistry {
    /// Map from lowercase resource type → resolved alias data.
    types: BTreeMap<String, ResolvedAliases>,
    /// Global reverse lookup: lowercase fully-qualified alias name → short name.
    ///
    /// Built during [`load_provider`] so the compiler can resolve any alias
    /// to its short name without knowing the resource type.
    alias_to_short: BTreeMap<String, String>,
    /// Global lookup: lowercase fully-qualified alias name → modifiable flag.
    ///
    /// `true` when `defaultMetadata.attributes == "Modifiable"`, `false` otherwise.
    alias_modifiable: BTreeMap<String, bool>,
}

impl AliasRegistry {
    /// Create a new empty registry.
    pub const fn new() -> Self {
        Self {
            types: BTreeMap::new(),
            alias_to_short: BTreeMap::new(),
            alias_modifiable: BTreeMap::new(),
        }
    }

    /// Load alias data from a JSON string.
    ///
    /// Accepts either a bare JSON array of `ProviderAliases` objects or an
    /// ARM-style `{ "value": [...] }` envelope, as produced by
    /// `Get-AzPolicyAlias` or the ARM provider metadata API.
    ///
    /// Multiple calls accumulate data; duplicates overwrite earlier entries.
    pub fn load_from_json(&mut self, json: &str) -> Result<()> {
        let providers: Vec<ProviderAliases> = types::load_auto(json)?;
        for provider in providers {
            self.load_provider(provider);
        }
        Ok(())
    }

    /// Load alias data from a data policy manifest JSON string.
    ///
    /// Data policy manifests describe data-plane aliases (e.g.,
    /// `Microsoft.KeyVault.Data`, `Microsoft.DataFactory.Data`).  Their format
    /// differs from the control-plane `ProviderAliases` catalog: aliases use
    /// `paths[0].path` instead of `defaultPath`, and may include both
    /// top-level aliases and per-resource-type groups.
    ///
    /// Multiple calls accumulate data; duplicates overwrite earlier entries.
    pub fn load_data_policy_manifest_json(&mut self, json: &str) -> Result<()> {
        let manifest: DataPolicyManifest = serde_json::from_str(json)?;
        self.load_data_policy_manifest(manifest);
        Ok(())
    }

    /// Load a data policy manifest.
    pub fn load_data_policy_manifest(&mut self, manifest: DataPolicyManifest) {
        let namespace = &manifest.data_namespace;

        // Collect known resource types so we can assign top-level aliases.
        let known_rts: Vec<String> = manifest
            .resource_type_aliases
            .iter()
            .map(|rta| rta.resource_type.clone())
            .collect();

        // 1. Process per-resource-type alias groups.
        for rta in &manifest.resource_type_aliases {
            let fq_type = alloc::format!("{}/{}", namespace, rta.resource_type);
            let entries = convert_data_manifest_aliases(&fq_type, &rta.aliases);
            self.ingest_alias_entries(&fq_type, &entries);
        }

        // 2. Process top-level aliases — determine resource type from name.
        //    Group them by resource type, then merge into existing entries.
        let mut grouped: BTreeMap<String, Vec<AliasEntry>> = BTreeMap::new();
        let ns_prefix = alloc::format!("{}/", namespace);

        for alias in &manifest.aliases {
            let suffix = if alias.name.len() > ns_prefix.len()
                && alias.name[..ns_prefix.len()].eq_ignore_ascii_case(&ns_prefix)
            {
                &alias.name[ns_prefix.len()..]
            } else {
                continue;
            };

            // Find the longest matching known resource type.
            let mut best_rt: Option<&str> = None;
            let mut best_len = 0;
            for rt in &known_rts {
                if suffix.len() > rt.len()
                    && suffix[..rt.len()].eq_ignore_ascii_case(rt)
                    && suffix.as_bytes().get(rt.len()) == Some(&b'/')
                    && rt.len() > best_len
                {
                    best_rt = Some(rt.as_str());
                    best_len = rt.len();
                }
            }

            let entry = data_alias_to_alias_entry(alias);

            if let Some(rt) = best_rt {
                let fq_type = alloc::format!("{}/{}", namespace, rt);
                grouped.entry(fq_type).or_default().push(entry);
            }
            // If no matching resource type, skip (shouldn't happen in practice).
        }

        // Merge grouped top-level aliases into existing resource type entries.
        for (fq_type, entries) in &grouped {
            self.ingest_alias_entries(fq_type, entries);
        }
    }

    /// Load a single provider's alias data.
    pub fn load_provider(&mut self, provider: ProviderAliases) {
        let namespace = &provider.namespace;
        for rt in provider.resource_types {
            let fq_type = alloc::format!("{}/{}", namespace, rt.resource_type);
            self.ingest_alias_entries(&fq_type, &rt.aliases);
        }
    }

    /// Ingest a batch of alias entries for a fully-qualified resource type.
    ///
    /// This is the shared core used by both [`load_provider`] and
    /// [`load_data_policy_manifest`].  It updates the global lookup maps
    /// and merges resolved entries into the per-resource-type map.
    fn ingest_alias_entries(&mut self, fq_type: &str, aliases: &[AliasEntry]) {
        let prefix = alloc::format!("{}/", fq_type);

        for alias in aliases {
            // Derive the short name by stripping the resource type prefix.
            let raw_short = if alias.name.len() > prefix.len()
                && alias.name[..prefix.len()].eq_ignore_ascii_case(&prefix)
            {
                alias.name[prefix.len()..].to_string()
            } else if let Some(rest) = alias
                .name
                .rfind('/')
                .and_then(|idx| alias.name.get(idx.saturating_add(1)..))
            {
                rest.to_string()
            } else {
                continue;
            };

            let default_path = alias.default_path.as_deref().unwrap_or("");
            // The normalizer flattens `properties` into the resource root, so
            // strip a leading `properties.` / `properties/` from the short name.
            let raw_short_normalized = normalize_short_name(&raw_short).to_string();

            let short = if is_root_field_collision(&raw_short_normalized, default_path) {
                collision_safe_key(&raw_short_normalized)
            } else {
                raw_short_normalized
            };
            let lc_name = alias.name.to_lowercase();
            self.alias_to_short.insert(lc_name.clone(), short);
            let is_modifiable = types::has_flag(
                alias
                    .default_metadata
                    .as_ref()
                    .and_then(|m| m.attributes.as_deref()),
                "Modifiable",
            );
            self.alias_modifiable.insert(lc_name, is_modifiable);
        }

        let resolved = resolve_resource_type(fq_type, aliases);
        let lc_type = fq_type.to_lowercase();

        // Merge into existing entry if one exists (for data manifests that
        // have both top-level and per-resource-type aliases for the same type).
        if let Some(existing) = self.types.get_mut(&lc_type) {
            for (key, entry) in resolved.entries {
                existing.entries.insert(key, entry);
            }
            // Replace sub-resource arrays: redetect from the merged entry set
            // so that overwritten aliases that no longer indicate sub-resource
            // wrapping cause stale classifications to be removed.
            existing.sub_resource_arrays = redetect_sub_resource_arrays(&existing.entries);
            // Recompute aggregates after merge.
            let (default_agg, versioned_agg) =
                precompute_aggregates(&existing.entries, &existing.sub_resource_arrays);
            existing.default_aggregates = default_agg;
            existing.versioned_aggregates = versioned_agg;
        } else {
            self.types.insert(lc_type, resolved);
        }
    }

    /// Look up resolved aliases for a resource type.
    ///
    /// The lookup is case-insensitive.
    pub fn get(&self, resource_type: &str) -> Option<&ResolvedAliases> {
        self.types.get(&resource_type.to_lowercase())
    }

    /// Number of registered resource types.
    pub fn len(&self) -> usize {
        self.types.len()
    }

    /// Whether the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }

    /// Resolve a fully-qualified alias name to its short name.
    ///
    /// The lookup is case-insensitive. Returns `None` if the alias is not
    /// found in the registry (meaning it's either already a short name or
    /// not a known alias).
    pub fn resolve_alias(&self, fq_name: &str) -> Option<&str> {
        self.alias_to_short
            .get(&fq_name.to_lowercase())
            .map(String::as_str)
    }

    /// Return a clone of the alias-to-short-name map for use by the compiler.
    ///
    /// The compiler stores this map internally so it can resolve fully-qualified
    /// alias names without holding a reference to the registry.
    pub fn alias_map(&self) -> BTreeMap<String, String> {
        self.alias_to_short.clone()
    }

    /// Return a clone of the alias-to-modifiable map for use by the compiler.
    ///
    /// Maps lowercase fully-qualified alias names to `true` when the alias
    /// has `defaultMetadata.attributes = "Modifiable"`.
    pub fn alias_modifiable_map(&self) -> BTreeMap<String, bool> {
        self.alias_modifiable.clone()
    }

    /// Normalize a raw ARM resource and wrap it in the input envelope.
    ///
    /// Convenience method that combines alias lookup, normalization, and
    /// envelope construction.  The resource type is extracted from the
    /// `type` field of `arm_resource` automatically.
    ///
    /// # Arguments
    ///
    /// * `arm_resource` — The raw ARM JSON for the resource.
    /// * `api_version` — Optional API version to select versioned alias paths.
    /// * `context` — Optional context object for the input envelope.
    /// * `parameters` — Optional parameters object for the input envelope.
    pub fn normalize_and_wrap(
        &self,
        arm_resource: &crate::Value,
        api_version: Option<&str>,
        context: Option<crate::Value>,
        parameters: Option<crate::Value>,
    ) -> crate::Value {
        let normalized = normalizer::normalize(arm_resource, Some(self), api_version);
        normalizer::build_input_envelope(normalized, context, parameters)
    }

    /// Denormalize a normalized resource back to ARM JSON structure.
    ///
    /// Convenience method that combines alias lookup and denormalization.
    /// The resource type is extracted from the `type` field of `normalized`
    /// automatically.
    ///
    /// # Arguments
    ///
    /// * `normalized` — The normalized JSON object (as produced by
    ///   [`normalizer::normalize`]).
    /// * `api_version` — Optional API version to select versioned alias paths.
    pub fn denormalize(
        &self,
        normalized: &crate::Value,
        api_version: Option<&str>,
    ) -> crate::Value {
        denormalizer::denormalize(normalized, Some(self), api_version)
    }
}

/// Resolve a resource type's alias entries into `ResolvedAliases`.
///
/// This:
/// 1. Strips the resource type prefix from alias names to produce short names.
/// 2. Extracts `defaultPath` and versioned paths.
/// 3. Detects sub-resource arrays from alias path patterns.
fn resolve_resource_type(fq_type: &str, aliases: &[types::AliasEntry]) -> ResolvedAliases {
    let prefix = alloc::format!("{}/", fq_type);
    let mut entries = BTreeMap::new();
    let mut sub_resource_arrays: BTreeSet<String> = BTreeSet::new();

    for alias in aliases {
        // Derive short name by stripping the resource type prefix.
        // For cross-type aliases (e.g., Microsoft.Compute/imagePublisher
        // under the virtualMachines resource type), the name does not
        // start with the resource type prefix.  In that case, take the
        // part after the last '/'.
        let short_name = if alias.name.len() > prefix.len()
            && alias.name[..prefix.len()].eq_ignore_ascii_case(&prefix)
        {
            &alias.name[prefix.len()..]
        } else if let Some(rest) = alias
            .name
            .rfind('/')
            .and_then(|idx| alias.name.get(idx.saturating_add(1)..))
        {
            rest
        } else {
            &alias.name
        };

        // The normalizer flattens `properties` into the resource root, so
        // strip a leading `properties.` / `properties/` from the short name.
        let short_name = normalize_short_name(short_name);

        let default_path = match &alias.default_path {
            Some(p) => p.clone(),
            None => continue, // Skip aliases without a default path (shouldn't happen in production)
        };

        // Detect sub-resource arrays from the alias pattern.
        // If short name contains `[*]` and default_path has
        // `properties.X[*].properties.Y`, then X is a sub-resource array.
        detect_sub_resource_array(short_name, &default_path, &mut sub_resource_arrays);

        let versioned_paths: Vec<(String, String)> = alias
            .paths
            .iter()
            .flat_map(|p| {
                p.api_versions
                    .iter()
                    .map(move |v| (v.clone(), p.path.clone()))
            })
            .collect();

        entries.insert(
            short_name.to_lowercase(),
            ResolvedEntry::new(
                short_name.to_string(),
                default_path,
                versioned_paths,
                alias.default_metadata.clone(),
            ),
        );
    }

    // Precompute aggregate fields from entries.
    let (default_aggregates, versioned_aggregates) =
        precompute_aggregates(&entries, &sub_resource_arrays);

    ResolvedAliases {
        resource_type: fq_type.to_string(),
        entries,
        sub_resource_arrays,
        default_aggregates,
        versioned_aggregates,
    }
}

/// Return type for [`precompute_aggregates`].
type AggregateFields = (VersionedAggregates, BTreeMap<String, VersionedAggregates>);

/// Precompute element remaps, reverse remaps, and array renames from resolved
/// entries for the default path AND every distinct api_version found in any
/// entry's `versioned_paths`.
///
/// This moves O(aliases) string splitting/lowercasing out of the per-call
/// normalize/denormalize hot path into a one-time cost at registry-load time.
fn precompute_aggregates(
    entries: &BTreeMap<String, ResolvedEntry>,
    sub_resource_arrays: &BTreeSet<String>,
) -> AggregateFields {
    // Collect all distinct api_versions that appear in any entry.
    let mut all_versions = alloc::collections::BTreeSet::new();
    for entry in entries.values() {
        for (ver, _) in &entry.versioned_paths {
            all_versions.insert(ver.to_lowercase());
        }
    }

    // Compute default aggregates (api_version = None).
    let default_agg = compute_aggregates_for_version(entries, sub_resource_arrays, None);

    // Compute per-version aggregates.
    let mut versioned_map = BTreeMap::new();
    for ver in &all_versions {
        let agg = compute_aggregates_for_version(entries, sub_resource_arrays, Some(ver.as_str()));
        // Only store if it differs from default (saves memory for versions
        // where no entry has a different path).
        if agg != default_agg {
            versioned_map.insert(ver.clone(), agg);
        }
    }

    (default_agg, versioned_map)
}

/// Compute aggregates for a specific api_version (or None for default path).
fn compute_aggregates_for_version(
    entries: &BTreeMap<String, ResolvedEntry>,
    sub_resource_arrays: &BTreeSet<String>,
    api_version: Option<&str>,
) -> VersionedAggregates {
    let mut element_remaps = Vec::new();
    let mut reverse_element_remaps = Vec::new();
    let mut renames_norm: Vec<(String, String)> = Vec::new();
    let mut renames_denorm: Vec<(String, String)> = Vec::new();

    // Use BTreeSet for O(log N) dedup instead of Vec::contains.
    let mut seen_norm = alloc::collections::BTreeSet::new();
    let mut seen_denorm = alloc::collections::BTreeSet::new();

    for entry in entries.values() {
        if !entry.is_wildcard {
            continue;
        }

        // Skip sub-resource array root entries for scalar processing.
        // The set is pre-lowercased, so use a direct O(log n) lookup.
        if sub_resource_arrays.contains(&entry.short_name.to_ascii_lowercase()) {
            continue;
        }

        // Select the ARM path for this version (or default).
        let selected_path = entry.select_path(api_version);
        let short_parts: Vec<&str> = entry.short_name.split("[*].").collect();
        let arm_raw_parts: Vec<&str> = selected_path.split("[*].").collect();

        if short_parts.len() >= 2 && arm_raw_parts.len() >= 2 {
            if let (Some(short_leaf), Some(arm_leaf_raw)) =
                (short_parts.last(), arm_raw_parts.last())
            {
                let arm_leaf = arm_leaf_raw
                    .strip_prefix("properties.")
                    .unwrap_or(arm_leaf_raw);

                if !short_leaf.eq_ignore_ascii_case(arm_leaf) {
                    let array_chain: Vec<Vec<String>> = short_parts
                        .split_last()
                        .map(|(_, init)| init)
                        .unwrap_or_default()
                        .iter()
                        .map(|part| part.split('.').map(|s| s.to_ascii_lowercase()).collect())
                        .collect();

                    let source_lc = arm_leaf.to_ascii_lowercase();
                    let target_lc = short_leaf.to_ascii_lowercase();

                    element_remaps.push(PrecomputedRemap {
                        array_chain: array_chain.clone(),
                        source_field: source_lc.clone(),
                        target_field: target_lc.clone(),
                    });

                    reverse_element_remaps.push(PrecomputedReverseRemap {
                        array_chain: array_chain.clone(),
                        source_field: target_lc.clone(),
                        target_field: source_lc,
                        cleanup_field: target_lc,
                    });
                }
            }
        }

        // Compute array base rename.
        if let (Some(short_base), Some(arm_base)) = (
            entry.short_name.split("[*]").next(),
            selected_path.split("[*]").next(),
        ) {
            let arm_base_stripped = arm_base.strip_prefix("properties.").unwrap_or(arm_base);
            if !short_base.eq_ignore_ascii_case(arm_base_stripped) {
                // Normalize direction: (arm_base_lc, short_base_lc)
                let norm_pair = (
                    arm_base_stripped.to_ascii_lowercase(),
                    short_base.to_ascii_lowercase(),
                );
                if seen_norm.insert(norm_pair.clone()) {
                    renames_norm.push(norm_pair);
                }

                // Denormalize direction: (short_base_lc, arm_base)
                let denorm_pair = (
                    short_base.to_ascii_lowercase(),
                    arm_base_stripped.to_string(),
                );
                if seen_denorm.insert(denorm_pair.clone()) {
                    renames_denorm.push(denorm_pair);
                }
            }
        }
    }

    VersionedAggregates {
        element_remaps,
        reverse_element_remaps,
        array_renames_normalize: renames_norm,
        array_renames_denormalize: renames_denorm,
    }
}

/// Detect sub-resource arrays from alias naming patterns.
///
/// If the alias short name has `X[*].Y` and the default path has
/// `properties.X[*].properties.Y`, then `X` is a sub-resource array whose
/// elements need `properties` flattening during normalization.
///
/// For nested sub-resource arrays like `X[*].Y[*].Z` mapping to
/// `properties.X[*].properties.Y[*].properties.Z`, both `X` and `X.Y`
/// (dotted path within the normalized structure) are sub-resource arrays.
fn detect_sub_resource_array(
    short_name: &str,
    default_path: &str,
    sub_resource_arrays: &mut BTreeSet<String>,
) {
    // Split short name and default path by `[*].`
    let short_parts: Vec<&str> = short_name.split("[*].").collect();
    let path_parts: Vec<&str> = default_path.split("[*].").collect();

    if short_parts.len() < 2 || path_parts.len() < 2 {
        return; // No wildcard — not a sub-resource array alias
    }

    // For each `[*]` level, check if the pattern matches sub-resource wrapping.
    // short_name: securityRules[*].protocol
    // default_path: properties.securityRules[*].properties.protocol
    //
    // The first segment of the default_path after splitting should start with
    // "properties." and the part after the first [*]. should start with
    // "properties." to indicate sub-resource wrapping.

    // Build up the chain of sub-resource array names.
    let mut accumulated_name = String::new();

    for (i, array_field) in short_parts
        .iter()
        .enumerate()
        .take(short_parts.len().saturating_sub(1))
    {
        // For the first level, check that default_path starts with `properties.X[*].properties.`
        // For nested levels, the segment after [*]. should also start with `properties.`
        if let Some(next_path_segment) = path_parts.get(i.saturating_add(1)) {
            if next_path_segment.starts_with("properties.")
                || next_path_segment.starts_with("properties/")
            {
                // This is a sub-resource array!
                let name = if accumulated_name.is_empty() {
                    array_field.to_string()
                } else {
                    alloc::format!("{}.{}", accumulated_name, array_field)
                };

                sub_resource_arrays.insert(name.to_ascii_lowercase());
                accumulated_name = name;
            }
        }
    }
}

/// Redetect sub-resource arrays from the merged entry set.
///
/// This is used after merging alias entries to ensure that stale sub-resource
/// classifications are removed when overwritten aliases no longer indicate
/// sub-resource wrapping.
fn redetect_sub_resource_arrays(entries: &BTreeMap<String, ResolvedEntry>) -> BTreeSet<String> {
    let mut sub_resource_arrays = BTreeSet::new();
    for entry in entries.values() {
        detect_sub_resource_array(
            &entry.short_name,
            &entry.default_path,
            &mut sub_resource_arrays,
        );
    }
    sub_resource_arrays
}

/// Convert a data manifest alias to a standard [`AliasEntry`].
///
/// Data manifest aliases use `paths[0].path` as the effective default path
/// (the `defaultPath` field is absent).  Both `apiVersions` and
/// `schemaVersions` are treated as version sets for versioned path lookup.
fn data_alias_to_alias_entry(dma: &types::DataManifestAlias) -> AliasEntry {
    let default_path = dma.paths.first().map(|p| p.path.clone());

    let paths: Vec<AliasPath> = dma
        .paths
        .iter()
        .map(|p| {
            // Merge apiVersions and schemaVersions into a single version list.
            let mut versions = p.api_versions.clone();
            versions.extend(p.schema_versions.iter().cloned());
            AliasPath {
                path: p.path.clone(),
                api_versions: versions,
                metadata: None,
                ..Default::default()
            }
        })
        .collect();

    AliasEntry {
        name: dma.name.clone(),
        default_path,
        default_metadata: None,
        paths,
        ..Default::default()
    }
}

/// Convert a slice of data manifest aliases to standard [`AliasEntry`] objects.
fn convert_data_manifest_aliases(
    _fq_type: &str,
    aliases: &[types::DataManifestAlias],
) -> Vec<AliasEntry> {
    aliases.iter().map(data_alias_to_alias_entry).collect()
}

/// Normalize a short name derived from an alias FQ name.
///
/// The normalizer always flattens `properties` into the resource root, so a
/// short name like `properties.domainNames[*]` must be reduced to
/// `domainNames[*]` to match the normalized resource structure.
///
/// This is primarily needed for data-plane aliases where the FQ name includes
/// `properties.` in the property part (e.g.,
/// `Microsoft.DataFactory.Data/factories/outboundTraffic/properties.domainNames[*]`).
/// Control-plane alias names never include `properties.` in the short portion.
fn normalize_short_name(short: &str) -> &str {
    short
        .strip_prefix("properties.")
        .or_else(|| short.strip_prefix("properties/"))
        .unwrap_or(short)
}

#[cfg(test)]
#[allow(clippy::indexing_slicing, clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use alloc::string::ToString as _;
    use alloc::vec;

    use super::*;

    #[test]
    fn test_detect_sub_resource_nsg() {
        let mut subs = BTreeSet::new();
        detect_sub_resource_array(
            "securityRules[*].protocol",
            "properties.securityRules[*].properties.protocol",
            &mut subs,
        );
        assert_eq!(subs, BTreeSet::from(["securityrules".to_string()]));
    }

    #[test]
    fn test_detect_no_sub_resource() {
        let mut subs = BTreeSet::new();
        // ipRules[*].value -> properties.networkAcls.ipRules[*].value
        // No `properties.` after the `[*].` means NOT a sub-resource
        detect_sub_resource_array(
            "networkAcls.ipRules[*].value",
            "properties.networkAcls.ipRules[*].value",
            &mut subs,
        );
        assert!(subs.is_empty());
    }

    #[test]
    fn test_detect_nested_sub_resource() {
        let mut subs = BTreeSet::new();
        detect_sub_resource_array(
            "subnets[*].ipConfigurations[*].name",
            "properties.subnets[*].properties.ipConfigurations[*].properties.name",
            &mut subs,
        );
        let expected: BTreeSet<String> = BTreeSet::from([
            "subnets".to_string(),
            "subnets.ipconfigurations".to_string(),
        ]);
        assert_eq!(subs, expected);
    }

    #[test]
    fn test_resolve_resource_type_basic() {
        let aliases = vec![
            types::AliasEntry {
                name: "Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly".to_string(),
                default_path: Some("properties.supportsHttpsTrafficOnly".to_string()),
                default_metadata: None,
                paths: vec![],
                ..Default::default()
            },
            types::AliasEntry {
                name: "Microsoft.Storage/storageAccounts/sku.name".to_string(),
                default_path: Some("sku.name".to_string()),
                default_metadata: None,
                paths: vec![],
                ..Default::default()
            },
        ];

        let resolved = resolve_resource_type("Microsoft.Storage/storageAccounts", &aliases);
        assert_eq!(resolved.entries.len(), 2);

        let https_entry = resolved.entries.get("supportshttpstrafficonly").unwrap();
        assert_eq!(
            https_entry.default_path,
            "properties.supportsHttpsTrafficOnly"
        );

        let sku_entry = resolved.entries.get("sku.name").unwrap();
        assert_eq!(sku_entry.default_path, "sku.name");

        assert!(resolved.sub_resource_arrays.is_empty());
    }

    #[test]
    fn test_resolve_nsg_has_sub_resource_arrays() {
        let aliases = vec![
            types::AliasEntry {
                name: "Microsoft.Network/networkSecurityGroups/securityRules[*].protocol"
                    .to_string(),
                default_path: Some("properties.securityRules[*].properties.protocol".to_string()),
                default_metadata: None,
                paths: vec![],
                ..Default::default()
            },
            types::AliasEntry {
                name: "Microsoft.Network/networkSecurityGroups/securityRules[*].access".to_string(),
                default_path: Some("properties.securityRules[*].properties.access".to_string()),
                default_metadata: None,
                paths: vec![],
                ..Default::default()
            },
        ];

        let resolved = resolve_resource_type("Microsoft.Network/networkSecurityGroups", &aliases);
        assert_eq!(
            resolved.sub_resource_arrays,
            BTreeSet::from(["securityrules".to_string()])
        );
    }

    #[test]
    fn test_load_from_json() {
        let json = r#"[
            {
                "namespace": "Microsoft.Storage",
                "resourceTypes": [
                    {
                        "resourceType": "storageAccounts",
                        "aliases": [
                            {
                                "name": "Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly",
                                "defaultPath": "properties.supportsHttpsTrafficOnly",
                                "paths": []
                            }
                        ]
                    }
                ]
            }
        ]"#;

        let mut registry = AliasRegistry::new();
        registry.load_from_json(json).unwrap();
        assert_eq!(registry.len(), 1);

        let resolved = registry.get("Microsoft.Storage/storageAccounts").unwrap();
        assert_eq!(resolved.entries.len(), 1);
        assert!(resolved.entries.contains_key("supportshttpstrafficonly"));
    }

    #[test]
    fn test_registry_case_insensitive_get() {
        let json = r#"[
            {
                "namespace": "Microsoft.Storage",
                "resourceTypes": [
                    {
                        "resourceType": "storageAccounts",
                        "aliases": [
                            {
                                "name": "Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly",
                                "defaultPath": "properties.supportsHttpsTrafficOnly",
                                "paths": []
                            }
                        ]
                    }
                ]
            }
        ]"#;

        let mut registry = AliasRegistry::new();
        registry.load_from_json(json).unwrap();

        // Mixed-case lookup should work
        assert!(registry.get("microsoft.storage/STORAGEACCOUNTS").is_some());
        assert!(registry.get("MICROSOFT.STORAGE/storageAccounts").is_some());
    }

    #[test]
    fn test_resolve_with_versioned_paths() {
        let aliases = vec![types::AliasEntry {
            name: "Microsoft.Web/sites/siteConfig.numberOfWorkers".to_string(),
            default_path: Some("properties.siteConfig.numberOfWorkers".to_string()),
            default_metadata: None,
            paths: vec![
                types::AliasPath {
                    path: "properties.siteConfig.properties.numberOfWorkers".to_string(),
                    api_versions: vec!["2014-04-01".to_string(), "2014-06-01".to_string()],
                    metadata: None,
                    ..Default::default()
                },
                types::AliasPath {
                    path: "properties.siteConfig.numberOfWorkers".to_string(),
                    api_versions: vec!["2021-01-01".to_string()],
                    metadata: None,
                    ..Default::default()
                },
            ],
            ..Default::default()
        }];

        let resolved = resolve_resource_type("Microsoft.Web/sites", &aliases);
        let entry = resolved.entries.get("siteconfig.numberofworkers").unwrap();

        assert_eq!(entry.default_path, "properties.siteConfig.numberOfWorkers");
        // Has versioned paths
        assert_eq!(entry.versioned_paths.len(), 3); // 2 + 1
        assert_eq!(
            entry.select_path(Some("2014-04-01")),
            "properties.siteConfig.properties.numberOfWorkers"
        );
        assert_eq!(
            entry.select_path(Some("2021-01-01")),
            "properties.siteConfig.numberOfWorkers"
        );
        // Unknown version falls back to default
        assert_eq!(
            entry.select_path(Some("9999-01-01")),
            "properties.siteConfig.numberOfWorkers"
        );
    }

    #[test]
    fn test_resolve_alias_without_default_path_skipped() {
        let aliases = vec![
            types::AliasEntry {
                name: "Microsoft.Storage/storageAccounts/good".to_string(),
                default_path: Some("properties.good".to_string()),
                default_metadata: None,
                paths: vec![],
                ..Default::default()
            },
            types::AliasEntry {
                name: "Microsoft.Storage/storageAccounts/bad".to_string(),
                default_path: None,
                default_metadata: None,
                paths: vec![],
                ..Default::default()
            },
        ];

        let resolved = resolve_resource_type("Microsoft.Storage/storageAccounts", &aliases);
        assert_eq!(resolved.entries.len(), 1);
        assert!(resolved.entries.contains_key("good"));
        assert!(!resolved.entries.contains_key("bad"));
    }

    #[test]
    fn test_empty_registry() {
        let registry = AliasRegistry::new();
        assert!(registry.is_empty());
        assert_eq!(registry.len(), 0);
        assert!(registry.get("Microsoft.Storage/storageAccounts").is_none());
    }

    #[test]
    fn test_resolve_empty_aliases() {
        let resolved = resolve_resource_type("Microsoft.Test/empty", &[]);
        assert!(resolved.entries.is_empty());
        assert!(resolved.sub_resource_arrays.is_empty());
    }

    #[test]
    fn test_sub_resource_dedup() {
        // Multiple aliases for the same sub-resource array should deduplicate
        let aliases = vec![
            types::AliasEntry {
                name: "T/R/rules[*].a".to_string(),
                default_path: Some("properties.rules[*].properties.a".to_string()),
                default_metadata: None,
                paths: vec![],
                ..Default::default()
            },
            types::AliasEntry {
                name: "T/R/rules[*].b".to_string(),
                default_path: Some("properties.rules[*].properties.b".to_string()),
                default_metadata: None,
                paths: vec![],
                ..Default::default()
            },
            types::AliasEntry {
                name: "T/R/rules[*].c".to_string(),
                default_path: Some("properties.rules[*].properties.c".to_string()),
                default_metadata: None,
                paths: vec![],
                ..Default::default()
            },
        ];

        let resolved = resolve_resource_type("T/R", &aliases);
        // "rules" should appear only once despite 3 aliases detecting it
        assert_eq!(
            resolved.sub_resource_arrays,
            BTreeSet::from(["rules".to_string()])
        );
    }

    #[test]
    fn test_normalize_and_wrap_full_pipeline() {
        let json = r#"[
            {
                "namespace": "Microsoft.Network",
                "resourceTypes": [
                    {
                        "resourceType": "networkSecurityGroups",
                        "aliases": [
                            {
                                "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].protocol",
                                "defaultPath": "properties.securityRules[*].properties.protocol",
                                "paths": []
                            }
                        ]
                    }
                ]
            }
        ]"#;

        let mut registry = AliasRegistry::new();
        registry.load_from_json(json).unwrap();

        let arm_resource = crate::Value::from_json_str(
            r#"{
            "name": "myNsg",
            "type": "Microsoft.Network/networkSecurityGroups",
            "properties": {
                "securityRules": [
                    {
                        "name": "rule1",
                        "properties": {
                            "protocol": "Tcp"
                        }
                    }
                ]
            }
        }"#,
        )
        .unwrap();

        let context = crate::Value::from_json_str(r#"{"resourceGroup": {"name": "rg1"}}"#).unwrap();
        let parameters = crate::Value::from_json_str(r#"{"env": "prod"}"#).unwrap();

        let envelope =
            registry.normalize_and_wrap(&arm_resource, None, Some(context), Some(parameters));

        // Resource is normalized (all keys lowercased)
        assert_eq!(envelope["resource"]["name"], crate::Value::from("myNsg"));
        let rules = envelope["resource"]["securityrules"].as_array().unwrap();
        assert_eq!(rules[0]["protocol"], crate::Value::from("Tcp"));
        assert_eq!(rules[0]["properties"], crate::Value::Undefined);
        // Context and parameters are passed through
        assert_eq!(
            envelope["context"]["resourceGroup"]["name"],
            crate::Value::from("rg1")
        );
        assert_eq!(envelope["parameters"]["env"], crate::Value::from("prod"));
    }

    #[test]
    fn test_load_test_aliases_json() {
        // Integration test: load the actual test_aliases.json file
        let json = std::fs::read_to_string("tests/azure_policy/aliases/test_aliases.json")
            .expect("test_aliases.json should exist");

        let mut registry = AliasRegistry::new();
        registry
            .load_from_json(&json)
            .expect("test_aliases.json should parse");

        // Expect 44 resource types
        assert_eq!(registry.len(), 44);

        // Storage
        let storage = registry
            .get("Microsoft.Storage/storageAccounts")
            .expect("Storage aliases should exist");
        assert!(!storage.entries.is_empty());
        assert!(storage.sub_resource_arrays.is_empty());

        // NSG — should have sub-resource arrays
        let nsg = registry
            .get("Microsoft.Network/networkSecurityGroups")
            .expect("NSG aliases should exist");
        assert!(!nsg.entries.is_empty());
        assert!(
            nsg.sub_resource_arrays.contains("securityrules"),
            "NSG should detect securityRules as sub-resource array"
        );

        // KeyVault
        assert!(registry.get("Microsoft.KeyVault/vaults").is_some());

        // SQL
        assert!(registry.get("Microsoft.Sql/servers").is_some());

        // VM
        assert!(registry.get("Microsoft.Compute/virtualMachines").is_some());

        // Web
        assert!(registry.get("Microsoft.Web/sites").is_some());

        // AKS
        assert!(registry
            .get("Microsoft.ContainerService/managedClusters")
            .is_some());

        // Disks
        assert!(registry.get("Microsoft.Compute/disks").is_some());

        // NIC — should have sub-resource arrays
        let nic = registry
            .get("Microsoft.Network/networkInterfaces")
            .expect("NIC aliases should exist");
        assert!(
            nic.sub_resource_arrays.contains("ipconfigurations"),
            "NIC should detect ipConfigurations as sub-resource array"
        );
    }

    #[test]
    fn test_resolve_alias_basic() {
        let json = r#"[
            {
                "namespace": "Microsoft.Storage",
                "resourceTypes": [
                    {
                        "resourceType": "storageAccounts",
                        "aliases": [
                            {
                                "name": "Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly",
                                "defaultPath": "properties.supportsHttpsTrafficOnly",
                                "paths": []
                            },
                            {
                                "name": "Microsoft.Storage/storageAccounts/sku.name",
                                "defaultPath": "sku.name",
                                "paths": []
                            }
                        ]
                    }
                ]
            }
        ]"#;

        let mut registry = AliasRegistry::new();
        registry.load_from_json(json).unwrap();

        assert_eq!(
            registry.resolve_alias("Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly"),
            Some("supportsHttpsTrafficOnly")
        );
        assert_eq!(
            registry.resolve_alias("Microsoft.Storage/storageAccounts/sku.name"),
            Some("sku.name")
        );
        // Case-insensitive
        assert_eq!(
            registry.resolve_alias("microsoft.storage/STORAGEACCOUNTS/supportsHttpsTrafficOnly"),
            Some("supportsHttpsTrafficOnly")
        );
        // Unknown alias
        assert_eq!(
            registry.resolve_alias("Microsoft.Storage/storageAccounts/unknown"),
            None
        );
        // Already a short name
        assert_eq!(registry.resolve_alias("supportsHttpsTrafficOnly"), None);
    }

    #[test]
    fn test_alias_map_for_compiler() {
        let json = r#"[
            {
                "namespace": "Microsoft.Network",
                "resourceTypes": [
                    {
                        "resourceType": "networkSecurityGroups",
                        "aliases": [
                            {
                                "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].protocol",
                                "defaultPath": "properties.securityRules[*].properties.protocol",
                                "paths": []
                            }
                        ]
                    }
                ]
            }
        ]"#;

        let mut registry = AliasRegistry::new();
        registry.load_from_json(json).unwrap();

        let map = registry.alias_map();
        // alias_map returns the short name derived by stripping the FQ type
        // prefix from the alias name:
        //   `Microsoft.Network/networkSecurityGroups/securityRules[*].protocol`
        //   → `securityRules[*].protocol`
        assert_eq!(
            map.get("microsoft.network/networksecuritygroups/securityrules[*].protocol"),
            Some(&"securityRules[*].protocol".to_string())
        );
    }

    #[test]
    fn test_alias_modifiable_comma_separated_flags() {
        // Regression: alias_modifiable_map should detect "Modifiable" even when
        // the attributes field contains comma-separated flags like
        // "Modifiable, SupportsCreate".
        let json = r#"[
            {
                "namespace": "Microsoft.Test",
                "resourceTypes": [
                    {
                        "resourceType": "widgets",
                        "aliases": [
                            {
                                "name": "Microsoft.Test/widgets/singleFlag",
                                "defaultPath": "properties.singleFlag",
                                "paths": [],
                                "defaultMetadata": {
                                    "attributes": "Modifiable"
                                }
                            },
                            {
                                "name": "Microsoft.Test/widgets/multiFlag",
                                "defaultPath": "properties.multiFlag",
                                "paths": [],
                                "defaultMetadata": {
                                    "attributes": "Modifiable, SupportsCreate"
                                }
                            },
                            {
                                "name": "Microsoft.Test/widgets/notModifiable",
                                "defaultPath": "properties.notModifiable",
                                "paths": [],
                                "defaultMetadata": {
                                    "attributes": "None"
                                }
                            },
                            {
                                "name": "Microsoft.Test/widgets/noMetadata",
                                "defaultPath": "properties.noMetadata",
                                "paths": []
                            }
                        ]
                    }
                ]
            }
        ]"#;

        let mut registry = AliasRegistry::new();
        registry.load_from_json(json).unwrap();

        let modifiable = registry.alias_modifiable_map();

        // Single "Modifiable" flag → true
        assert_eq!(
            modifiable.get("microsoft.test/widgets/singleflag"),
            Some(&true)
        );
        // Comma-separated flags containing "Modifiable" → true
        assert_eq!(
            modifiable.get("microsoft.test/widgets/multiflag"),
            Some(&true)
        );
        // "None" → false
        assert_eq!(
            modifiable.get("microsoft.test/widgets/notmodifiable"),
            Some(&false)
        );
        // No metadata → false
        assert_eq!(
            modifiable.get("microsoft.test/widgets/nometadata"),
            Some(&false)
        );
    }

    #[test]
    fn test_overwrite_removes_stale_sub_resource_arrays() {
        // Regression: a second load that overwrites aliases for the same
        // resource type must remove stale sub-resource array classifications
        // when the new alias paths no longer indicate sub-resource wrapping.

        // First load: rules[*] aliases with `properties.` wrapping → sub-resource.
        let json1 = r#"[
            {
                "namespace": "Microsoft.Test",
                "resourceTypes": [
                    {
                        "resourceType": "firewalls",
                        "aliases": [
                            {
                                "name": "Microsoft.Test/firewalls/rules[*].protocol",
                                "defaultPath": "properties.rules[*].properties.protocol",
                                "paths": []
                            },
                            {
                                "name": "Microsoft.Test/firewalls/rules[*].port",
                                "defaultPath": "properties.rules[*].properties.port",
                                "paths": []
                            }
                        ]
                    }
                ]
            }
        ]"#;

        let mut registry = AliasRegistry::new();
        registry.load_from_json(json1).unwrap();

        let fw = registry.get("Microsoft.Test/firewalls").unwrap();
        assert!(
            fw.sub_resource_arrays.contains("rules"),
            "first load should detect 'rules' as a sub-resource array"
        );

        // Second load: same resource type, but rules[*] no longer has inner
        // `properties.` wrapping → NOT a sub-resource.
        let json2 = r#"[
            {
                "namespace": "Microsoft.Test",
                "resourceTypes": [
                    {
                        "resourceType": "firewalls",
                        "aliases": [
                            {
                                "name": "Microsoft.Test/firewalls/rules[*].protocol",
                                "defaultPath": "properties.rules[*].protocol",
                                "paths": []
                            },
                            {
                                "name": "Microsoft.Test/firewalls/rules[*].port",
                                "defaultPath": "properties.rules[*].port",
                                "paths": []
                            }
                        ]
                    }
                ]
            }
        ]"#;

        registry.load_from_json(json2).unwrap();

        let fw2 = registry.get("Microsoft.Test/firewalls").unwrap();
        assert!(
            !fw2.sub_resource_arrays.contains("rules"),
            "after overwrite, 'rules' should no longer be a sub-resource array"
        );
    }
}
