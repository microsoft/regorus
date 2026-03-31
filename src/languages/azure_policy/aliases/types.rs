// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Data types for Azure Policy alias definitions.
//!
//! These types deserialize production alias catalog data from multiple sources:
//!   1. ARM API response: `GET /providers?$expand=resourceTypes/aliases`
//!   2. Static `ResourceTypesAndAliases.json` (used by PolicyTester)
//!   3. `az provider list --expand resourceTypes/aliases` CLI output
//!      (where `defaultPath` may be serialized as `{ path, apiVersions }`)
//!
//! All data is captured for completeness; fields not yet used by the compiler
//! are retained so the types stay in sync with the production schema.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use serde::{Deserialize, Deserializer};

use super::obj_map::{collision_safe_key, is_root_field_collision};

// ─── Top-level response wrappers ────────────────────────────────────────────

/// ARM API response envelope: `{ "value": [...] }`
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct ArmProvidersResponse {
    pub value: Vec<ProviderAliases>,
    /// Pagination link (ARM may paginate large responses).
    #[serde(rename = "nextLink", default)]
    pub next_link: Option<String>,
}

// ─── Provider / resource type ───────────────────────────────────────────────

/// A resource provider's alias definitions.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct ProviderAliases {
    /// The provider namespace (e.g., `"Microsoft.Storage"`).
    pub namespace: String,

    /// Resource types with their alias entries.
    #[serde(default, rename = "resourceTypes")]
    pub resource_types: Vec<ResourceTypeAliases>,
}

/// Aliases for a single resource type within a provider.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct ResourceTypeAliases {
    /// The resource type name (e.g., `"storageAccounts"`).
    pub resource_type: String,

    /// All alias entries for this resource type.
    #[serde(default)]
    pub aliases: Vec<AliasEntry>,

    /// Resource capabilities as a comma-separated string
    /// (e.g., `"SupportsTags, SupportsLocation"`).
    #[serde(default)]
    pub capabilities: Option<String>,

    /// Default API version for the resource type.
    #[serde(default)]
    pub default_api_version: Option<String>,
}

// ─── Alias ──────────────────────────────────────────────────────────────────

/// A single alias entry within a resource type.
#[derive(Debug, Clone, Default, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct AliasEntry {
    /// Fully qualified alias name
    /// (e.g., `"Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly"`).
    pub name: String,

    /// The default ARM JSON path used when no versioned path matches.
    ///
    /// In most formats this is a plain string.  The `az CLI` format serializes
    /// it as `{ "path": "...", "apiVersions": [...] }`.  The custom
    /// deserializer accepts both, extracting just the path string.
    #[serde(default, deserialize_with = "deserialize_default_path")]
    pub default_path: Option<String>,

    /// Optional metadata for the default path (type, modifiability).
    #[serde(default)]
    pub default_metadata: Option<AliasPathMetadata>,

    /// Extraction pattern for the default path (present in ARM responses for
    /// some aliases; absent from the static file).
    #[serde(default)]
    pub default_pattern: Option<AliasPattern>,

    /// Alias-level type as a comma-separated string of flags:
    /// `"PlainText"`, `"Mask"`, `"Deprecated"`, `"Preview"`, or combinations
    /// like `"Mask, Deprecated"`.  `None` when absent.
    #[serde(default, rename = "type")]
    pub alias_type: Option<String>,

    /// Versioned path entries.  Empty for the vast majority of aliases that
    /// have only a `defaultPath`.
    #[serde(default)]
    pub paths: Vec<AliasPath>,
}

// ─── Alias path ─────────────────────────────────────────────────────────────

/// A versioned path mapping for an alias.
///
/// When an alias maps to different ARM JSON paths across API versions, each
/// distinct path is recorded as an `AliasPath` entry.
#[derive(Debug, Clone, Default, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct AliasPath {
    /// The ARM JSON path (e.g., `"properties.encryption.services.blob.enabled"`).
    pub path: String,

    /// API versions for which this path is valid.  Empty means all versions.
    #[serde(default)]
    pub api_versions: Vec<String>,

    /// Optional per-version metadata.
    #[serde(default)]
    pub metadata: Option<AliasPathMetadata>,

    /// Extraction pattern for this specific path.
    #[serde(default)]
    pub pattern: Option<AliasPattern>,
}

// ─── Alias path metadata ───────────────────────────────────────────────────

/// Metadata associated with an alias path (default or versioned).
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct AliasPathMetadata {
    /// The data type of the alias value as a string token
    /// (e.g., `"String"`, `"Integer"`, `"Boolean"`, `"Array"`, `"Object"`).
    #[serde(rename = "type")]
    pub kind: Option<String>,

    /// Attribute flags as a comma-separated string
    /// (e.g., `"Modifiable"`, `"Modifiable, SupportsCreate, SupportsRead"`).
    pub attributes: Option<String>,
}

// ─── Alias pattern ──────────────────────────────────────────────────────────

/// Extraction pattern for an alias path (URI template or regex).
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct AliasPattern {
    /// The pattern phrase (URI template or regex string).
    pub phrase: String,

    /// The variable to extract from the pattern.
    #[serde(default)]
    pub variable: Option<String>,

    /// Pattern type (e.g., `"Extract"`).
    #[serde(default, rename = "type")]
    pub pattern_type: Option<String>,
}

// ─── Custom deserializer: defaultPath (string or object) ────────────────────

/// Accepts either a plain string `"properties.foo"` or an az CLI object
/// `{ "path": "properties.foo", "apiVersions": [...] }`, extracting just the
/// path string.  Handles `null` gracefully.
fn deserialize_default_path<'de, D>(deserializer: D) -> Result<Option<String>, D::Error>
where
    D: Deserializer<'de>,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum RawDefaultPath {
        Str(String),
        Obj {
            path: String,
            #[serde(default, rename = "apiVersions")]
            _api_versions: Vec<String>,
        },
        Null,
    }

    match Option::<RawDefaultPath>::deserialize(deserializer)? {
        None | Some(RawDefaultPath::Null) => Ok(None),
        Some(RawDefaultPath::Str(s)) => Ok(Some(s)),
        Some(RawDefaultPath::Obj { path, .. }) => Ok(Some(path)),
    }
}

// ─── Data Policy Manifest types (data-plane aliases) ────────────────────────

/// A single alias entry in a data policy manifest.
///
/// Unlike control-plane [`AliasEntry`], data-plane aliases have no
/// `defaultPath` — the path is always taken from `paths[0].path`.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct DataManifestAlias {
    /// Fully qualified alias name
    /// (e.g., `"Microsoft.KeyVault.Data/vaults/certificates/attributes.expiresOn"`).
    pub name: String,

    /// Versioned path entries.  `paths[0].path` serves as the default path.
    #[serde(default)]
    pub paths: Vec<DataManifestAliasPath>,
}

/// A path entry in a data policy manifest alias.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct DataManifestAliasPath {
    /// The ARM JSON path (e.g., `"attributes.expiresOn"`).
    pub path: String,

    /// API versions for which this path is valid.
    #[serde(default)]
    pub api_versions: Vec<String>,

    /// Schema versions for which this path is valid (used by some data-plane
    /// providers instead of `apiVersions`).
    #[serde(default)]
    pub schema_versions: Vec<String>,
}

/// Per-resource-type alias group in a data policy manifest.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct DataManifestResourceTypeAliases {
    /// Resource type suffix (e.g., `"vaults/certificates"`).
    pub resource_type: String,

    /// Aliases for this resource type.
    #[serde(default)]
    pub aliases: Vec<DataManifestAlias>,
}

/// A data policy manifest describing data-plane aliases for a namespace.
///
/// This format is used by `dataPolicyManifests/` files, as opposed to the
/// control-plane `ProviderAliases` format used by `Get-AzPolicyAlias`.
#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct DataPolicyManifest {
    /// The data namespace (e.g., `"Microsoft.KeyVault.Data"`).
    pub data_namespace: String,

    /// Top-level aliases not scoped to a specific resource type.
    #[serde(default)]
    pub aliases: Vec<DataManifestAlias>,

    /// Per-resource-type alias groups.
    #[serde(default)]
    pub resource_type_aliases: Vec<DataManifestResourceTypeAliases>,
}

// ─── Convenience loading functions ──────────────────────────────────────────

/// Load from the static `ResourceTypesAndAliases.json` file (bare array).
pub fn load_from_static_file(json: &str) -> Result<Vec<ProviderAliases>, serde_json::Error> {
    serde_json::from_str(json)
}

/// Load from an ARM API `GET /providers` response (`{ "value": [...] }`).
pub fn load_from_arm_response(json: &str) -> Result<Vec<ProviderAliases>, serde_json::Error> {
    let resp: ArmProvidersResponse = serde_json::from_str(json)?;
    Ok(resp.value)
}

/// Load from either format: tries ARM envelope first, then bare array.
pub fn load_auto(json: &str) -> Result<Vec<ProviderAliases>, serde_json::Error> {
    let trimmed = json.trim_start();
    if trimmed.starts_with('[') {
        load_from_static_file(json)
    } else {
        load_from_arm_response(json)
    }
}

// ─── Utility methods ────────────────────────────────────────────────────────

impl AliasEntry {
    /// Returns `true` if this alias is marked as deprecated (case-insensitive).
    pub fn is_deprecated(&self) -> bool {
        has_flag(self.alias_type.as_deref(), "Deprecated")
    }

    /// Returns `true` if this alias is marked as preview.
    pub fn is_preview(&self) -> bool {
        has_flag(self.alias_type.as_deref(), "Preview")
    }

    /// Returns `true` if this alias's value should be masked (secret).
    pub fn is_secret(&self) -> bool {
        has_flag(self.alias_type.as_deref(), "Mask")
    }

    /// Returns the effective path string (defaultPath or first versioned path).
    pub fn effective_path(&self) -> Option<&str> {
        self.default_path
            .as_deref()
            .or_else(|| self.paths.first().map(|p| p.path.as_str()))
    }
}

impl AliasPathMetadata {
    /// Returns `true` if this path supports modification (Modifiable flag).
    pub fn is_modifiable(&self) -> bool {
        has_flag(self.attributes.as_deref(), "Modifiable")
    }
}

/// Check whether a comma-separated flags string contains a specific flag
/// (case-insensitive).
pub(crate) fn has_flag(flags: Option<&str>, flag: &str) -> bool {
    flags.is_some_and(|s| {
        s.split(',')
            .any(|part| part.trim().eq_ignore_ascii_case(flag))
    })
}

/// Parsed alias data for a single resource type, keyed by short name.
///
/// The short name is derived by stripping the resource type prefix from the
/// fully qualified alias name:
/// `Microsoft.Storage/storageAccounts/sku.name` → `sku.name`
#[derive(Debug, Clone)]
pub struct ResolvedAliases {
    /// Fully qualified resource type (e.g., `"Microsoft.Storage/storageAccounts"`).
    pub resource_type: String,
    /// Map from alias short name (case-insensitive key, stored lowercase) to
    /// the resolved ARM path.
    pub entries: BTreeMap<String, ResolvedEntry>,
    /// Array field names whose elements are sub-resources (have their own
    /// `properties` wrapper to flatten).  Stored pre-lowercased so consumers
    /// can look up directly without per-call allocation.
    pub sub_resource_arrays: BTreeSet<String>,
    /// Precomputed casing restoration map built from the resource type's aliases.
    pub casing_map: BTreeMap<String, String>,

    // ── Precomputed aggregate fields ────────────────────────────────────
    /// Precomputed aggregates for the default path (api_version = None).
    pub default_aggregates: VersionedAggregates,
    /// Precomputed aggregates keyed by lowercase api_version string.
    /// Computed at registry-load time for every distinct version found in
    /// any entry's `versioned_paths`.
    pub versioned_aggregates: BTreeMap<String, VersionedAggregates>,
}

/// Precomputed aggregate data for a specific API version, or for the default path.
///
/// Stored at [`ResolvedAliases`] level so it is computed once at registry-load
/// time rather than reconstructed on every normalize/denormalize call.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VersionedAggregates {
    /// Top-level normalized keys owned by alias transforms for this version.
    pub alias_owned_normalized_roots: BTreeSet<String>,
    /// Precomputed sub-resource array rewrap operations.
    pub sub_resource_rewraps: Vec<PrecomputedSubResourceRewrap>,
    /// Precomputed scalar alias operations for normalization.
    pub scalar_aliases_normalize: Vec<PrecomputedScalarNormalize>,
    /// Precomputed scalar alias operations for denormalization.
    pub scalar_aliases_denormalize: Vec<PrecomputedScalarDenormalize>,
    /// Precomputed element-level field remaps for wildcard aliases.
    pub element_remaps: Vec<PrecomputedRemap>,
    /// Precomputed reverse element remaps for denormalization.
    pub reverse_element_remaps: Vec<PrecomputedReverseRemap>,
    /// Deduplicated array base renames for normalization: `(arm_base_lc, short_base_lc)`.
    pub array_renames_normalize: Vec<(String, String)>,
    /// Deduplicated array base renames for denormalization: `(short_base_lc, arm_base)`.
    pub array_renames_denormalize: Vec<(String, String)>,
}

/// A precomputed scalar alias operation used during normalization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrecomputedScalarNormalize {
    /// Source ARM path segments for reading from raw ARM JSON.
    pub arm_path_segments: Vec<String>,
    /// Original-cased alias short name, used when normalizing extracted values.
    pub short_name: String,
    /// Normalized output path materialized in `input.resource`.
    pub normalized_path: String,
}

/// A precomputed scalar alias operation used during denormalization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrecomputedScalarDenormalize {
    /// Normalized path segments to read from `input.resource`.
    pub normalized_path_segments: Vec<String>,
    /// ARM path to write during denormalization.
    pub arm_path: String,
    /// Whether the ARM path should be written under `properties`.
    pub write_to_properties: bool,
}

/// A precomputed sub-resource array rewrap operation used during denormalization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrecomputedSubResourceRewrap {
    /// Path of parent arrays leading to the target array.
    pub parent_path: Vec<String>,
    /// Name of the target sub-resource array under each parent.
    pub array_name: String,
    /// Lowercased envelope fields that remain at the element root.
    pub envelope_fields: BTreeSet<String>,
}

/// A precomputed element-level field remap, stored at `ResolvedAliases` level
/// so it's computed once at registry-load time rather than per-call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrecomputedRemap {
    /// Chain of array navigations for nested `[*]` levels.
    pub array_chain: Vec<Vec<String>>,
    /// Field to read within each element.
    pub source_field: String,
    /// Field to write within each element.
    pub target_field: String,
}

/// A precomputed reverse remap for denormalization, including the forward
/// target field name for cleanup after remapping.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrecomputedReverseRemap {
    /// Chain of array navigations for nested `[*]` levels.
    pub array_chain: Vec<Vec<String>>,
    /// Field to read within each element (was the forward target).
    pub source_field: String,
    /// Field to write within each element (was the forward source),
    /// stored with original ARM casing so no runtime casing restoration is needed.
    pub target_field: String,
    /// The forward target field to remove after remapping.
    pub cleanup_field: String,
}

/// A resolved alias entry with its default path and optional versioned paths.
#[derive(Debug, Clone)]
pub struct ResolvedEntry {
    /// The original-cased alias short name (e.g., `"accountType"`, not
    /// `"accounttype"`).  The entries map uses lowercase keys for
    /// case-insensitive lookup, but the normalizer needs the original casing
    /// to write values at correctly-cased paths in the output.
    pub short_name: String,
    /// The default ARM JSON path.
    pub default_path: String,
    /// Precomputed normalized key used in the materialized `input.resource`
    /// object for scalar alias lookup during denormalization.
    pub normalized_key: String,
    /// Versioned path overrides: `(api_version, arm_path)` pairs.
    pub versioned_paths: Vec<(String, String)>,
    /// Optional metadata from the alias catalog (type, modifiability).
    pub metadata: Option<AliasPathMetadata>,

    // ── Precomputed fields (derived at registry-load time) ──────────────
    /// Whether `short_name` contains `[*]` (i.e., this is a wildcard/array alias).
    pub is_wildcard: bool,
    /// Precomputed `default_path.split('.').collect()` for fast ARM path navigation.
    pub default_path_segments: Vec<String>,
    /// Precomputed path segments for each versioned path, in the same order
    /// as `versioned_paths`.
    pub versioned_path_segments: Vec<Vec<String>>,
    /// Precomputed normalized output path segments.
    pub normalized_key_segments: Vec<String>,
    /// Top-level normalized key that owns this alias in `input.resource`.
    pub normalized_root_key: String,
}

impl ResolvedEntry {
    /// Build a `ResolvedEntry` and precompute derived fields.
    pub fn new(
        short_name: String,
        default_path: String,
        versioned_paths: Vec<(String, String)>,
        metadata: Option<AliasPathMetadata>,
    ) -> Self {
        let is_wildcard = short_name.contains("[*]");
        let normalized_key = if is_root_field_collision(&short_name, &default_path) {
            collision_safe_key(&short_name)
        } else {
            short_name.to_ascii_lowercase()
        };
        let default_path_segments = default_path.split('.').map(String::from).collect();
        let versioned_path_segments = versioned_paths
            .iter()
            .map(|(_, p)| p.split('.').map(String::from).collect())
            .collect();
        let normalized_key_segments: Vec<String> =
            normalized_key.split('.').map(String::from).collect();
        let normalized_root_key = normalized_key_segments
            .first()
            .map(|segment: &String| String::from(segment.trim_end_matches("[*]")))
            .unwrap_or_else(|| normalized_key.clone());
        Self {
            short_name,
            default_path,
            normalized_key,
            versioned_paths,
            metadata,
            is_wildcard,
            default_path_segments,
            versioned_path_segments,
            normalized_key_segments,
            normalized_root_key,
        }
    }

    /// Select the ARM path for a given API version.
    ///
    /// If `api_version` is `Some` and matches a versioned path, returns that
    /// path. Otherwise returns the `default_path`.
    pub fn select_path(&self, api_version: Option<&str>) -> &str {
        if let Some(ver) = api_version {
            for (v, path) in &self.versioned_paths {
                if v.eq_ignore_ascii_case(ver) {
                    return path;
                }
            }
        }
        &self.default_path
    }

    /// Select pre-tokenized path segments for a given API version.
    ///
    /// Returns the versioned segments if `api_version` matches, otherwise
    /// the default segments.  This avoids per-call `split('.')` for both
    /// default and versioned scalar alias navigation.
    pub fn select_path_segments(&self, api_version: Option<&str>) -> &[String] {
        if let Some(ver) = api_version {
            for (i, (v, _)) in self.versioned_paths.iter().enumerate() {
                if v.eq_ignore_ascii_case(ver) {
                    if let Some(segs) = self.versioned_path_segments.get(i) {
                        return segs;
                    }
                }
            }
        }
        &self.default_path_segments
    }

    /// Return the normalized key materialized in `input.resource` for this alias.
    pub fn normalized_output_key(&self) -> &str {
        &self.normalized_key
    }

    /// Return the normalized output path segments materialized in `input.resource`.
    pub fn normalized_output_segments(&self) -> &[String] {
        &self.normalized_key_segments
    }

    /// Return the top-level normalized key that owns this alias.
    pub fn normalized_root_key(&self) -> &str {
        &self.normalized_root_key
    }
}

impl ResolvedAliases {
    /// Select precomputed aggregates for the requested API version.
    pub fn select_aggregates(&self, api_version: Option<&str>) -> &VersionedAggregates {
        api_version.map_or(&self.default_aggregates, |ver| {
            let ver_lc = ver.to_ascii_lowercase();
            self.versioned_aggregates
                .get(&ver_lc)
                .unwrap_or(&self.default_aggregates)
        })
    }
}

#[cfg(test)]
#[allow(clippy::indexing_slicing, clippy::unwrap_used)]
mod tests {
    use alloc::string::ToString as _;
    use alloc::vec;

    use super::*;

    fn make_entry(short: &str, default: &str, versioned: Vec<(&str, &str)>) -> ResolvedEntry {
        ResolvedEntry::new(
            short.to_string(),
            default.to_string(),
            versioned
                .into_iter()
                .map(|(v, p)| (v.to_string(), p.to_string()))
                .collect(),
            None,
        )
    }

    #[test]
    fn select_path_no_version_returns_default() {
        let entry = make_entry(
            "enabled",
            "properties.enabled",
            vec![("2020-01-01", "properties.isEnabled")],
        );
        assert_eq!(entry.select_path(None), "properties.enabled");
    }

    #[test]
    fn select_path_matching_version() {
        let entry = make_entry(
            "enabled",
            "properties.enabled",
            vec![
                ("2020-01-01", "properties.isEnabled"),
                ("2021-06-01", "properties.enabled"),
            ],
        );
        assert_eq!(
            entry.select_path(Some("2020-01-01")),
            "properties.isEnabled"
        );
    }

    #[test]
    fn select_path_no_matching_version_returns_default() {
        let entry = make_entry(
            "enabled",
            "properties.enabled",
            vec![("2020-01-01", "properties.isEnabled")],
        );
        assert_eq!(entry.select_path(Some("9999-01-01")), "properties.enabled");
    }

    #[test]
    fn select_path_case_insensitive_version() {
        let entry = make_entry(
            "enabled",
            "properties.enabled",
            vec![("2020-01-01-Preview", "properties.isEnabled")],
        );
        assert_eq!(
            entry.select_path(Some("2020-01-01-preview")),
            "properties.isEnabled"
        );
    }

    #[test]
    fn select_path_empty_versioned_paths() {
        let entry = make_entry("enabled", "properties.enabled", vec![]);
        assert_eq!(entry.select_path(Some("2020-01-01")), "properties.enabled");
    }

    #[test]
    fn deserialize_provider_aliases() {
        let json = r#"{
            "namespace": "Microsoft.Storage",
            "resourceTypes": [
                {
                    "resourceType": "storageAccounts",
                    "aliases": [
                        {
                            "name": "Microsoft.Storage/storageAccounts/sku.name",
                            "defaultPath": "sku.name",
                            "defaultMetadata": { "type": "String", "attributes": "Modifiable" },
                            "paths": []
                        },
                        {
                            "name": "Microsoft.Storage/storageAccounts/accessTier",
                            "defaultPath": "properties.accessTier",
                            "paths": [
                                {
                                    "path": "properties.accessTier",
                                    "apiVersions": ["2021-01-01", "2020-08-01-preview"],
                                    "metadata": { "type": "String" }
                                }
                            ]
                        }
                    ]
                }
            ]
        }"#;

        let provider: ProviderAliases = serde_json::from_str(json).unwrap();
        assert_eq!(provider.namespace, "Microsoft.Storage");
        assert_eq!(provider.resource_types.len(), 1);

        let rt = &provider.resource_types[0];
        assert_eq!(rt.resource_type, "storageAccounts");
        assert_eq!(rt.aliases.len(), 2);

        let sku_alias = &rt.aliases[0];
        assert_eq!(sku_alias.default_path.as_deref(), Some("sku.name"));
        assert!(sku_alias.paths.is_empty());

        let access_alias = &rt.aliases[1];
        assert_eq!(access_alias.paths.len(), 1);
        assert_eq!(access_alias.paths[0].api_versions.len(), 2);
    }

    #[test]
    fn deserialize_alias_metadata() {
        let json = r#"{
            "name": "test/alias",
            "defaultPath": "properties.value",
            "defaultMetadata": { "type": "Integer", "attributes": "None" },
            "paths": []
        }"#;
        let entry: AliasEntry = serde_json::from_str(json).unwrap();
        let meta = entry.default_metadata.unwrap();
        assert_eq!(meta.kind.as_deref(), Some("Integer"));
        assert_eq!(meta.attributes.as_deref(), Some("None"));
    }

    #[test]
    fn deserialize_az_cli_default_path_object() {
        let json = r#"{
            "name": "Microsoft.Compute/virtualMachines/sku.name",
            "defaultPath": {
                "path": "properties.hardwareProfile.vmSize",
                "apiVersions": ["2024-07-01"]
            },
            "paths": []
        }"#;
        let entry: AliasEntry = serde_json::from_str(json).unwrap();
        assert_eq!(
            entry.default_path.as_deref(),
            Some("properties.hardwareProfile.vmSize")
        );
    }

    #[test]
    fn alias_type_flags() {
        let json = r#"{
            "name": "test",
            "type": "Mask, Deprecated",
            "defaultMetadata": { "type": "String", "attributes": "Modifiable, SupportsCreate" },
            "paths": []
        }"#;
        let entry: AliasEntry = serde_json::from_str(json).unwrap();
        assert!(entry.is_secret());
        assert!(entry.is_deprecated());
        assert!(!entry.is_preview());
        assert!(entry.default_metadata.as_ref().unwrap().is_modifiable());
    }

    #[test]
    fn load_auto_detects_format() {
        let array_json = r#"[{"namespace":"N","resourceTypes":[]}]"#;
        let arm_json = r#"{"value":[{"namespace":"N","resourceTypes":[]}]}"#;
        assert_eq!(load_auto(array_json).unwrap()[0].namespace, "N");
        assert_eq!(load_auto(arm_json).unwrap()[0].namespace, "N");
    }

    #[test]
    fn deserialize_pattern() {
        let json = r#"{
            "name": "test",
            "defaultPath": "p",
            "paths": [{
                "path": "p",
                "apiVersions": ["2020-01-01"],
                "pattern": {
                    "phrase": "/Subscriptions/{sub}/Providers/{prov}",
                    "variable": "prov",
                    "type": "Extract"
                }
            }]
        }"#;
        let entry: AliasEntry = serde_json::from_str(json).unwrap();
        let pattern = entry.paths[0].pattern.as_ref().unwrap();
        assert_eq!(pattern.pattern_type.as_deref(), Some("Extract"));
        assert_eq!(pattern.variable.as_deref(), Some("prov"));
    }

    #[test]
    fn capabilities_preserved() {
        let json = r#"{
            "namespace": "NS",
            "resourceTypes": [{
                "resourceType": "rt",
                "capabilities": "SupportsTags, SupportsLocation",
                "aliases": []
            }]
        }"#;
        let provider: ProviderAliases = serde_json::from_str(json).unwrap();
        assert_eq!(
            provider.resource_types[0].capabilities.as_deref(),
            Some("SupportsTags, SupportsLocation")
        );
    }
}
