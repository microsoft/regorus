// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;
use alloc::string::String;
use alloc::vec::Vec;

use serde::Deserialize;

use super::spec::{BuiltinPurity, BuiltinTableError, BuiltinTypeTemplate};

#[derive(Debug, Deserialize, Default)]
pub(super) struct BuiltinCatalog {
    #[serde(default)]
    pub(super) groups: Vec<BuiltinGroupConfig>,
    #[serde(default)]
    pub(super) builtins: Vec<BuiltinConfig>,
}

#[derive(Debug, Deserialize, Default)]
pub(super) struct BuiltinGroupConfig {
    #[allow(dead_code)]
    pub(super) name: String,
    #[serde(default)]
    pub(super) requires: Vec<String>,
    #[serde(default)]
    pub(super) builtins: Vec<BuiltinConfig>,
}

impl BuiltinGroupConfig {
    pub(super) fn is_enabled(&self) -> Result<bool, BuiltinTableError> {
        for feature in self.requires.iter() {
            if !feature_active(feature)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[derive(Debug, Deserialize, Clone)]
pub(super) struct BuiltinConfig {
    pub(super) name: String,
    #[serde(default)]
    pub(super) purity: Option<PurityConfig>,
    #[serde(default)]
    pub(super) cache: bool,
    #[serde(default)]
    pub(super) params: Vec<TemplateConfig>,
    #[serde(rename = "return")]
    pub(super) return_template: TemplateConfig,
}

#[derive(Debug, Deserialize, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub(super) enum PurityConfig {
    Pure,
    Impure,
}

impl PurityConfig {
    pub(super) fn into_purity(self) -> BuiltinPurity {
        match self {
            PurityConfig::Pure => BuiltinPurity::Pure,
            PurityConfig::Impure => BuiltinPurity::Impure,
        }
    }
}

#[derive(Debug, Deserialize, Clone, Copy)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum TemplateConfig {
    Any,
    Boolean,
    Number,
    Integer,
    String,
    Null,
    ArrayAny,
    SetAny,
    ObjectAny,
    SameAsArgument { index: u8 },
    CollectionElement { index: u8 },
}

impl TemplateConfig {
    pub(super) fn as_template(self) -> BuiltinTypeTemplate {
        match self {
            TemplateConfig::Any => BuiltinTypeTemplate::Any,
            TemplateConfig::Boolean => BuiltinTypeTemplate::Boolean,
            TemplateConfig::Number => BuiltinTypeTemplate::Number,
            TemplateConfig::Integer => BuiltinTypeTemplate::Integer,
            TemplateConfig::String => BuiltinTypeTemplate::String,
            TemplateConfig::Null => BuiltinTypeTemplate::Null,
            TemplateConfig::ArrayAny => BuiltinTypeTemplate::ArrayAny,
            TemplateConfig::SetAny => BuiltinTypeTemplate::SetAny,
            TemplateConfig::ObjectAny => BuiltinTypeTemplate::ObjectAny,
            TemplateConfig::SameAsArgument { index } => BuiltinTypeTemplate::SameAsArgument(index),
            TemplateConfig::CollectionElement { index } => {
                BuiltinTypeTemplate::CollectionElement(index)
            }
        }
    }
}

pub(super) fn feature_active(feature: &str) -> Result<bool, BuiltinTableError> {
    match feature {
        "" | "core" => Ok(true),
        "azure_policy" => Ok(cfg!(feature = "azure_policy")),
        "std" => Ok(cfg!(feature = "std")),
        "jsonschema" => Ok(cfg!(feature = "jsonschema")),
        "base64" => Ok(cfg!(feature = "base64")),
        "base64url" => Ok(cfg!(feature = "base64url")),
        "glob" => Ok(cfg!(feature = "glob")),
        "graph" => Ok(cfg!(feature = "graph")),
        "hex" => Ok(cfg!(feature = "hex")),
        "http" => Ok(cfg!(feature = "http")),
        "net" => Ok(cfg!(feature = "net")),
        "opa-runtime" => Ok(cfg!(feature = "opa-runtime")),
        "regex" => Ok(cfg!(feature = "regex")),
        "semver" => Ok(cfg!(feature = "semver")),
        "time" => Ok(cfg!(feature = "time")),
        "urlquery" => Ok(cfg!(feature = "urlquery")),
        "uuid" => Ok(cfg!(feature = "uuid")),
        "yaml" => Ok(cfg!(feature = "yaml")),
        "opa-testutil" => Ok(cfg!(feature = "opa-testutil")),
        other => Err(BuiltinTableError::UnknownFeature(other.to_owned())),
    }
}
