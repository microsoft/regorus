// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::builtins;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use thiserror::Error;

/// An immutable set of native builtin names disabled for one compiler or VM.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[cfg_attr(docsrs, doc(cfg(feature = "rvm")))]
pub struct BuiltinPolicy {
    disabled_names: Vec<String>,
}

impl BuiltinPolicy {
    /// Create a policy that disables exactly the supplied registered builtin names.
    ///
    /// Names are validated against the builtins available in this feature
    /// configuration. Duplicate names are normalized.
    pub fn from_disabled_names(names: &[&str]) -> Result<Self, BuiltinPolicyError> {
        let mut disabled_names = Vec::new();
        for name in names {
            if !is_valid_builtin_name(name) {
                return Err(BuiltinPolicyError::InvalidName {
                    name: (*name).to_string(),
                });
            }
            if !builtins::BUILTINS.contains_key(name) {
                return Err(BuiltinPolicyError::UnknownBuiltin {
                    name: (*name).to_string(),
                });
            }
            if !disabled_names.iter().any(|disabled| disabled == name) {
                disabled_names.push((*name).to_string());
            }
        }
        disabled_names.sort_unstable();
        Ok(Self { disabled_names })
    }

    /// Return the normalized disabled native builtin names.
    pub fn disabled_names(&self) -> &[String] {
        &self.disabled_names
    }

    pub(crate) fn is_disabled(&self, name: &str) -> bool {
        self.disabled_names
            .binary_search_by(|disabled| disabled.as_str().cmp(name))
            .is_ok()
    }
}

/// Validation failures when constructing a [`BuiltinPolicy`].
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[cfg_attr(docsrs, doc(cfg(feature = "rvm")))]
pub enum BuiltinPolicyError {
    /// The supplied name is not a valid dotted Rego builtin identifier.
    #[error("invalid builtin name: {name:?}")]
    InvalidName { name: String },

    /// The supplied name is valid but is not registered in this build.
    #[error("unknown builtin name: {name}")]
    UnknownBuiltin { name: String },
}

fn is_valid_builtin_name(name: &str) -> bool {
    if name.is_empty() || name.trim() != name {
        return false;
    }

    let mut segment_start = true;
    for character in name.chars() {
        if character == '.' {
            if segment_start {
                return false;
            }
            segment_start = true;
        } else if segment_start {
            if !(character.is_ascii_alphabetic() || character == '_') {
                return false;
            }
            segment_start = false;
        } else if !(character.is_ascii_alphanumeric() || character == '_') {
            return false;
        }
    }

    !segment_start
}
