// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::Rc;
use thiserror::Error;

type String = Rc<str>;

/// Error type for interpreter target resolution operations.
#[derive(Debug, Clone, Error)]
pub enum TargetCompileError {
    /// Multiple different targets specified across modules
    #[error("Multiple different targets specified: '{existing}' and '{conflicting}'")]
    ConflictingTargets {
        existing: String,
        conflicting: String,
    },
    /// Target not found in registry
    #[error("Target '{0}' not found in registry")]
    TargetNotFound(String),
    /// No target specified when one is required
    #[error("No target specified. When using compile_for_target, at least one module must specify a target using the __target__ annotation")]
    NoTargetSpecified,
    /// Modules with targets have different packages
    #[error("Modules with target '{target}' have different packages: '{existing_package}' and '{conflicting_package}'")]
    ConflictingPackages {
        target: String,
        existing_package: String,
        conflicting_package: String,
    },

    /// No effects have rules defined for the target
    #[error(
        "Target '{target_name}' requires a rule with name {effect_names} in package '{package}'"
    )]
    NoEffectRules {
        target_name: String,
        package: String,
        effect_names: String,
    },
    /// Multiple effect rules found for the same effect
    #[error("Multiple effects have rules defined for target '{target_name}': {effect_names}. Only one effect should have rules defined in package '{path}'")]
    MultipleEffectRules {
        target_name: String,
        effect_names: String,
        path: String,
    },

    /// Missing default resource schema error
    #[error("Missing default resource schema: {0}")]
    MissingDefaultResourceSchema(String),
    /// Incompatible default schema error
    #[error("Incompatible default schema: {0}")]
    IncompatibleDefaultSchema(String),
    /// Invalid default schema type error
    #[error("Invalid default schema type: {0}")]
    InvalidDefaultSchemaType(String),
}
