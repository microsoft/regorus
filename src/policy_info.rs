// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(missing_debug_implementations)] // policy info structs used for serialization only

#[cfg(feature = "azure_policy")]
use crate::engine::PolicyParameters;
use crate::*;
type String = Rc<str>;

/// Information about a compiled policy, including metadata about modules,
/// target configuration, and resource types that the policy can evaluate.
#[derive(serde::Serialize)]
pub struct PolicyInfo {
    /// List of module identifiers that were compiled into this policy.
    /// Each module ID represents a unique policy module that contributes
    /// rules, functions, or data to the compiled policy.
    pub module_ids: Vec<String>,

    /// Name of the target configuration used during compilation, if any.
    /// This indicates which target schema and validation rules were applied.
    pub target_name: Option<String>,

    /// List of resource types that this policy can evaluate.
    /// For target-aware policies, this contains the inferred or configured
    /// resource types. For general policies, this may be empty.
    pub applicable_resource_types: Vec<String>,

    /// The primary rule or entrypoint that this policy evaluates.
    /// This is the rule path that will be executed when the policy runs.
    pub entrypoint_rule: String,

    /// The effect rule name for target-aware policies, if applicable.
    /// This is the specific effect rule (e.g., "effect", "allow", "deny")
    /// that determines the policy decision for target evaluation.
    pub effect_rule: Option<String>,

    /// Parameters that can be configured for this policy.
    /// Contains parameter names and their expected types or default values.
    /// Used for parameterized policies that accept configuration at evaluation time.
    /// Each element represents parameters from a different module.
    #[cfg(feature = "azure_policy")]
    pub parameters: Vec<PolicyParameters>,
}
