// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System.Collections.Generic;
using System.Text.Json.Serialization;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Information about a compiled policy, including metadata about modules,
    /// target configuration, and resource types that the policy can evaluate.
    /// </summary>
    public class PolicyInfo
    {
        /// <summary>
        /// List of module identifiers that were compiled into this policy.
        /// Each module ID represents a unique policy module that contributes
        /// rules, functions, or data to the compiled policy.
        /// </summary>
        [JsonPropertyName("module_ids")]
        public List<string> ModuleIds { get; set; } = new List<string>();

        /// <summary>
        /// Name of the target configuration used during compilation, if any.
        /// This indicates which target schema and validation rules were applied.
        /// </summary>
        [JsonPropertyName("target_name")]
        public string? TargetName { get; set; }

        /// <summary>
        /// List of resource types that this policy can evaluate.
        /// For target-aware policies, this contains the inferred or configured
        /// resource types. For general policies, this may be empty.
        /// </summary>
        [JsonPropertyName("applicable_resource_types")]
        public List<string> ApplicableResourceTypes { get; set; } = new List<string>();

        /// <summary>
        /// The primary rule or entrypoint that this policy evaluates.
        /// This is the rule path that will be executed when the policy runs.
        /// </summary>
        [JsonPropertyName("entrypoint_rule")]
        public string EntrypointRule { get; set; } = string.Empty;

        /// <summary>
        /// The effect rule name for target-aware policies, if applicable.
        /// This is the specific effect rule (e.g., "effect", "allow", "deny")
        /// that determines the policy decision for target evaluation.
        /// </summary>
        [JsonPropertyName("effect_rule")]
        public string? EffectRule { get; set; }

        /// <summary>
        /// Parameters that can be configured for this policy.
        /// Contains parameter names and their expected types or default values.
        /// Used for parameterized policies that accept configuration at evaluation time.
        /// Each element represents parameters from a different module.
        /// </summary>
        [JsonPropertyName("parameters")]
        public List<PolicyParameters> Parameters { get; set; } = new List<PolicyParameters>();
    }

    /// <summary>
    /// Parameters that can be configured for a policy.
    /// </summary>
    public class PolicyParameters
    {
        /// <summary>
        /// Source file where the parameters are defined.
        /// </summary>
        [JsonPropertyName("source_file")]
        public string SourceFile { get; set; } = string.Empty;

        /// <summary>
        /// List of parameter definitions.
        /// </summary>
        [JsonPropertyName("parameters")]
        public List<PolicyParameter> Parameters { get; set; } = new List<PolicyParameter>();

        /// <summary>
        /// List of parameter modifiers.
        /// </summary>
        [JsonPropertyName("modifiers")]
        public List<PolicyParameterModifier> Modifiers { get; set; } = new List<PolicyParameterModifier>();
    }

    /// <summary>
    /// A single parameter definition.
    /// </summary>
    public class PolicyParameter
    {
        /// <summary>
        /// Name of the parameter.
        /// </summary>
        [JsonPropertyName("name")]
        public string Name { get; set; } = string.Empty;

        /// <summary>
        /// Type of the parameter.
        /// </summary>
        [JsonPropertyName("type")]
        public string Type { get; set; } = string.Empty;

        /// <summary>
        /// Default value of the parameter, if any.
        /// </summary>
        [JsonPropertyName("default")]
        public object? Default { get; set; }

        /// <summary>
        /// Description of the parameter.
        /// </summary>
        [JsonPropertyName("description")]
        public string? Description { get; set; }

        /// <summary>
        /// Allowed values for the parameter, if constrained.
        /// </summary>
        [JsonPropertyName("allowed_values")]
        public List<object>? AllowedValues { get; set; }
    }

    /// <summary>
    /// A parameter modifier that affects parameter behavior.
    /// </summary>
    public class PolicyParameterModifier
    {
        /// <summary>
        /// Name of the modifier.
        /// </summary>
        [JsonPropertyName("name")]
        public string Name { get; set; } = string.Empty;

        /// <summary>
        /// Value of the modifier.
        /// </summary>
        [JsonPropertyName("value")]
        public object? Value { get; set; }
    }
}
