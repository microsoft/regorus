// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
using System.Linq;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Represents a policy module with an ID and content.
    /// </summary>
    public readonly struct PolicyModule
    {
        /// <summary>
        /// Gets the unique identifier for this policy module.
        /// </summary>
        public string Id { get; }

        /// <summary>
        /// Gets the Rego policy content.
        /// </summary>
        public string Content { get; }

        /// <summary>
        /// Initializes a new instance of the PolicyModule struct.
        /// </summary>
        /// <param name="id">The unique identifier for this policy module</param>
        /// <param name="content">The Rego policy content</param>
        public PolicyModule(string id, string content)
        {
            Id = id;
            Content = content;
        }
    }

    /// <summary>
    /// Provides static methods for compiling policies into efficient compiled representations.
    /// These are convenience methods that create an engine internally and perform compilation.
    /// </summary>
    public static unsafe class Compiler
    {
        /// <summary>
        /// Compiles a policy from data and modules with a specific entry point rule.
        /// This is a convenience function that sets up an Engine internally and calls the appropriate compilation method.
        /// </summary>
        /// <param name="dataJson">JSON string containing static data for policy evaluation</param>
        /// <param name="modules">List of policy modules to compile</param>
        /// <param name="entryPointRule">The specific rule path to evaluate (e.g., "data.policy.allow")</param>
        /// <returns>A compiled policy that can be evaluated efficiently</returns>
        /// <exception cref="Exception">Thrown when compilation fails</exception>
        public static CompiledPolicy CompilePolicyWithEntrypoint(string dataJson, IEnumerable<PolicyModule> modules, string entryPointRule)
        {
            if (modules is null)
            {
                throw new ArgumentNullException(nameof(modules));
            }

            return CompilePolicyWithEntrypoint(dataJson, modules.ToArray(), entryPointRule);
        }

        /// <summary>
        /// Compiles a policy from data and modules with a specific entry point rule.
        /// </summary>
        public static CompiledPolicy CompilePolicyWithEntrypoint(string dataJson, IReadOnlyList<PolicyModule> modules, string entryPointRule)
        {
            if (modules is null)
            {
                throw new ArgumentNullException(nameof(modules));
            }

            using var pinnedModules = Internal.ModuleMarshalling.PinPolicyModules(modules);

            return Utf8Marshaller.WithUtf8(dataJson, dataPtr =>
                Utf8Marshaller.WithUtf8(entryPointRule, entryPointPtr =>
                {
                    unsafe
                    {
                        fixed (Internal.RegorusPolicyModule* modulesPtr = pinnedModules.Buffer)
                        {
                            var result = Internal.API.regorus_compile_policy_with_entrypoint(
                                (byte*)dataPtr, modulesPtr, (UIntPtr)pinnedModules.Length, (byte*)entryPointPtr);

                            return GetCompiledPolicyResult(result);
                        }
                    }
                }));
        }

        /// <summary>
        /// Compiles a target-aware policy from data and modules.
        /// This is a convenience function that sets up an Engine internally and calls target-aware compilation.
        /// At least one module must contain a `__target__` declaration.
        /// </summary>
        /// <param name="dataJson">JSON string containing static data for policy evaluation</param>
        /// <param name="modules">List of policy modules to compile</param>
        /// <returns>A compiled policy that can be evaluated efficiently</returns>
        /// <exception cref="Exception">Thrown when compilation fails</exception>
        public static CompiledPolicy CompilePolicyForTarget(string dataJson, IEnumerable<PolicyModule> modules)
        {
            if (modules is null)
            {
                throw new ArgumentNullException(nameof(modules));
            }

            return CompilePolicyForTarget(dataJson, modules.ToArray());
        }

        /// <summary>
        /// Compiles a target-aware policy from data and modules.
        /// </summary>
        public static CompiledPolicy CompilePolicyForTarget(string dataJson, IReadOnlyList<PolicyModule> modules)
        {
            if (modules is null)
            {
                throw new ArgumentNullException(nameof(modules));
            }

            using var pinnedModules = Internal.ModuleMarshalling.PinPolicyModules(modules);

            return Utf8Marshaller.WithUtf8(dataJson, dataPtr =>
            {
                unsafe
                {
                    fixed (Internal.RegorusPolicyModule* modulesPtr = pinnedModules.Buffer)
                    {
                        var result = Internal.API.regorus_compile_policy_for_target(
                            (byte*)dataPtr, modulesPtr, (UIntPtr)pinnedModules.Length);

                        return GetCompiledPolicyResult(result);
                    }
                }
            });
        }

        private static CompiledPolicy GetCompiledPolicyResult(Internal.RegorusResult result)
        {
            try
            {
                if (result.status != Internal.RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                if (result.data_type != Internal.RegorusDataType.Pointer || result.pointer_value == null)
                {
                    throw new Exception("Expected compiled policy pointer but got different data type");
                }

                var handle = RegorusCompiledPolicyHandle.FromPointer((IntPtr)result.pointer_value);
                return new CompiledPolicy(handle);
            }
            finally
            {
                Internal.API.regorus_result_drop(result);
            }
        }
    }
}
