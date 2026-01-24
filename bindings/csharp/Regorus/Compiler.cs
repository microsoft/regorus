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
    public struct PolicyModule
    {
        /// <summary>
        /// Gets or sets the unique identifier for this policy module.
        /// </summary>
        public string Id { get; set; }

        /// <summary>
        /// Gets or sets the Rego policy content.
        /// </summary>
        public string Content { get; set; }

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
            var modulesArray = modules.ToArray();

            var nativeModules = new Internal.RegorusPolicyModule[modulesArray.Length];
            var pinnedStrings = new List<Utf8Marshaller.PinnedUtf8>(modulesArray.Length * 2);

            try
            {
                for (int i = 0; i < modulesArray.Length; i++)
                {
                    var idPinned = Utf8Marshaller.Pin(modulesArray[i].Id);
                    var contentPinned = Utf8Marshaller.Pin(modulesArray[i].Content);
                    pinnedStrings.Add(idPinned);
                    pinnedStrings.Add(contentPinned);

                    nativeModules[i] = new Internal.RegorusPolicyModule
                    {
                        id = idPinned.Pointer,
                        content = contentPinned.Pointer
                    };
                }

                return Utf8Marshaller.WithUtf8(dataJson, dataPtr =>
                    Utf8Marshaller.WithUtf8(entryPointRule, entryPointPtr =>
                    {
                        unsafe
                        {
                            fixed (Internal.RegorusPolicyModule* modulesPtr = nativeModules)
                            {
                                var result = Internal.API.regorus_compile_policy_with_entrypoint(
                                    (byte*)dataPtr, modulesPtr, (UIntPtr)modulesArray.Length, (byte*)entryPointPtr);

                                var policy = GetCompiledPolicyResult(result);
                                return policy;
                            }
                        }
                    }));
            }
            finally
            {
                foreach (var pinned in pinnedStrings)
                {
                    pinned.Dispose();
                }
            }
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
            var modulesArray = modules.ToArray();

            var nativeModules = new Internal.RegorusPolicyModule[modulesArray.Length];
            var pinnedStrings = new List<Utf8Marshaller.PinnedUtf8>(modulesArray.Length * 2);

            try
            {
                for (int i = 0; i < modulesArray.Length; i++)
                {
                    var idPinned = Utf8Marshaller.Pin(modulesArray[i].Id);
                    var contentPinned = Utf8Marshaller.Pin(modulesArray[i].Content);
                    pinnedStrings.Add(idPinned);
                    pinnedStrings.Add(contentPinned);

                    nativeModules[i] = new Internal.RegorusPolicyModule
                    {
                        id = idPinned.Pointer,
                        content = contentPinned.Pointer
                    };
                }

                return Utf8Marshaller.WithUtf8(dataJson, dataPtr =>
                {
                    unsafe
                    {
                        fixed (Internal.RegorusPolicyModule* modulesPtr = nativeModules)
                        {
                            var result = Internal.API.regorus_compile_policy_for_target(
                                (byte*)dataPtr, modulesPtr, (UIntPtr)modulesArray.Length);

                            var policy = GetCompiledPolicyResult(result);
                            return policy;
                        }
                    }
                });
            }
            finally
            {
                foreach (var pinned in pinnedStrings)
                {
                    pinned.Dispose();
                }
            }
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
