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
    /// Represents a host-awaitable builtin registration for RVM compilation.
    /// When registered, calls to the named function compile to HostAwait instructions
    /// rather than regular function calls.
    /// </summary>
    /// <remarks>
    /// This legacy registration accepts exactly one input and passes its raw
    /// Rego value to the host, including arrays and objects.
    ///
    /// Host-await builtins are not yet supported via the <c>CompileFromEngine</c>
    /// path; only <c>CompileFromModules</c> accepts them today.
    /// </remarks>
    public readonly struct HostAwaitBuiltin
    {
        /// <summary>
        /// Gets the function name to register as host-awaitable.
        /// </summary>
        public string Name { get; }

        /// <summary>
        /// Initializes a new instance of the HostAwaitBuiltin struct.
        /// </summary>
        /// <param name="name">The function name to register as host-awaitable.</param>
        /// <exception cref="ArgumentNullException">Thrown when <paramref name="name"/> is null.</exception>
        /// <exception cref="ArgumentException">Thrown when <paramref name="name"/> contains an embedded NUL ('\0').</exception>
        public HostAwaitBuiltin(string name)
        {
            Name = name ?? throw new ArgumentNullException(nameof(name));
            Utf8Marshaller.ThrowIfContainsNul(name, nameof(name));
        }
    }

    /// <summary>
    /// Represents an explicitly versioned fixed-arity packed-array
    /// host-awaitable builtin registration for RVM compilation.
    /// </summary>
    /// <remarks>
    /// The host receives an ordered array of the declared input values. A Rego
    /// output parameter, when used, is not included in the declared count.
    /// </remarks>
    public readonly struct HostAwaitBuiltinV2
    {
        /// <summary>
        /// Gets the function name to register as host-awaitable.
        /// </summary>
        public string Name { get; }

        /// <summary>
        /// Gets the number of input arguments expected by the registered function.
        /// </summary>
        public int ArgCount { get; }

        /// <summary>
        /// Initializes a new instance of the HostAwaitBuiltinV2 struct.
        /// </summary>
        /// <param name="name">The function name to register as host-awaitable.</param>
        /// <param name="argCount">The fixed number of input arguments.</param>
        /// <exception cref="ArgumentNullException">Thrown when <paramref name="name"/> is null.</exception>
        /// <exception cref="ArgumentException">Thrown when <paramref name="name"/> contains an embedded NUL ('\0').</exception>
        /// <exception cref="ArgumentOutOfRangeException">Thrown when <paramref name="argCount"/> is negative.</exception>
        public HostAwaitBuiltinV2(string name, int argCount)
        {
            Name = name ?? throw new ArgumentNullException(nameof(name));
            Utf8Marshaller.ThrowIfContainsNul(name, nameof(name));
            if (argCount < 0)
            {
                throw new ArgumentOutOfRangeException(nameof(argCount), "Argument count must be non-negative.");
            }

            ArgCount = argCount;
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
