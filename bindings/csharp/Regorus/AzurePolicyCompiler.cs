// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Provides static methods for compiling Azure Policy JSON definitions
    /// into RVM programs that can be executed by <see cref="Rvm"/>.
    /// </summary>
    /// <remarks>
    /// <para>
    /// This class bridges the gap between Azure Policy JSON (the native
    /// Azure policy language with <c>policyRule</c>, <c>field</c>,
    /// <c>equals</c>, etc.) and Regorus's RVM execution engine.
    /// </para>
    ///
    /// <para>
    /// <b>Typical workflow:</b>
    /// </para>
    /// <list type="number">
    /// <item>Load alias definitions into an <see cref="AliasRegistry"/>.</item>
    /// <item>Normalize the ARM resource via <see cref="AliasRegistry.NormalizeAndWrap"/>.</item>
    /// <item>Compile the JSON policy definition with <see cref="CompilePolicyDefinition"/>.</item>
    /// <item>Execute the resulting <see cref="Program"/> in an <see cref="Rvm"/>
    ///        instance with the normalized input.</item>
    /// </list>
    ///
    /// <para>
    /// <b>Context-dependent policies:</b> Policies that use context functions
    /// such as <c>subscription()</c>, <c>resourceGroup()</c>, or
    /// <c>requestContext()</c> require the VM context to be set separately via
    /// <see cref="Rvm.SetContextJson"/> before execution. The context JSON
    /// returned by <see cref="AliasRegistry.NormalizeAndWrap"/> is passed as
    /// <c>input.context</c> but is <b>not</b> automatically wired into the VM's
    /// ambient context — the caller must do both:
    /// <c>vm.SetInputJson(envelope)</c> and <c>vm.SetContextJson(contextJson)</c>.
    /// </para>
    /// </remarks>
    public static unsafe class AzurePolicyCompiler
    {
        /// <summary>
        /// Compile a full Azure Policy definition JSON into an RVM <see cref="Program"/>.
        /// </summary>
        /// <param name="aliasRegistry">
        /// Alias registry for resolving fully-qualified alias names in field
        /// references.  Pass <c>null</c> if no alias resolution is needed.
        /// <para>
        /// <b>Warning:</b> When <c>null</c>, alias field references compile as raw
        /// property paths and will silently produce incorrect evaluation results for
        /// policies that use aliases.  Modify/Append effect policies will also skip
        /// the compile-time modifiability validation.  Only pass <c>null</c> when the
        /// policy is known to contain no alias references (e.g. simple type/location
        /// checks or unit-test scenarios).
        /// </para>
        /// </param>
        /// <param name="policyDefinitionJson">
        /// JSON string containing the full policy definition, which includes
        /// <c>policyRule</c>, <c>parameters</c>, <c>displayName</c>, etc.
        /// Accepted in both wrapped and unwrapped forms.
        /// </param>
        /// <returns>
        /// A compiled <see cref="Program"/> ready to be loaded into an
        /// <see cref="Rvm"/> instance.
        /// </returns>
        /// <exception cref="ArgumentNullException">
        /// Thrown when <paramref name="policyDefinitionJson"/> is <c>null</c>.
        /// </exception>
        /// <exception cref="Exception">
        /// Thrown when parsing or compilation fails.
        /// </exception>
        public static Program CompilePolicyDefinition(AliasRegistry? aliasRegistry, string policyDefinitionJson)
        {
            if (policyDefinitionJson is null)
            {
                throw new ArgumentNullException(nameof(policyDefinitionJson));
            }

            return Utf8Marshaller.WithUtf8(policyDefinitionJson, defnPtr =>
            {
                if (aliasRegistry is null)
                {
                    var result = API.regorus_compile_azure_policy_definition(
                        null, (byte*)defnPtr);
                    return GetProgramResult(result);
                }
                else
                {
                    return aliasRegistry.UseHandleForInterop(regPtr =>
                    {
                        var result = API.regorus_compile_azure_policy_definition(
                            (RegorusAliasRegistry*)regPtr, (byte*)defnPtr);
                        return GetProgramResult(result);
                    });
                }
            });
        }

        private static Program GetProgramResult(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                if (result.data_type != RegorusDataType.Pointer || result.pointer_value == null)
                {
                    throw new Exception("Expected program pointer but got different data type");
                }

                var handle = RegorusProgramHandle.FromPointer((IntPtr)result.pointer_value);
                return new Program(handle);
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }
    }
}
