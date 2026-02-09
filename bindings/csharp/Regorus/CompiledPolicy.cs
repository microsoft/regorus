// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Text.Json;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Represents a compiled Regorus policy that can be evaluated efficiently.
    /// This class wraps a pre-compiled policy that can be evaluated multiple times
    /// with different inputs without recompilation overhead.
    /// 
    /// This class manages unmanaged resources and should not be copied or cloned.
    /// Each instance represents a unique native policy object.
    /// 
    /// Thread Safety: This class is thread-safe for all operations. Multiple threads
    /// can safely call EvalWithInput() concurrently. Dispose() blocks new calls, waits
    /// briefly, and defers the native release to the last in-flight caller if needed.
    /// No external synchronization is required.
    /// </summary>
    public unsafe sealed class CompiledPolicy : SafeHandleWrapper
    {
        internal CompiledPolicy(RegorusCompiledPolicyHandle handle)
            : base(handle, nameof(CompiledPolicy))
        {
        }

        /// <summary>
        /// Evaluates the compiled policy with the given input.
        /// For target policies, evaluates the target's effect rule.
        /// For regular policies, evaluates the originally compiled rule.
        /// </summary>
        /// <param name="inputJson">JSON encoded input data (resource) to validate against the policy</param>
        /// <returns>The evaluation result as JSON string</returns>
        /// <exception cref="Exception">Thrown when policy evaluation fails</exception>
        /// <exception cref="ObjectDisposedException">Thrown when the policy has been disposed</exception>
        public string? EvalWithInput(string inputJson)
        {
            return Internal.Utf8Marshaller.WithUtf8(inputJson, inputPtr =>
            {
                return UseHandle(policyPtr =>
                {
                    unsafe
                    {
                        return CheckAndDropResult(Internal.API.regorus_compiled_policy_eval_with_input((Internal.RegorusCompiledPolicy*)policyPtr, (byte*)inputPtr));
                    }
                });
            });
        }

        /// <summary>
        /// Gets information about the compiled policy including metadata about modules,
        /// target configuration, and resource types.
        /// </summary>
        /// <returns>Policy information containing module IDs, target name, applicable resource types, entry point rule, and parameters</returns>
        /// <exception cref="Exception">Thrown when getting policy info fails</exception>
        /// <exception cref="ObjectDisposedException">Thrown when the policy has been disposed</exception>
        public PolicyInfo GetPolicyInfo()
        {
            var jsonResult = UseHandle(policyPtr =>
            {
                unsafe
                {
                    return CheckAndDropResult(Internal.API.regorus_compiled_policy_get_policy_info((Internal.RegorusCompiledPolicy*)policyPtr));
                }
            });

            if (string.IsNullOrEmpty(jsonResult))
            {
                throw new Exception("Failed to get policy info: empty response");
            }

            try
            {
                var options = new JsonSerializerOptions
                {
                    PropertyNameCaseInsensitive = true
                };

                return JsonSerializer.Deserialize<PolicyInfo>(jsonResult!, options)
                    ?? throw new Exception("Failed to deserialize policy info");
            }
            catch (JsonException ex)
            {
                throw new Exception($"Failed to parse policy info JSON: {ex.Message}", ex);
            }
        }

        private string? CheckAndDropResult(Internal.RegorusResult result)
        {
            return Internal.ResultHelpers.GetStringResult(result);
        }
    }
}
