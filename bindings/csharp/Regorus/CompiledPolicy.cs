// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Text;
using System.Text.Json;

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
    /// can safely call EvalWithInput() concurrently, and Dispose() will safely wait
    /// for all active evaluations to complete before freeing resources. No external
    /// synchronization is required.
    /// </summary>
    public unsafe sealed class CompiledPolicy : IDisposable
    {
        private Internal.RegorusCompiledPolicy* _policy;
        private int _isDisposed;
        private int _activeEvaluations;

        internal CompiledPolicy(Internal.RegorusCompiledPolicy* policy)
        {
            _policy = policy;
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
            // Increment active evaluations count
            System.Threading.Interlocked.Increment(ref _activeEvaluations);
            try
            {
                ThrowIfDisposed();
                
                var inputBytes = Encoding.UTF8.GetBytes(inputJson + char.MinValue);
                fixed (byte* inputPtr = inputBytes)
                {
                    return CheckAndDropResult(Internal.API.regorus_compiled_policy_eval_with_input(_policy, inputPtr));
                }
            }
            finally
            {
                // Decrement active evaluations count
                System.Threading.Interlocked.Decrement(ref _activeEvaluations);
            }
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
            ThrowIfDisposed();
            var jsonResult = CheckAndDropResult(Internal.API.regorus_compiled_policy_get_policy_info(_policy));
            
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

        public void Dispose()
        {
            Dispose(disposing: true);
            GC.SuppressFinalize(this);
        }

        private void Dispose(bool disposing)
        {
            if (System.Threading.Interlocked.CompareExchange(ref _isDisposed, 1, 0) == 0)
            {
                if (_policy != null)
                {
                    // Wait for all active evaluations to complete
                    while (System.Threading.Volatile.Read(ref _activeEvaluations) > 0)
                    {
                        System.Threading.Thread.Yield();
                    }
                    
                    Internal.API.regorus_compiled_policy_drop(_policy);
                    _policy = null;
                }
            }
        }

        ~CompiledPolicy() => Dispose(disposing: false);

        private void ThrowIfDisposed()
        {
            if (_isDisposed != 0)
                throw new ObjectDisposedException(nameof(CompiledPolicy));
        }

        private string? StringFromUTF8(IntPtr ptr)
        {
#if NETSTANDARD2_1
            return System.Runtime.InteropServices.Marshal.PtrToStringUTF8(ptr);
#else
            int len = 0;
            while (System.Runtime.InteropServices.Marshal.ReadByte(ptr, len) != 0) { ++len; }
            byte[] buffer = new byte[len];
            System.Runtime.InteropServices.Marshal.Copy(ptr, buffer, 0, buffer.Length);
            return Encoding.UTF8.GetString(buffer);
#endif
        }

        private string? CheckAndDropResult(Internal.RegorusResult result)
        {
            try
            {
                if (result.status != Internal.RegorusStatus.Ok)
                {
                    var message = StringFromUTF8((IntPtr)result.error_message);
                    throw new Exception(message ?? "Unknown error occurred");
                }

                return result.data_type switch
                {
                    Internal.RegorusDataType.String => StringFromUTF8((IntPtr)result.output),
                    Internal.RegorusDataType.Boolean => result.bool_value.ToString().ToLowerInvariant(),
                    Internal.RegorusDataType.Integer => result.int_value.ToString(),
                    Internal.RegorusDataType.None => null,
                    _ => StringFromUTF8((IntPtr)result.output)
                };
            }
            finally
            {
                Internal.API.regorus_result_drop(result);
            }
        }
    }
}
