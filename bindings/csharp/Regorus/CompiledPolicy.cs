// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Text.Json;
using System.Threading;
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
    /// can safely call EvalWithInput() concurrently, and Dispose() will safely wait
    /// for all active evaluations to complete before freeing resources. No external
    /// synchronization is required.
    /// </summary>
    public unsafe sealed class CompiledPolicy : IDisposable
    {
    private RegorusCompiledPolicyHandle? _handle;
    private readonly ManualResetEventSlim _idleEvent = new(initialState: true);
    private int _isDisposed;
    private int _activeEvaluations;

        internal CompiledPolicy(RegorusCompiledPolicyHandle handle)
        {
            _handle = handle ?? throw new ArgumentNullException(nameof(handle));
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
            var active = System.Threading.Interlocked.Increment(ref _activeEvaluations);
            if (active == 1)
            {
                _idleEvent.Reset();
            }
            try
            {
                ThrowIfDisposed();

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
            finally
            {
                // Decrement active evaluations count
                var remaining = System.Threading.Interlocked.Decrement(ref _activeEvaluations);
                if (remaining == 0)
                {
                    _idleEvent.Set();
                }
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

        public void Dispose()
        {
            Dispose(disposing: true);
            GC.SuppressFinalize(this);
        }

        private void Dispose(bool disposing)
        {
            if (System.Threading.Interlocked.CompareExchange(ref _isDisposed, 1, 0) == 0)
            {
                var handle = _handle;
                if (handle != null)
                {
                    _idleEvent.Wait();
                    
                    handle.Dispose();
                    _handle = null;
                }

                _idleEvent.Dispose();
            }
        }

        private void ThrowIfDisposed()
        {
            if (_isDisposed != 0 || _handle is null || _handle.IsClosed)
                throw new ObjectDisposedException(nameof(CompiledPolicy));
        }

        private string? CheckAndDropResult(Internal.RegorusResult result)
        {
            try
            {
                if (result.status != Internal.RegorusStatus.Ok)
                {
                    var message = Internal.Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                return result.data_type switch
                {
                    Internal.RegorusDataType.String => Internal.Utf8Marshaller.FromUtf8(result.output),
                    Internal.RegorusDataType.Boolean => result.bool_value.ToString().ToLowerInvariant(),
                    Internal.RegorusDataType.Integer => result.int_value.ToString(),
                    Internal.RegorusDataType.None => null,
                    _ => Internal.Utf8Marshaller.FromUtf8(result.output)
                };
            }
            finally
            {
                Internal.API.regorus_result_drop(result);
            }
        }

        private RegorusCompiledPolicyHandle GetHandleForUse()
        {
            var handle = _handle;
            if (handle is null || handle.IsClosed || handle.IsInvalid)
            {
                throw new ObjectDisposedException(nameof(CompiledPolicy));
            }
            return handle;
        }

        internal T UseHandle<T>(Func<IntPtr, T> func)
        {
            var handle = GetHandleForUse();
            bool addedRef = false;
            try
            {
                handle.DangerousAddRef(ref addedRef);
                var pointer = handle.DangerousGetHandle();
                if (pointer == IntPtr.Zero)
                {
                    throw new ObjectDisposedException(nameof(CompiledPolicy));
                }

                return func(pointer);
            }
            finally
            {
                if (addedRef)
                {
                    handle.DangerousRelease();
                }
            }
        }

        internal T UseHandleForInterop<T>(Func<IntPtr, T> func)
        {
            return UseHandle(func);
        }

        private void UseHandle(Action<IntPtr> action)
        {
            UseHandle<object?>(handlePtr =>
            {
                action(handlePtr);
                return null;
            });
        }
    }
}
