// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Wrapper for the Regorus RVM runtime.
    /// </summary>
    public unsafe sealed class Rvm : IDisposable
    {
        private RegorusRvmHandle? _handle;
        private int _isDisposed;

        public Rvm()
        {
            _handle = RegorusRvmHandle.Create();
        }

        private Rvm(RegorusRvmHandle handle)
        {
            _handle = handle ?? throw new ArgumentNullException(nameof(handle));
        }

        /// <summary>
        /// Create an RVM instance backed by a compiled policy (for default rule evaluation).
        /// </summary>
        public static Rvm CreateWithPolicy(CompiledPolicy policy)
        {
            if (policy is null)
            {
                throw new ArgumentNullException(nameof(policy));
            }

            return policy.UseHandleForInterop(policyPtr =>
            {
                var result = API.regorus_rvm_new_with_policy((RegorusCompiledPolicy*)policyPtr);
                return GetRvmResult(result);
            });
        }

        /// <summary>
        /// Load a program into the VM.
        /// </summary>
        public void LoadProgram(Program program)
        {
            ThrowIfDisposed();
            if (program is null)
            {
                throw new ArgumentNullException(nameof(program));
            }

            program.UseHandle(programPtr =>
            {
                UseHandle(vmPtr =>
                {
                    CheckAndDropResult(API.regorus_rvm_load_program((RegorusRvm*)vmPtr, (RegorusProgram*)programPtr));
                    return 0;
                });
                return 0;
            });
        }

        /// <summary>
        /// Set the data document for the VM.
        /// </summary>
        public void SetDataJson(string dataJson)
        {
            ThrowIfDisposed();
            Utf8Marshaller.WithUtf8(dataJson, dataPtr =>
            {
                UseHandle(vmPtr =>
                {
                    CheckAndDropResult(API.regorus_rvm_set_data((RegorusRvm*)vmPtr, (byte*)dataPtr));
                    return 0;
                });
            });
        }

        /// <summary>
        /// Set the input document for the VM.
        /// </summary>
        public void SetInputJson(string inputJson)
        {
            ThrowIfDisposed();
            Utf8Marshaller.WithUtf8(inputJson, inputPtr =>
            {
                UseHandle(vmPtr =>
                {
                    CheckAndDropResult(API.regorus_rvm_set_input((RegorusRvm*)vmPtr, (byte*)inputPtr));
                    return 0;
                });
            });
        }

        /// <summary>
        /// Set the execution mode (0 = run-to-completion, 1 = suspendable).
        /// </summary>
        public void SetExecutionMode(byte mode)
        {
            ThrowIfDisposed();
            UseHandle(vmPtr =>
            {
                CheckAndDropResult(API.regorus_rvm_set_execution_mode((RegorusRvm*)vmPtr, mode));
                return 0;
            });
        }

        /// <summary>
        /// Execute the program and return the JSON result.
        /// </summary>
        public string? Execute()
        {
            ThrowIfDisposed();
            return UseHandle(vmPtr =>
            {
                return CheckAndDropResult(API.regorus_rvm_execute((RegorusRvm*)vmPtr));
            });
        }

        /// <summary>
        /// Execute a named entry point.
        /// </summary>
        public string? ExecuteEntryPoint(string entryPoint)
        {
            ThrowIfDisposed();
            return Utf8Marshaller.WithUtf8(entryPoint, entryPtr =>
            {
                return UseHandle(vmPtr =>
                {
                    return CheckAndDropResult(API.regorus_rvm_execute_entry_point_by_name((RegorusRvm*)vmPtr, (byte*)entryPtr));
                });
            });
        }

        /// <summary>
        /// Execute an entry point by index.
        /// </summary>
        public string? ExecuteEntryPoint(ulong index)
        {
            ThrowIfDisposed();
            return UseHandle(vmPtr =>
            {
                return CheckAndDropResult(API.regorus_rvm_execute_entry_point_by_index((RegorusRvm*)vmPtr, (UIntPtr)index));
            });
        }

        /// <summary>
        /// Resume execution with an optional value.
        /// </summary>
        public string? Resume(string? resumeValueJson)
        {
            ThrowIfDisposed();
            if (resumeValueJson is null)
            {
                return UseHandle(vmPtr =>
                {
                    return CheckAndDropResult(API.regorus_rvm_resume((RegorusRvm*)vmPtr, null, has_value: false));
                });
            }

            return Utf8Marshaller.WithUtf8(resumeValueJson, valuePtr =>
            {
                return UseHandle(vmPtr =>
                {
                    return CheckAndDropResult(API.regorus_rvm_resume((RegorusRvm*)vmPtr, (byte*)valuePtr, has_value: true));
                });
            });
        }

        /// <summary>
        /// Get the current execution state.
        /// </summary>
        public string? GetExecutionState()
        {
            ThrowIfDisposed();
            return UseHandle(vmPtr =>
            {
                return CheckAndDropResult(API.regorus_rvm_get_execution_state((RegorusRvm*)vmPtr));
            });
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
                _handle?.Dispose();
                _handle = null;
            }
        }

        private void ThrowIfDisposed()
        {
            if (_isDisposed != 0 || _handle is null || _handle.IsClosed)
            {
                throw new ObjectDisposedException(nameof(Rvm));
            }
        }

        internal RegorusRvmHandle GetHandleForUse()
        {
            var handle = _handle;
            if (handle is null || handle.IsClosed || handle.IsInvalid)
            {
                throw new ObjectDisposedException(nameof(Rvm));
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
                    throw new ObjectDisposedException(nameof(Rvm));
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

        private static Rvm GetRvmResult(RegorusResult result)
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
                    throw new Exception("Expected RVM pointer but got different data type");
                }

                var handle = RegorusRvmHandle.FromPointer((IntPtr)result.pointer_value);
                return new Rvm(handle);
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        private static string? CheckAndDropResult(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                return result.data_type switch
                {
                    RegorusDataType.String => Utf8Marshaller.FromUtf8(result.output),
                    RegorusDataType.Boolean => result.bool_value.ToString().ToLowerInvariant(),
                    RegorusDataType.Integer => result.int_value.ToString(),
                    RegorusDataType.None => null,
                    _ => Utf8Marshaller.FromUtf8(result.output)
                };
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }
    }
}
