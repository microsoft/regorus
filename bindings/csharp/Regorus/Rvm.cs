// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Execution mode for the RVM runtime.
    /// </summary>
    public enum ExecutionMode : byte
    {
        /// <summary>
        /// Run to completion without yielding.
        /// </summary>
        RunToCompletion = 0,

        /// <summary>
        /// Suspendable execution mode.
        /// </summary>
        Suspendable = 1,
    }

    /// <summary>
    /// Wrapper for the Regorus RVM runtime.
    /// </summary>
    public unsafe sealed class Rvm : SafeHandleWrapper
    {
        public Rvm()
            : base(RegorusRvmHandle.Create(), nameof(Rvm))
        {
        }

        private Rvm(RegorusRvmHandle handle)
            : base(handle, nameof(Rvm))
        {
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
            if (program is null)
            {
                throw new ArgumentNullException(nameof(program));
            }

            program.UseHandleForInterop(programPtr =>
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
            UseHandle(vmPtr =>
            {
                CheckAndDropResult(API.regorus_rvm_set_execution_mode((RegorusRvm*)vmPtr, mode));
                return 0;
            });
        }

        /// <summary>
        /// Set the execution mode.
        /// </summary>
        public void SetExecutionMode(ExecutionMode mode)
        {
            SetExecutionMode((byte)mode);
        }

        /// <summary>
        /// Execute the program and return the JSON result.
        /// </summary>
        public string? Execute()
        {
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
            return UseHandle(vmPtr =>
            {
                return CheckAndDropResult(API.regorus_rvm_get_execution_state((RegorusRvm*)vmPtr));
            });
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
            return ResultHelpers.GetStringResult(result);
        }
    }
}
