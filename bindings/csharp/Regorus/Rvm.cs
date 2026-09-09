// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
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
        /// Set the context document for the VM.
        /// The context provides host-supplied ambient data (e.g. resourceGroup(),
        /// subscription()) that Azure Policy functions can access via LoadContext
        /// instructions.
        /// </summary>
        public void SetContextJson(string contextJson)
        {
            Utf8Marshaller.WithUtf8(contextJson, contextPtr =>
            {
                UseHandle(vmPtr =>
                {
                    CheckAndDropResult(API.regorus_rvm_set_context((RegorusRvm*)vmPtr, (byte*)contextPtr));
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
        /// Set the maximum number of RVM bytecode instructions dispatched by one execution.
        /// </summary>
        /// <remarks>
        /// The default is 25,000. Zero permits no dispatches. A fresh execution or program load
        /// resets the consumed count, while Resume preserves it. Updating the maximum while
        /// suspended replaces the limit without resetting the consumed count.
        /// </remarks>
        /// <param name="maxInstructions">The maximum number of dispatched instructions.</param>
        /// <exception cref="ArgumentOutOfRangeException">
        /// Thrown when the value cannot be represented by the native pointer width.
        /// </exception>
        public void SetMaxInstructions(ulong maxInstructions)
        {
            if (IntPtr.Size == 4 && maxInstructions > uint.MaxValue)
            {
                throw new ArgumentOutOfRangeException(
                    nameof(maxInstructions),
                    "The instruction limit must fit in the native pointer width.");
            }

            UseHandle(vmPtr =>
            {
                CheckAndDropResult(API.regorus_rvm_set_max_instructions(
                    (RegorusRvm*)vmPtr,
                    new UIntPtr(maxInstructions)));
                return 0;
            });
        }

        /// <summary>
        /// Configure a fresh memory budget for every run-to-completion execution.
        /// </summary>
        /// <param name="config">Memory-budget configuration.</param>
        public void SetMemoryBudgetConfig(MemoryBudgetConfig config)
        {
            var nativeConfig = config.ToNative();
            UseHandle(vmPtr =>
            {
                CheckAndDropResult(API.regorus_rvm_set_memory_budget_config(
                    (RegorusRvm*)vmPtr,
                    has_config: true,
                    nativeConfig));
                return 0;
            });
        }

        /// <summary>
        /// Clear the per-execution memory budget.
        /// </summary>
        public void ClearMemoryBudgetConfig()
        {
            UseHandle(vmPtr =>
            {
                CheckAndDropResult(API.regorus_rvm_set_memory_budget_config(
                    (RegorusRvm*)vmPtr,
                    has_config: false,
                    default));
                return 0;
            });
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

        /// <summary>
        /// Get the HostAwait argument as a JSON string.
        /// Returns null if the VM is not in a HostAwait-suspended state.
        /// </summary>
        public string? GetHostAwaitArgument()
        {
            return UseHandle(vmPtr =>
            {
                return CheckAndDropResult(API.regorus_rvm_get_host_await_argument((RegorusRvm*)vmPtr));
            });
        }

        /// <summary>
        /// Get the HostAwait identifier as a raw UTF-8 string (not JSON-quoted).
        /// Returns null if the VM is not in a HostAwait-suspended state.
        /// </summary>
        public string? GetHostAwaitIdentifier()
        {
            return UseHandle(vmPtr =>
            {
                return CheckAndDropResult(API.regorus_rvm_get_host_await_identifier((RegorusRvm*)vmPtr));
            });
        }

        /// <summary>
        /// Pre-load HostAwait responses for run-to-completion mode.
        /// </summary>
        /// <remarks>
        /// Atomically replaces all previously configured responses for every
        /// identifier. Pass all identifiers the policy may invoke in a single
        /// call; calling this method again discards the prior configuration
        /// in full.
        /// </remarks>
        /// <param name="responsesByIdentifier">
        /// Per-identifier queues of JSON-encoded response values, consumed in
        /// FIFO order when the corresponding host-await builtin is invoked.
        /// </param>
        public void SetHostAwaitResponses(IReadOnlyDictionary<string, IReadOnlyList<string>> responsesByIdentifier)
        {
            if (responsesByIdentifier is null)
            {
                throw new ArgumentNullException(nameof(responsesByIdentifier));
            }

            using var pinnedSets = ModuleMarshalling.PinHostAwaitResponseSets(responsesByIdentifier);

            UseHandle(vmPtr =>
            {
                fixed (RegorusHostAwaitResponseSet* setsPtr = pinnedSets.Buffer)
                {
                    CheckAndDropResult(API.regorus_rvm_set_host_await_responses(
                        (RegorusRvm*)vmPtr,
                        setsPtr,
                        (UIntPtr)pinnedSets.Length,
                        (UIntPtr)sizeof(RegorusHostAwaitResponseSet)));
                }
                return 0;
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
