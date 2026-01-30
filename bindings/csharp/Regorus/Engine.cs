// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Runtime.InteropServices;
using System.Text;
using Regorus.Internal;


#nullable enable
namespace Regorus
{
    /// <summary>
    /// C# Wrapper for the Regorus engine.
    /// This class is not thread-safe. For multithreaded use, prefer cloning after adding policies and data to an instance.
    /// Cloning is cheap and involves only incrementing reference counts for shared immutable objects like parsed policies,
    /// data etc. Mutable state is deep copied as needed.
    /// </summary>
    public unsafe sealed class Engine : IDisposable
    {
        private RegorusEngineHandle? _handle;
        private int _isDisposed;

        public Engine()
        {
            _handle = RegorusEngineHandle.Create();
        }

        public static void SetFallbackExecutionTimerConfig(ExecutionTimerConfig config)
        {
            var nativeConfig = config.ToNative();
            CheckAndDropResult(Regorus.Internal.API.regorus_set_fallback_execution_timer_config(nativeConfig));
        }

        public static void ClearFallbackExecutionTimerConfig()
        {
            CheckAndDropResult(Regorus.Internal.API.regorus_clear_fallback_execution_timer_config());
        }

        public void Dispose()
        {
            Dispose(disposing: true);

            // This object will be cleaned up by the Dispose method.
            // Therefore, call GC.SuppressFinalize to
            // take this object off the finalization queue
            // and prevent finalization code for this object
            // from executing a second time.
            GC.SuppressFinalize(this);
        }

        // Dispose(bool disposing) executes in two distinct scenarios.
        // If disposing equals true, the method has been called directly
        // or indirectly by a user's code. Managed and unmanaged resources
        // can be disposed.
        // If disposing equals false, the method has been called by the
        // runtime from inside the finalizer and you should not reference
        // other objects. Only unmanaged resources can be disposed.
        void Dispose(bool disposing)
        {
            if (System.Threading.Interlocked.CompareExchange(ref _isDisposed, 1, 0) == 0)
            {
                _handle?.Dispose();
                _handle = null;
            }
        }

        private Engine(RegorusEngineHandle handle)
        {
            _handle = handle ?? throw new ArgumentNullException(nameof(handle));
        }

        public Engine Clone()
        {
            ThrowIfDisposed();
            return UseHandle(enginePtr =>
            {
                unsafe
                {
                    var clonePtr = Regorus.Internal.API.regorus_engine_clone((Regorus.Internal.RegorusEngine*)enginePtr);
                    if (clonePtr is null)
                    {
                        throw new InvalidOperationException("Failed to clone Regorus engine.");
                    }

                    var handle = RegorusEngineHandle.FromPointer((IntPtr)clonePtr);
                    return new Engine(handle);
                }
            });
        }

        public void SetStrictBuiltinErrors(bool strict)
        {
            ThrowIfDisposed();
            UseHandle(enginePtr =>
            {
                unsafe
                {
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_strict_builtin_errors((Regorus.Internal.RegorusEngine*)enginePtr, strict));
                }
            });
        }

        public void SetExecutionTimerConfig(ExecutionTimerConfig config)
        {
            ThrowIfDisposed();
            var nativeConfig = config.ToNative();
            UseHandle(enginePtr =>
            {
                unsafe
                {
                    var localConfig = nativeConfig;
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_execution_timer_config((Regorus.Internal.RegorusEngine*)enginePtr, &localConfig));
                }
            });
        }

        public void ClearExecutionTimerConfig()
        {
            ThrowIfDisposed();
            UseHandle(enginePtr =>
            {
                unsafe
                {
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_clear_execution_timer_config((Regorus.Internal.RegorusEngine*)enginePtr));
                }
            });
        }
        public string? AddPolicy(string path, string rego)
        {
            ThrowIfDisposed();
            return Utf8Marshaller.WithUtf8(path, pathPtr =>
                Utf8Marshaller.WithUtf8(rego, regoPtr =>
                {
                    unsafe
                    {
                        return UseHandle(enginePtr =>
                        {
                            unsafe
                            {
                                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_policy((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)pathPtr, (byte*)regoPtr));
                            }
                        });
                    }
                }));
        }

        public void SetRegoV0(bool enable)
        {
            ThrowIfDisposed();
            UseHandle(enginePtr =>
            {
                unsafe
                {
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_rego_v0((Regorus.Internal.RegorusEngine*)enginePtr, enable));
                }
            });
        }

        public string? AddPolicyFromFile(string path)
        {
            ThrowIfDisposed();
            return Utf8Marshaller.WithUtf8(path, pathPtr =>
            {
                unsafe
                {
                    return UseHandle(enginePtr =>
                    {
                        unsafe
                        {
                            return CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_policy_from_file((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)pathPtr));
                        }
                    });
                }
            });

        }

        public void AddDataJson(string data)
        {
            ThrowIfDisposed();
            Utf8Marshaller.WithUtf8(data, dataPtr =>
            {
                unsafe
                {
                    UseHandle(enginePtr =>
                    {
                        unsafe
                        {
                            CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_data_json((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)dataPtr));
                        }
                    });
                }
            });

        }

        public void AddDataFromJsonFile(string path)
        {
            ThrowIfDisposed();
            Utf8Marshaller.WithUtf8(path, pathPtr =>
            {
                unsafe
                {
                    UseHandle(enginePtr =>
                    {
                        unsafe
                        {
                            CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_data_from_json_file((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)pathPtr));
                        }
                    });
                }
            });

        }

        public void SetInputJson(string input)
        {
            ThrowIfDisposed();
            Utf8Marshaller.WithUtf8(input, inputPtr =>
            {
                unsafe
                {
                    UseHandle(enginePtr =>
                    {
                        unsafe
                        {
                            CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_input_json((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)inputPtr));
                        }
                    });
                }
            });
        }

        public void SetInputFromJsonFile(string path)
        {
            ThrowIfDisposed();
            Utf8Marshaller.WithUtf8(path, pathPtr =>
            {
                unsafe
                {
                    UseHandle(enginePtr =>
                    {
                        unsafe
                        {
                            CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_input_from_json_file((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)pathPtr));
                        }
                    });
                }
            });
        }

        public string? EvalQuery(string query)
        {
            ThrowIfDisposed();
            return Utf8Marshaller.WithUtf8(query, queryPtr =>
            {
                unsafe
                {
                    return UseHandle(enginePtr =>
                    {
                        unsafe
                        {
                            return CheckAndDropResult(Regorus.Internal.API.regorus_engine_eval_query((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)queryPtr));
                        }
                    });
                }
            });
        }

        public string? EvalRule(string rule)
        {
            ThrowIfDisposed();
            return Utf8Marshaller.WithUtf8(rule, rulePtr =>
            {
                unsafe
                {
                    return UseHandle(enginePtr =>
                    {
                        unsafe
                        {
                            return CheckAndDropResult(Regorus.Internal.API.regorus_engine_eval_rule((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)rulePtr));
                        }
                    });
                }
            });
        }

        public void SetEnableCoverage(bool enable)
        {
            ThrowIfDisposed();
            UseHandle(enginePtr =>
            {
                unsafe
                {
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_enable_coverage((Regorus.Internal.RegorusEngine*)enginePtr, enable));
                }
            });
        }

        public void ClearCoverageData()
        {
            ThrowIfDisposed();
            UseHandle(enginePtr =>
            {
                unsafe
                {
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_clear_coverage_data((Regorus.Internal.RegorusEngine*)enginePtr));
                }
            });
        }

        public string? GetCoverageReport()
        {
            ThrowIfDisposed();
            return UseHandle(enginePtr =>
            {
                unsafe
                {
                    return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_coverage_report((Regorus.Internal.RegorusEngine*)enginePtr));
                }
            });
        }

        public string? GetCoverageReportPretty()
        {
            ThrowIfDisposed();
            return UseHandle(enginePtr =>
            {
                unsafe
                {
                    return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_coverage_report_pretty((Regorus.Internal.RegorusEngine*)enginePtr));
                }
            });
        }

        public void SetGatherPrints(bool enable)
        {
            ThrowIfDisposed();
            UseHandle(enginePtr =>
            {
                unsafe
                {
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_gather_prints((Regorus.Internal.RegorusEngine*)enginePtr, enable));
                }
            });
        }

        public string? TakePrints()
        {
            ThrowIfDisposed();
            return UseHandle(enginePtr =>
            {
                unsafe
                {
                    return CheckAndDropResult(Regorus.Internal.API.regorus_engine_take_prints((Regorus.Internal.RegorusEngine*)enginePtr));
                }
            });
        }

        public string? GetAstAsJson()
        {
            ThrowIfDisposed();
            return UseHandle(enginePtr =>
            {
                unsafe
                {
                    return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_ast_as_json((Regorus.Internal.RegorusEngine*)enginePtr));
                }
            });
        }

        public string? GetPolicyPackageNames()
        {
            ThrowIfDisposed();
            return UseHandle(enginePtr =>
            {
                unsafe
                {
                    return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_policy_package_names((Regorus.Internal.RegorusEngine*)enginePtr));
                }
            });
        }

        public string? GetPolicyParameters()
        {
            ThrowIfDisposed();
            return UseHandle(enginePtr =>
            {
                unsafe
                {
                    return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_policy_parameters((Regorus.Internal.RegorusEngine*)enginePtr));
                }
            });
        }

    private static string? StringFromUtf8(IntPtr ptr)
        {

#if NETSTANDARD2_1
			return Marshal.PtrToStringUTF8(ptr);
#else
            int len = 0;
            while (Marshal.ReadByte(ptr, len) != 0) { ++len; }
            byte[] buffer = new byte[len];
            Marshal.Copy(ptr, buffer, 0, buffer.Length);
            return Encoding.UTF8.GetString(buffer);
#endif
        }

    private static string? CheckAndDropResult(Regorus.Internal.RegorusResult result)
        {
            try
            {
                if (result.status != Regorus.Internal.RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                return result.data_type switch
                {
                    Regorus.Internal.RegorusDataType.String => Utf8Marshaller.FromUtf8(result.output),
                    Regorus.Internal.RegorusDataType.Boolean => result.bool_value.ToString().ToLowerInvariant(),
                    Regorus.Internal.RegorusDataType.Integer => result.int_value.ToString(),
                    Regorus.Internal.RegorusDataType.None => null,
                    _ => Utf8Marshaller.FromUtf8(result.output)
                };
            }
            finally
            {
                Regorus.Internal.API.regorus_result_drop(result);
            }
        }

        private void ThrowIfDisposed()
        {
            if (_isDisposed != 0 || _handle is null || _handle.IsClosed)
            {
                throw new ObjectDisposedException(nameof(Engine));
            }
        }

        internal RegorusEngineHandle GetHandleForUse()
        {
            var handle = _handle;
            if (handle is null || handle.IsClosed || handle.IsInvalid)
            {
                throw new ObjectDisposedException(nameof(Engine));
            }
            return handle;
        }

        internal void UseHandle(Action<IntPtr> action)
        {
            UseHandle<object?>(handlePtr =>
            {
                action(handlePtr);
                return null;
            });
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
                    throw new ObjectDisposedException(nameof(Engine));
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

    }
}
