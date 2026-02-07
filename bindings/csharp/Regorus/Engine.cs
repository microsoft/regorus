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
    public unsafe sealed class Engine : SafeHandleWrapper
    {
        public Engine()
            : base(RegorusEngineHandle.Create(), nameof(Engine))
        {
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

        private Engine(RegorusEngineHandle handle)
            : base(handle, nameof(Engine))
        {
        }

        public Engine Clone()
        {
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
            UseHandle(enginePtr =>
            {
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_strict_builtin_errors((Regorus.Internal.RegorusEngine*)enginePtr, strict));
            });
        }

        public void SetExecutionTimerConfig(ExecutionTimerConfig config)
        {
            var nativeConfig = config.ToNative();
            UseHandle(enginePtr =>
            {
                var localConfig = nativeConfig;
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_execution_timer_config((Regorus.Internal.RegorusEngine*)enginePtr, &localConfig));
            });
        }

        public void ClearExecutionTimerConfig()
        {
            UseHandle(enginePtr =>
            {
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_clear_execution_timer_config((Regorus.Internal.RegorusEngine*)enginePtr));
            });
        }
        public string? AddPolicy(string path, string rego)
        {
            return Utf8Marshaller.WithUtf8(path, pathPtr =>
                Utf8Marshaller.WithUtf8(rego, regoPtr =>
                    UseHandle(enginePtr =>
                        CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_policy((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)pathPtr, (byte*)regoPtr))
                    )));
        }

        public void SetRegoV0(bool enable)
        {
            UseHandle(enginePtr =>
            {
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_rego_v0((Regorus.Internal.RegorusEngine*)enginePtr, enable));
            });
        }

        public string? AddPolicyFromFile(string path)
        {
            return Utf8Marshaller.WithUtf8(path, pathPtr =>
            {
                return UseHandle(enginePtr =>
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_policy_from_file((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)pathPtr))
                );
            });

        }

        public void AddDataJson(string data)
        {
            Utf8Marshaller.WithUtf8(data, dataPtr =>
            {
                UseHandle(enginePtr =>
                {
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_data_json((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)dataPtr));
                });
            });

        }

        public void AddDataFromJsonFile(string path)
        {
            Utf8Marshaller.WithUtf8(path, pathPtr =>
            {
                UseHandle(enginePtr =>
                {
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_add_data_from_json_file((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)pathPtr));
                });
            });

        }

        public void SetInputJson(string input)
        {
            Utf8Marshaller.WithUtf8(input, inputPtr =>
            {
                UseHandle(enginePtr =>
                {
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_input_json((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)inputPtr));
                });
            });
        }

        public void SetInputFromJsonFile(string path)
        {
            Utf8Marshaller.WithUtf8(path, pathPtr =>
            {
                UseHandle(enginePtr =>
                {
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_input_from_json_file((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)pathPtr));
                });
            });
        }

        public string? EvalQuery(string query)
        {
            return Utf8Marshaller.WithUtf8(query, queryPtr =>
            {
                return UseHandle(enginePtr =>
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_eval_query((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)queryPtr))
                );
            });
        }

        public string? EvalRule(string rule)
        {
            return Utf8Marshaller.WithUtf8(rule, rulePtr =>
            {
                return UseHandle(enginePtr =>
                    CheckAndDropResult(Regorus.Internal.API.regorus_engine_eval_rule((Regorus.Internal.RegorusEngine*)enginePtr, (byte*)rulePtr))
                );
            });
        }

        public void SetEnableCoverage(bool enable)
        {
            UseHandle(enginePtr =>
            {
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_enable_coverage((Regorus.Internal.RegorusEngine*)enginePtr, enable));
            });
        }

        public void ClearCoverageData()
        {
            UseHandle(enginePtr =>
            {
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_clear_coverage_data((Regorus.Internal.RegorusEngine*)enginePtr));
            });
        }

        public string? GetCoverageReport()
        {
            return UseHandle(enginePtr =>
            {
                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_coverage_report((Regorus.Internal.RegorusEngine*)enginePtr));
            });
        }

        public string? GetCoverageReportPretty()
        {
            return UseHandle(enginePtr =>
            {
                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_coverage_report_pretty((Regorus.Internal.RegorusEngine*)enginePtr));
            });
        }

        public void SetGatherPrints(bool enable)
        {
            UseHandle(enginePtr =>
            {
                CheckAndDropResult(Regorus.Internal.API.regorus_engine_set_gather_prints((Regorus.Internal.RegorusEngine*)enginePtr, enable));
            });
        }

        public string? TakePrints()
        {
            return UseHandle(enginePtr =>
            {
                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_take_prints((Regorus.Internal.RegorusEngine*)enginePtr));
            });
        }

        public string? GetAstAsJson()
        {
            return UseHandle(enginePtr =>
            {
                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_ast_as_json((Regorus.Internal.RegorusEngine*)enginePtr));
            });
        }

        public string? GetPolicyPackageNames()
        {
            return UseHandle(enginePtr =>
            {
                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_policy_package_names((Regorus.Internal.RegorusEngine*)enginePtr));
            });
        }

        public string? GetPolicyParameters()
        {
            return UseHandle(enginePtr =>
            {
                return CheckAndDropResult(Regorus.Internal.API.regorus_engine_get_policy_parameters((Regorus.Internal.RegorusEngine*)enginePtr));
            });
        }

        private static string? CheckAndDropResult(Regorus.Internal.RegorusResult result)
        {
            return ResultHelpers.GetStringResult(result);
        }

    }
}
