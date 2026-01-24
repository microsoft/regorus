// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Helpers for configuring and inspecting Regorus memory limits via the native allocator bridge.
    /// </summary>
    public static class MemoryLimits
    {
        /// <summary>
        /// Configure the process-wide global memory limit in bytes. Pass <c>null</c> to remove the limit.
        /// </summary>
        /// <param name="bytes">Maximum number of bytes the allocator may reserve before signalling an error.</param>
        public static void SetGlobalMemoryLimit(ulong? bytes)
        {
            var result = API.regorus_set_global_memory_limit(bytes ?? 0, bytes.HasValue);
            EnsureSuccess(result, nameof(SetGlobalMemoryLimit));
        }

        /// <summary>
        /// Returns the currently configured global memory limit, if any.
        /// </summary>
        public static ulong? GetGlobalMemoryLimit()
        {
            var result = API.regorus_get_global_memory_limit();
            return ExtractOptionalU64(result, "Failed to get global memory limit");
        }

        /// <summary>
        /// Forces the allocator to flush this thread's pending counters into the global aggregates.
        /// </summary>
        public static void FlushThreadMemoryCounters()
        {
            var result = API.regorus_flush_thread_memory_counters();
            EnsureSuccess(result, nameof(FlushThreadMemoryCounters));
        }

        /// <summary>
        /// Immediately checks the global memory limit and throws if the allocator reports exhaustion.
        /// </summary>
        public static void CheckGlobalMemoryLimit()
        {
            var result = API.regorus_check_global_memory_limit();
            EnsureSuccess(result, nameof(CheckGlobalMemoryLimit));
        }

        /// <summary>
        /// Override the per-thread automatic flush threshold in bytes. Pass <c>null</c> to restore the default.
        /// </summary>
        public static void SetThreadFlushThresholdOverride(ulong? bytes)
        {
            var result = API.regorus_set_thread_flush_threshold_override(bytes ?? 0, bytes.HasValue);
            EnsureSuccess(result, nameof(SetThreadFlushThresholdOverride));
        }

        /// <summary>
        /// Returns the per-thread flush threshold, if automatic flushing is enabled.
        /// </summary>
        public static ulong? GetThreadMemoryFlushThreshold()
        {
            var result = API.regorus_get_thread_memory_flush_threshold();
            return ExtractOptionalU64(result, "Failed to get thread memory flush threshold");
        }

        private static unsafe ulong? ExtractOptionalU64(RegorusResult result, string errorContext)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message) ?? $"{errorContext}: native call failed";
                    throw result.status.CreateException(message);
                }

                if (!result.bool_value)
                {
                    return null;
                }

                if (result.data_type != RegorusDataType.Integer)
                {
                    throw new InvalidOperationException(
                        $"{errorContext}: native call returned {result.data_type} ({(int)result.data_type}) with bool_value={result.bool_value}"
                    );
                }

                if (result.int_value < 0)
                {
                    throw new OverflowException($"{errorContext}: native value was negative ({result.int_value})");
                }

                return (ulong)result.int_value;
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        private static void EnsureSuccess(RegorusResult result, string operation)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    string? message;
                    unsafe
                    {
                        message = Utf8Marshaller.FromUtf8(result.error_message);
                    }

                    throw result.status.CreateException(message);
                }
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }
    }
}
