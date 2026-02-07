// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

#nullable enable

namespace Regorus.Internal
{
    internal static unsafe class ResultHelpers
    {
        internal static string? GetStringResult(RegorusResult result)
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

        internal static bool GetBoolResult(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                return result.data_type == RegorusDataType.Boolean && result.bool_value;
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }

        internal static long GetIntResult(RegorusResult result)
        {
            try
            {
                if (result.status != RegorusStatus.Ok)
                {
                    var message = Utf8Marshaller.FromUtf8(result.error_message);
                    throw result.status.CreateException(message);
                }

                return result.data_type == RegorusDataType.Integer ? result.int_value : 0;
            }
            finally
            {
                API.regorus_result_drop(result);
            }
        }
    }
}
