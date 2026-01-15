// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

#nullable enable

namespace Regorus.Internal
{
    internal static class StatusExtensions
    {
        internal static Exception CreateException(this RegorusStatus status, string? message)
        {
            var details = string.IsNullOrWhiteSpace(message) ? "Regorus call failed." : message;

            return status switch
            {
                RegorusStatus.Panic => new InvalidOperationException($"Regorus engine panicked: {details}"),
                RegorusStatus.Poisoned => new InvalidOperationException($"Regorus engine is poisoned: {details}"),
                _ => new InvalidOperationException(details),
            };
        }
    }
}
