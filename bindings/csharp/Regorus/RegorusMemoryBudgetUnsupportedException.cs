// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

namespace Regorus
{
    /// <summary>
    /// Compatibility exception for the reserved native status 11.
    /// </summary>
    public sealed class RegorusMemoryBudgetUnsupportedException : InvalidOperationException
    {
        internal RegorusMemoryBudgetUnsupportedException(string message)
            : base(message)
        {
        }
    }
}
