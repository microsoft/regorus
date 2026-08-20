// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

namespace Regorus
{
    /// <summary>
    /// The exception thrown when an RVM memory budget is used with suspendable execution.
    /// </summary>
    public sealed class RegorusMemoryBudgetUnsupportedException : InvalidOperationException
    {
        internal RegorusMemoryBudgetUnsupportedException(string message)
            : base(message)
        {
        }
    }
}
