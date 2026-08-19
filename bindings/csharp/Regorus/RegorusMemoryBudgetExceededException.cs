// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

namespace Regorus
{
    /// <summary>
    /// The exception thrown when an RVM execution exceeds its configured memory budget.
    /// </summary>
    public sealed class RegorusMemoryBudgetExceededException : InvalidOperationException
    {
        internal RegorusMemoryBudgetExceededException(string message)
            : base(message)
        {
        }
    }
}
