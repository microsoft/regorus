// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

#if REGORUS_EXPERIMENTAL
namespace Regorus.Experimental
#else
namespace Regorus
#endif
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
