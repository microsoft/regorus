// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

namespace Regorus
{
    /// <summary>
    /// Configures the additional live-memory budget for one RVM execution.
    /// </summary>
    public readonly struct MemoryBudgetConfig
    {
        /// <summary>
        /// Initializes a new instance of the <see cref="MemoryBudgetConfig"/> struct.
        /// </summary>
        /// <param name="limitBytes">Maximum additional live bytes allowed during one execution.</param>
        /// <exception cref="ArgumentOutOfRangeException">Thrown when <paramref name="limitBytes"/> is zero.</exception>
        public MemoryBudgetConfig(ulong limitBytes)
        {
            if (limitBytes == 0)
            {
                throw new ArgumentOutOfRangeException(nameof(limitBytes), "Memory budget must be non-zero.");
            }

            LimitBytes = limitBytes;
        }

        /// <summary>
        /// Gets the maximum additional live bytes allowed during one execution.
        /// </summary>
        public ulong LimitBytes { get; }

        internal Regorus.Internal.RegorusMemoryBudgetConfig ToNative()
        {
            if (LimitBytes == 0)
            {
                throw new InvalidOperationException("Memory budget must be non-zero.");
            }

            return new Regorus.Internal.RegorusMemoryBudgetConfig
            {
                limit_bytes = LimitBytes,
            };
        }
    }
}
