// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

namespace Regorus
{
    /// <summary>
    /// Configures the additional memory budget for one RVM execution.
    /// </summary>
    public readonly struct MemoryBudgetConfig
    {
        /// <summary>
        /// Initializes a new instance of the <see cref="MemoryBudgetConfig"/> struct.
        /// </summary>
        /// <param name="limitBytes">
        /// Maximum additional bytes charged during one execution. Suspendable runs
        /// count successful allocation requests cumulatively; run-to-completion
        /// runs retain live-byte accounting.
        /// </param>
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
        /// Gets the maximum additional bytes charged during one execution.
        /// Suspendable runs count successful allocation requests cumulatively;
        /// run-to-completion runs retain live-byte accounting.
        /// </summary>
        public ulong LimitBytes { get; }

        internal Regorus.Internal.RegorusMemoryBudgetConfig ToNative()
        {
            if (LimitBytes == 0)
            {
                throw new ArgumentOutOfRangeException(nameof(LimitBytes), "Memory budget must be non-zero.");
            }

            return new Regorus.Internal.RegorusMemoryBudgetConfig
            {
                limit_bytes = LimitBytes,
            };
        }
    }
}
