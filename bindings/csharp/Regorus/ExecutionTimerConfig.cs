// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

namespace Regorus
{
    /// <summary>
    /// Managed representation of the execution timer configuration used by the engine.
    /// </summary>
    public readonly struct ExecutionTimerConfig
    {
        /// <summary>
        /// Initializes a new instance of the <see cref="ExecutionTimerConfig"/> struct.
        /// </summary>
        /// <param name="limit">Maximum wall-clock duration allowed for evaluation. Must be non-negative.</param>
        /// <param name="checkInterval">Number of work units between timer checks. Must be non-zero.</param>
        /// <exception cref="ArgumentOutOfRangeException">Thrown when <paramref name="limit"/> is negative or <paramref name="checkInterval"/> is zero.</exception>
        public ExecutionTimerConfig(TimeSpan limit, uint checkInterval)
        {
            if (limit < TimeSpan.Zero)
            {
                throw new ArgumentOutOfRangeException(nameof(limit), "Execution timer limit must be non-negative.");
            }

            if (checkInterval == 0)
            {
                throw new ArgumentOutOfRangeException(nameof(checkInterval), "Execution timer check interval must be non-zero.");
            }

            Limit = limit;
            CheckInterval = checkInterval;
        }

        /// <summary>
        /// Maximum wall-clock duration allowed for an evaluation.
        /// </summary>
        public TimeSpan Limit { get; }

        /// <summary>
        /// Number of work units between timer checks.
        /// </summary>
        public uint CheckInterval { get; }

        internal Regorus.Internal.RegorusExecutionTimerConfig ToNative()
        {
            if (Limit < TimeSpan.Zero)
            {
                throw new InvalidOperationException("Execution timer limit must be non-negative.");
            }

            ulong ticks = checked((ulong)Limit.Ticks);
            ulong limitNanoseconds = checked(ticks * 100UL);

            return new Regorus.Internal.RegorusExecutionTimerConfig
            {
                limit_ns = limitNanoseconds,
                check_interval = CheckInterval,
            };
        }
    }
}
