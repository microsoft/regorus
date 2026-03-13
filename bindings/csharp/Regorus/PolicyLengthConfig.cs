// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

namespace Regorus
{
    /// <summary>
    /// Policy source length limits enforced when loading policy files.
    /// </summary>
    public readonly struct PolicyLengthConfig
    {
        /// <summary>
        /// Initializes a new instance of the <see cref="PolicyLengthConfig"/> struct.
        /// </summary>
        /// <param name="maxCol">Maximum column width per line. Must be non-zero.</param>
        /// <param name="maxFileBytes">Maximum policy file size in bytes. Must be non-zero.</param>
        /// <param name="maxLines">Maximum number of lines per policy file. Must be non-zero.</param>
        /// <exception cref="ArgumentOutOfRangeException">Thrown when any parameter is zero.</exception>
        public PolicyLengthConfig(uint maxCol, nuint maxFileBytes, nuint maxLines)
        {
            if (maxCol == 0)
                throw new ArgumentOutOfRangeException(nameof(maxCol), "Must be non-zero.");
            if (maxFileBytes == 0)
                throw new ArgumentOutOfRangeException(nameof(maxFileBytes), "Must be non-zero.");
            if (maxLines == 0)
                throw new ArgumentOutOfRangeException(nameof(maxLines), "Must be non-zero.");

            MaxCol = maxCol;
            MaxFileBytes = maxFileBytes;
            MaxLines = maxLines;
        }

        /// <summary>Maximum column width per line (default: 1024).</summary>
        public uint MaxCol { get; }

        /// <summary>Maximum policy file size in bytes (default: 1 MiB).</summary>
        public nuint MaxFileBytes { get; }

        /// <summary>Maximum number of lines per policy file (default: 20000).</summary>
        public nuint MaxLines { get; }

        internal Regorus.Internal.RegorusPolicyLengthConfig ToNative()
        {
            return new Regorus.Internal.RegorusPolicyLengthConfig
            {
                max_col = MaxCol,
                max_file_bytes = MaxFileBytes,
                max_lines = MaxLines,
            };
        }
    }
}
