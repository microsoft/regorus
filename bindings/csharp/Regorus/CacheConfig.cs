// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

namespace Regorus
{
    /// <summary>
    /// Global configuration for compiled pattern caches used by regex and glob builtins.
    /// </summary>
    public readonly struct CacheConfig
    {
        /// <summary>
        /// Initializes a new instance of the <see cref="CacheConfig"/> struct.
        /// </summary>
        /// <param name="regex">Maximum cached compiled regex patterns (default 256, 0 = disabled).</param>
        /// <param name="glob">Maximum cached compiled glob matchers (default 128, 0 = disabled).</param>
        public CacheConfig(nuint regex, nuint glob)
        {
            Regex = regex;
            Glob = glob;
        }

        /// <summary>Maximum cached compiled regex patterns (default 256).</summary>
        public nuint Regex { get; }

        /// <summary>Maximum cached compiled glob matchers (default 128).</summary>
        public nuint Glob { get; }

        internal Regorus.Internal.RegorusCacheConfig ToNative()
        {
            return new Regorus.Internal.RegorusCacheConfig
            {
                regex = Regex,
                glob = Glob,
            };
        }
    }
}
