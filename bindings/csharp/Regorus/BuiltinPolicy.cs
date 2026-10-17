// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
using System.Linq;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Immutable, instance-scoped restrictions on native Rego builtins.
    /// </summary>
    /// <remarks>
    /// Names are validated by the native registry when a policy is compiled or
    /// applied to an RVM. This policy does not constrain unrelated host capabilities.
    /// </remarks>
    public sealed class BuiltinPolicy
    {
        private readonly IReadOnlyList<string> _disabledNames;

        /// <summary>
        /// An allow-all policy.
        /// </summary>
        public static BuiltinPolicy AllowAll { get; } = new(Array.Empty<string>());

        /// <summary>
        /// Gets the normalized, exact native builtin names disabled by this policy.
        /// </summary>
        public IReadOnlyList<string> DisabledNames => _disabledNames;

        /// <summary>
        /// Creates a policy that disables exactly the supplied builtin names.
        /// Duplicate names are normalized using ordinal comparison.
        /// </summary>
        /// <param name="disabledNames">Exact native builtin names to disable.</param>
        /// <exception cref="ArgumentException">
        /// A name is empty, padded, or is not a dotted identifier.
        /// </exception>
        public BuiltinPolicy(IEnumerable<string> disabledNames)
        {
            if (disabledNames is null)
            {
                throw new ArgumentNullException(nameof(disabledNames));
            }

            var normalized = new SortedSet<string>(StringComparer.Ordinal);
            foreach (var name in disabledNames)
            {
                if (!IsValidName(name))
                {
                    throw new ArgumentException(
                        $"Invalid builtin name: '{name}'.",
                        nameof(disabledNames));
                }

                Utf8Marshaller.ThrowIfContainsNul(name, nameof(disabledNames));
                normalized.Add(name);
            }

            _disabledNames = Array.AsReadOnly(normalized.ToArray());
        }

        internal bool IsEmpty => _disabledNames.Count == 0;

        private static bool IsValidName(string? name)
        {
            if (name is null || name.Length == 0 || !string.Equals(name, name.Trim(), StringComparison.Ordinal))
            {
                return false;
            }

            var segmentStart = true;
            foreach (var character in name)
            {
                if (character == '.')
                {
                    if (segmentStart)
                    {
                        return false;
                    }
                    segmentStart = true;
                }
                else if (segmentStart)
                {
                    if (!(IsAsciiLetter(character) || character == '_'))
                    {
                        return false;
                    }
                    segmentStart = false;
                }
                else if (!(IsAsciiLetter(character) || IsAsciiDigit(character) || character == '_'))
                {
                    return false;
                }
            }

            return !segmentStart;
        }

        private static bool IsAsciiLetter(char value) =>
            (value >= 'a' && value <= 'z') || (value >= 'A' && value <= 'Z');

        private static bool IsAsciiDigit(char value) => value >= '0' && value <= '9';
    }

    /// <summary>
    /// Immutable options for compiling an RVM program.
    /// </summary>
    public sealed class CompilerOptions
    {
        private readonly IReadOnlyList<HostAwaitBuiltin> _hostAwaitBuiltins;

        /// <summary>
        /// Gets the builtin restrictions used during compilation.
        /// </summary>
        public BuiltinPolicy BuiltinPolicy { get; }

        /// <summary>
        /// Gets the copied host-awaitable builtin registrations.
        /// </summary>
        public IReadOnlyList<HostAwaitBuiltin> HostAwaitBuiltins => _hostAwaitBuiltins;

        /// <summary>
        /// Creates immutable RVM compiler options.
        /// </summary>
        /// <param name="builtinPolicy">Native builtin restrictions; defaults to allow-all.</param>
        /// <param name="hostAwaitBuiltins">Host-await registrations; defaults to none.</param>
        public CompilerOptions(
            BuiltinPolicy? builtinPolicy = null,
            IEnumerable<HostAwaitBuiltin>? hostAwaitBuiltins = null)
        {
            BuiltinPolicy = builtinPolicy ?? BuiltinPolicy.AllowAll;

            var copiedHostAwaitBuiltins = hostAwaitBuiltins?.ToArray() ?? Array.Empty<HostAwaitBuiltin>();
            for (var index = 0; index < copiedHostAwaitBuiltins.Length; index++)
            {
                var name = copiedHostAwaitBuiltins[index].Name;
                if (name is null)
                {
                    throw new ArgumentException(
                        $"Host-await builtin name at index {index} must not be null.",
                        nameof(hostAwaitBuiltins));
                }
                Utf8Marshaller.ThrowIfContainsNul(name, nameof(hostAwaitBuiltins));
            }

            _hostAwaitBuiltins = Array.AsReadOnly(copiedHostAwaitBuiltins);
        }
    }
}
