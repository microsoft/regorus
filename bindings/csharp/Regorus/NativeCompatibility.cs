// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;

namespace Regorus.Internal
{
    internal static class NativeCompatibility
    {
        internal static NotSupportedException BuiltinPolicyUnsupported(EntryPointNotFoundException error) =>
            new(
                "The loaded Regorus native library does not support builtin policies. Upgrade the native library.",
                error);
    }
}
