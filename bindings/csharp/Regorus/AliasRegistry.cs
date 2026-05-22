// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Immutable Azure Policy alias registry used for resource normalization
    /// and policy compilation.
    /// </summary>
    public unsafe sealed class AliasRegistry : SafeHandleWrapper
    {
        internal AliasRegistry(RegorusAliasRegistryHandle handle)
            : base(handle, nameof(AliasRegistry))
        {
        }

        /// <summary>
        /// Create an empty immutable alias registry.
        /// </summary>
        public static AliasRegistry Empty()
        {
            using var builder = new AliasRegistryBuilder();
            return builder.Build();
        }

        /// <summary>
        /// Create an immutable alias registry from control-plane alias JSON.
        /// </summary>
        public static AliasRegistry FromJson(string json)
        {
            using var builder = new AliasRegistryBuilder();
            builder.LoadJson(json);
            return builder.Build();
        }

        /// <summary>
        /// Create an immutable alias registry from a data-plane manifest JSON document.
        /// </summary>
        public static AliasRegistry FromManifest(string json)
        {
            using var builder = new AliasRegistryBuilder();
            builder.LoadManifest(json);
            return builder.Build();
        }

        /// <summary>
        /// Gets the number of resource types loaded in the registry.
        /// </summary>
        public long Length
        {
            get
            {
                return UseHandle(regPtr =>
                {
                    return ResultHelpers.GetIntResult(
                        API.regorus_alias_registry_len((RegorusAliasRegistry*)regPtr));
                });
            }
        }

        /// <summary>
        /// Normalize an ARM resource JSON and wrap it into the standard input envelope
        /// expected by a compiled Azure Policy program.
        /// </summary>
        public string? NormalizeAndWrap(string resourceJson, string? apiVersion = null, string contextJson = "{}", string parametersJson = "{}")
        {
            return Utf8Marshaller.WithUtf8(resourceJson, resPtr =>
                Utf8Marshaller.WithUtf8(contextJson, ctxPtr =>
                    Utf8Marshaller.WithUtf8(parametersJson, paramsPtr =>
                    {
                        if (apiVersion is null)
                        {
                            return UseHandle(regPtr =>
                            {
                                return ResultHelpers.GetStringResult(
                                    API.regorus_alias_registry_normalize_and_wrap(
                                        (RegorusAliasRegistry*)regPtr,
                                        (byte*)resPtr, null,
                                        (byte*)ctxPtr, (byte*)paramsPtr));
                            });
                        }

                        return Utf8Marshaller.WithUtf8(apiVersion, apiPtr =>
                            UseHandle(regPtr =>
                            {
                                return ResultHelpers.GetStringResult(
                                    API.regorus_alias_registry_normalize_and_wrap(
                                        (RegorusAliasRegistry*)regPtr,
                                        (byte*)resPtr, (byte*)apiPtr,
                                        (byte*)ctxPtr, (byte*)paramsPtr));
                            }));
                    })));
        }

        /// <summary>
        /// Denormalize a previously-normalized resource JSON back to ARM format.
        /// </summary>
        public string? Denormalize(string normalizedJson, string? apiVersion = null)
        {
            return Utf8Marshaller.WithUtf8(normalizedJson, normPtr =>
            {
                if (apiVersion is null)
                {
                    return UseHandle(regPtr =>
                    {
                        return ResultHelpers.GetStringResult(
                            API.regorus_alias_registry_denormalize(
                                (RegorusAliasRegistry*)regPtr,
                                (byte*)normPtr, null));
                    });
                }

                return Utf8Marshaller.WithUtf8(apiVersion, apiPtr =>
                    UseHandle(regPtr =>
                    {
                        return ResultHelpers.GetStringResult(
                            API.regorus_alias_registry_denormalize(
                                (RegorusAliasRegistry*)regPtr,
                                (byte*)normPtr, (byte*)apiPtr));
                    }));
            });
        }
    }
}
