// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Mutable, single-threaded builder for <see cref="AliasRegistry"/>.
    /// Load alias data, then call <see cref="Build"/> to freeze the registry.
    /// </summary>
    public unsafe sealed class AliasRegistryBuilder : SafeHandleWrapper
    {
        /// <summary>
        /// Create an empty alias registry builder.
        /// </summary>
        public AliasRegistryBuilder()
            : base(RegorusAliasRegistryBuilderHandle.Create(), nameof(AliasRegistryBuilder))
        {
        }

        /// <summary>
        /// Load control-plane alias data (array of ProviderAliases) from a JSON string.
        /// </summary>
        public void LoadJson(string json)
        {
            Utf8Marshaller.WithUtf8(json, jsonPtr =>
            {
                UseHandle(builderPtr =>
                {
                    ResultHelpers.GetStringResult(API.regorus_alias_registry_builder_load_json(
                        (RegorusAliasRegistryBuilder*)builderPtr,
                        (byte*)jsonPtr));
                });
            });
        }

        /// <summary>
        /// Load a data-plane policy manifest from a JSON string.
        /// </summary>
        public void LoadManifest(string json)
        {
            Utf8Marshaller.WithUtf8(json, jsonPtr =>
            {
                UseHandle(builderPtr =>
                {
                    ResultHelpers.GetStringResult(API.regorus_alias_registry_builder_load_manifest(
                        (RegorusAliasRegistryBuilder*)builderPtr,
                        (byte*)jsonPtr));
                });
            });
        }

        /// <summary>
        /// Freeze the builder into an immutable, thread-safe alias registry.
        /// </summary>
        public AliasRegistry Build()
        {
            return UseHandle(builderPtr =>
            {
                var registryPtr = ResultHelpers.GetPointerResult(
                    API.regorus_alias_registry_builder_build((RegorusAliasRegistryBuilder*)builderPtr));
                return new AliasRegistry(RegorusAliasRegistryHandle.FromPointer(registryPtr));
            });
        }
    }
}
