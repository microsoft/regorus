// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using Regorus.Internal;

#nullable enable
namespace Regorus
{
    /// <summary>
    /// Manages Azure Policy alias definitions used for resource normalization
    /// and policy compilation.
    /// </summary>
    public unsafe sealed class AliasRegistry : SafeHandleWrapper
    {
        /// <summary>
        /// Create an empty alias registry.
        /// </summary>
        public AliasRegistry()
            : base(RegorusAliasRegistryHandle.Create(), nameof(AliasRegistry))
        {
        }

        /// <summary>
        /// Load control-plane alias data (array of ProviderAliases) from a JSON string.
        /// </summary>
        /// <param name="json">JSON array of ProviderAliases (e.g. from Get-AzPolicyAlias or ResourceTypesAndAliases.json)</param>
        public void LoadJson(string json)
        {
            Utf8Marshaller.WithUtf8(json, jsonPtr =>
            {
                UseHandle(regPtr =>
                {
                    CheckAndDropResult(API.regorus_alias_registry_load_json(
                        (RegorusAliasRegistry*)regPtr, (byte*)jsonPtr));
                    return 0;
                });
            });
        }

        /// <summary>
        /// Load a data-plane policy manifest from a JSON string.
        /// </summary>
        /// <param name="json">JSON object containing a DataPolicyManifest</param>
        public void LoadManifest(string json)
        {
            Utf8Marshaller.WithUtf8(json, jsonPtr =>
            {
                UseHandle(regPtr =>
                {
                    CheckAndDropResult(API.regorus_alias_registry_load_manifest(
                        (RegorusAliasRegistry*)regPtr, (byte*)jsonPtr));
                    return 0;
                });
            });
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
        /// <param name="resourceJson">Raw ARM resource JSON</param>
        /// <param name="apiVersion">API version string (e.g. "2023-01-01"), or null to use default alias paths</param>
        /// <param name="contextJson">Additional context JSON object (pass "{}" if none)</param>
        /// <param name="parametersJson">Policy parameter values JSON (pass "{}" if none)</param>
        /// <returns>JSON string: { "resource": &lt;normalized&gt;, "context": &lt;context&gt;, "parameters": &lt;params&gt; }</returns>
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
                        else
                        {
                            return Utf8Marshaller.WithUtf8(apiVersion, apiPtr =>
                                UseHandle(regPtr =>
                                {
                                    return ResultHelpers.GetStringResult(
                                        API.regorus_alias_registry_normalize_and_wrap(
                                            (RegorusAliasRegistry*)regPtr,
                                            (byte*)resPtr, (byte*)apiPtr,
                                            (byte*)ctxPtr, (byte*)paramsPtr));
                                }));
                        }
                    })));
        }

        /// <summary>
        /// Denormalize a previously-normalized resource JSON back to ARM format.
        /// </summary>
        /// <param name="normalizedJson">The normalized resource JSON</param>
        /// <param name="apiVersion">API version string, or null to use default alias paths</param>
        /// <returns>Denormalized ARM JSON string</returns>
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
                else
                {
                    return Utf8Marshaller.WithUtf8(apiVersion, apiPtr =>
                        UseHandle(regPtr =>
                        {
                            return ResultHelpers.GetStringResult(
                                API.regorus_alias_registry_denormalize(
                                    (RegorusAliasRegistry*)regPtr,
                                    (byte*)normPtr, (byte*)apiPtr));
                        }));
                }
            });
        }

        private static string? CheckAndDropResult(RegorusResult result)
        {
            return ResultHelpers.GetStringResult(result);
        }
    }
}
