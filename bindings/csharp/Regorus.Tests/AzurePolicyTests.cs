// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.IO;
using System.Text.Json;
using System.Text.Json.Nodes;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Regorus;

namespace Regorus.Tests;

/// <summary>
/// Tests for Azure Policy alias normalization and denormalization
/// using the AliasRegistry exposed through the C# bindings.
/// </summary>
[TestClass]
public class AzurePolicyTests
{
    /// <summary>
    /// Sample alias definitions for Microsoft.Storage provider.
    /// These mirror a subset of the test aliases used by the Rust test suite.
    /// </summary>
    private const string StorageAliasesJson = @"[{
        ""namespace"": ""Microsoft.Storage"",
        ""resourceTypes"": [{
            ""resourceType"": ""storageAccounts"",
            ""capabilities"": ""SupportsTags, SupportsLocation"",
            ""aliases"": [
                {
                    ""name"": ""Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly"",
                    ""defaultPath"": ""properties.supportsHttpsTrafficOnly"",
                    ""paths"": []
                },
                {
                    ""name"": ""Microsoft.Storage/storageAccounts/minimumTlsVersion"",
                    ""defaultPath"": ""properties.minimumTlsVersion"",
                    ""paths"": []
                },
                {
                    ""name"": ""Microsoft.Storage/storageAccounts/allowBlobPublicAccess"",
                    ""defaultPath"": ""properties.allowBlobPublicAccess"",
                    ""paths"": []
                }
            ]
        }]
    }]";

    /// <summary>
    /// ARM resource in its original shape (with properties wrapper).
    /// </summary>
    private const string StorageResourceJson = @"{
        ""type"": ""Microsoft.Storage/storageAccounts"",
        ""name"": ""mystorage"",
        ""location"": ""eastus"",
        ""properties"": {
            ""supportsHttpsTrafficOnly"": true,
            ""minimumTlsVersion"": ""TLS1_2"",
            ""allowBlobPublicAccess"": false
        }
    }";

    [TestMethod]
    public void AliasRegistry_NormalizeAndWrap_produces_input_envelope()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        var result = registry.NormalizeAndWrap(
            StorageResourceJson,
            apiVersion: null,
            contextJson: "{}",
            parametersJson: "{}");

        Assert.IsNotNull(result, "NormalizeAndWrap should return a non-null string");

        // The result should be valid JSON with resource, parameters, and context keys.
        var doc = JsonNode.Parse(result);
        Assert.IsNotNull(doc);
        Assert.IsNotNull(doc["resource"], "envelope must contain 'resource'");
        Assert.IsNotNull(doc["parameters"], "envelope must contain 'parameters'");
    }

    [TestMethod]
    public void AliasRegistry_NormalizeAndWrap_flattens_properties()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        var result = registry.NormalizeAndWrap(StorageResourceJson);
        Assert.IsNotNull(result);

        var doc = JsonNode.Parse(result);
        var resource = doc!["resource"];
        Assert.IsNotNull(resource);

        // After normalization, alias-mapped properties should be
        // available at the top level of the resource (lowercased).
        // The normalizer flattens "properties.supportsHttpsTrafficOnly"
        // to "supportshttpstrafficonly" at the resource root.
        var httpsOnly = resource["supportshttpstrafficonly"];
        Assert.IsNotNull(httpsOnly,
            "normalized resource should have 'supportshttpstrafficonly' at top level");
        Assert.AreEqual(true, httpsOnly!.GetValue<bool>());
    }

    [TestMethod]
    public void AliasRegistry_NormalizeAndWrap_preserves_type_field()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        var result = registry.NormalizeAndWrap(StorageResourceJson);
        var doc = JsonNode.Parse(result!);
        var resource = doc!["resource"];

        // The "type" field should be preserved (lowercased key).
        var typeField = resource!["type"];
        Assert.IsNotNull(typeField, "normalized resource should have 'type'");
        Assert.AreEqual(
            "microsoft.storage/storageaccounts",
            typeField!.GetValue<string>().ToLowerInvariant());
    }

    [TestMethod]
    public void AliasRegistry_NormalizeAndWrap_includes_parameters()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        var parametersJson = @"{ ""effect"": ""Deny"" }";
        var result = registry.NormalizeAndWrap(
            StorageResourceJson,
            parametersJson: parametersJson);
        Assert.IsNotNull(result);

        var doc = JsonNode.Parse(result!);
        var parameters = doc!["parameters"];
        Assert.IsNotNull(parameters);
        Assert.AreEqual("Deny", parameters!["effect"]!.GetValue<string>());
    }

    [TestMethod]
    public void AliasRegistry_Denormalize_roundtrips_correctly()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        // Normalize the ARM resource.
        var envelope = registry.NormalizeAndWrap(StorageResourceJson);
        Assert.IsNotNull(envelope);

        // Extract just the normalized resource from the envelope.
        var doc = JsonNode.Parse(envelope!);
        var normalizedResource = doc!["resource"]!.ToJsonString();

        // Denormalize back to ARM shape.
        var denormalized = registry.Denormalize(normalizedResource);
        Assert.IsNotNull(denormalized, "Denormalize should return a non-null string");

        // The denormalized result should have a "properties" wrapper again.
        var denormDoc = JsonNode.Parse(denormalized!);
        Assert.IsNotNull(denormDoc);
        var props = denormDoc!["properties"];
        Assert.IsNotNull(props, "denormalized resource should have 'properties'");
    }

    [TestMethod]
    public void AliasRegistry_loads_test_aliases_file()
    {
        // Load the same aliases file used by the Rust test suite.
        var aliasesPath = Path.Combine("tests", "azure_policy", "aliases", "test_aliases.json");
        if (!File.Exists(aliasesPath))
        {
            Assert.Inconclusive($"Test aliases file not found at {aliasesPath}");
            return;
        }

        var aliasesJson = File.ReadAllText(aliasesPath);
        using var registry = new AliasRegistry();
        registry.LoadJson(aliasesJson);

        // The test_aliases.json file contains multiple providers.
        Assert.IsTrue(registry.Length > 0,
            "registry should have loaded at least one resource type");
    }
}
