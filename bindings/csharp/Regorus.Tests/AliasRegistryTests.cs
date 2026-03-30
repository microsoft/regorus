// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Text.Json;
using System.Text.Json.Nodes;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Regorus;

namespace Regorus.Tests;

[TestClass]
public class AliasRegistryTests
{
    private const string AliasesJson = @"[{
        ""namespace"": ""Microsoft.Storage"",
        ""resourceTypes"": [{
            ""resourceType"": ""storageAccounts"",
            ""aliases"": [{
                ""name"": ""Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly"",
                ""defaultPath"": ""properties.supportsHttpsTrafficOnly"",
                ""paths"": []
            }, {
                ""name"": ""Microsoft.Storage/storageAccounts/accessTier"",
                ""defaultPath"": ""properties.accessTier"",
                ""paths"": []
            }]
        }]
    }]";

    private const string ManifestJson = @"{
        ""dataNamespace"": ""Microsoft.KeyVault.Data"",
        ""aliases"": [],
        ""resourceTypeAliases"": [{
            ""resourceType"": ""vaults/certificates"",
            ""aliases"": [{
                ""name"": ""Microsoft.KeyVault.Data/vaults/certificates/keySize"",
                ""paths"": [{ ""path"": ""keySize"", ""apiVersions"": [""7.0""] }]
            }]
        }]
    }";

    [TestMethod]
    public void Create_and_dispose_succeeds()
    {
        using var registry = new AliasRegistry();
        Assert.AreEqual(0, registry.Length);
    }

    [TestMethod]
    public void LoadJson_populates_registry()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(AliasesJson);
        Assert.AreEqual(1, registry.Length);
    }

    [TestMethod]
    public void LoadManifest_populates_registry()
    {
        using var registry = new AliasRegistry();
        registry.LoadManifest(ManifestJson);
        Assert.AreEqual(1, registry.Length);
    }

    [TestMethod]
    public void NormalizeAndWrap_produces_envelope()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(AliasesJson);

        var resource = @"{
            ""name"": ""acct1"",
            ""type"": ""Microsoft.Storage/storageAccounts"",
            ""properties"": { ""supportsHttpsTrafficOnly"": true, ""accessTier"": ""Hot"" }
        }";

        var result = registry.NormalizeAndWrap(resource, "2023-01-01", "{}", "{}");
        Assert.IsNotNull(result);

        var envelope = JsonNode.Parse(result!)!;
        Assert.IsNotNull(envelope["resource"]);
        Assert.IsNotNull(envelope["parameters"]);
        Assert.IsNotNull(envelope["context"]);

        // Normalized resource should have lowercased alias field names
        var res = envelope["resource"]!;
        Assert.AreEqual(true, res["supportshttpstrafficonly"]?.GetValue<bool>());
        Assert.AreEqual("Hot", res["accesstier"]?.GetValue<string>());
        Assert.AreEqual("acct1", res["name"]?.GetValue<string>());
    }

    [TestMethod]
    public void NormalizeAndWrap_with_context_and_parameters()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(AliasesJson);

        var resource = @"{
            ""name"": ""acct1"",
            ""type"": ""Microsoft.Storage/storageAccounts"",
            ""properties"": { ""supportsHttpsTrafficOnly"": true }
        }";
        var context = @"{""resourceGroup"": {""name"": ""rg1""}}";
        var parameters = @"{""env"": ""prod""}";

        var result = registry.NormalizeAndWrap(resource, "2023-01-01", context, parameters);
        Assert.IsNotNull(result);

        var envelope = JsonNode.Parse(result!)!;
        Assert.AreEqual("rg1", envelope["context"]!["resourceGroup"]!["name"]?.GetValue<string>());
        Assert.AreEqual("prod", envelope["parameters"]!["env"]?.GetValue<string>());
    }

    [TestMethod]
    public void Denormalize_restores_properties()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(AliasesJson);

        var normalized = @"{
            ""name"": ""acct1"",
            ""type"": ""Microsoft.Storage/storageAccounts"",
            ""supportshttpstrafficonly"": true,
            ""accesstier"": ""Hot""
        }";

        var result = registry.Denormalize(normalized, "2023-01-01");
        Assert.IsNotNull(result);

        var arm = JsonNode.Parse(result!)!;
        Assert.AreEqual("acct1", arm["name"]?.GetValue<string>());
        Assert.AreEqual(true, arm["properties"]!["supportsHttpsTrafficOnly"]?.GetValue<bool>());
        Assert.AreEqual("Hot", arm["properties"]!["accessTier"]?.GetValue<string>());
    }

    [TestMethod]
    public void Round_trip_normalize_then_denormalize()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(AliasesJson);

        var resource = @"{
            ""name"": ""acct1"",
            ""type"": ""Microsoft.Storage/storageAccounts"",
            ""properties"": { ""supportsHttpsTrafficOnly"": true, ""accessTier"": ""Hot"" }
        }";

        // Normalize
        var envelopeJson = registry.NormalizeAndWrap(resource, "2023-01-01", "{}", "{}");
        Assert.IsNotNull(envelopeJson);

        var envelope = JsonNode.Parse(envelopeJson!)!;
        var normalizedResource = envelope["resource"]!.ToJsonString();

        // Denormalize
        var armJson = registry.Denormalize(normalizedResource, "2023-01-01");
        Assert.IsNotNull(armJson);

        var arm = JsonNode.Parse(armJson!)!;
        Assert.AreEqual(true, arm["properties"]!["supportsHttpsTrafficOnly"]?.GetValue<bool>());
        Assert.AreEqual("Hot", arm["properties"]!["accessTier"]?.GetValue<string>());
        Assert.AreEqual("acct1", arm["name"]?.GetValue<string>());
    }

    [TestMethod]
    public void DataPlane_manifest_normalize()
    {
        using var registry = new AliasRegistry();
        registry.LoadManifest(ManifestJson);

        var resource = @"{
            ""type"": ""Microsoft.KeyVault.Data/vaults/certificates"",
            ""keySize"": 2048
        }";

        var result = registry.NormalizeAndWrap(resource, "7.0", "{}", "{}");
        Assert.IsNotNull(result);

        var envelope = JsonNode.Parse(result!)!;
        Assert.AreEqual(2048, envelope["resource"]!["keysize"]?.GetValue<int>());
    }

    [TestMethod]
    [ExpectedException(typeof(InvalidOperationException))]
    public void LoadJson_invalid_throws()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson("not valid json");
    }
}
