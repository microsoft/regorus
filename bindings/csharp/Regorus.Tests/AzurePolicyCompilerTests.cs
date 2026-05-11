// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Text.Json.Nodes;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Regorus;

namespace Regorus.Tests;

/// <summary>
/// Tests for <see cref="AzurePolicyCompiler"/> — compiling Azure Policy JSON
/// policyRule and policyDefinition into RVM programs and evaluating them.
/// </summary>
[TestClass]
public class AzurePolicyCompilerTests
{
    // -----------------------------------------------------------------------
    // Test data
    // -----------------------------------------------------------------------

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
                }
            ]
        }]
    }]";

    /// <summary>Simple policy definition that checks the resource type.</summary>
    private const string SimpleAuditDefinition = @"{
        ""policyRule"": {
            ""if"": {
                ""field"": ""type"",
                ""equals"": ""Microsoft.Storage/storageAccounts""
            },
            ""then"": { ""effect"": ""audit"" }
        }
    }";

    /// <summary>Policy definition that uses an alias to check HTTPS-only.</summary>
    private const string HttpsDenyDefinition = @"{
        ""policyRule"": {
            ""if"": {
                ""allOf"": [
                    { ""field"": ""type"", ""equals"": ""Microsoft.Storage/storageAccounts"" },
                    { ""field"": ""Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly"", ""equals"": false }
                ]
            },
            ""then"": { ""effect"": ""deny"" }
        }
    }";

    /// <summary>Full policy definition with parameters.</summary>
    private const string PolicyDefinitionWithParams = @"{
        ""displayName"": ""Require HTTPS for storage accounts"",
        ""policyType"": ""Custom"",
        ""mode"": ""Indexed"",
        ""parameters"": {
            ""effect"": {
                ""type"": ""String"",
                ""defaultValue"": ""deny""
            }
        },
        ""policyRule"": {
            ""if"": {
                ""allOf"": [
                    { ""field"": ""type"", ""equals"": ""Microsoft.Storage/storageAccounts"" },
                    { ""field"": ""Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly"", ""equals"": false }
                ]
            },
            ""then"": { ""effect"": ""[parameters('effect')]"" }
        }
    }";

    // -----------------------------------------------------------------------
    // Helper
    // -----------------------------------------------------------------------

    /// <summary>
    /// Wrap a normalized resource JSON and parameters into the input envelope
    /// expected by compiled Azure Policy RVM programs.
    /// </summary>
    private static string WrapInput(string resourceJson, string parametersJson = "{}")
    {
        return $@"{{""resource"": {resourceJson}, ""parameters"": {parametersJson}}}";
    }

    /// <summary>
    /// Compile a policy definition, load it into an RVM, set input, and execute.
    /// Returns the result string from <c>ExecuteEntryPoint("main")</c>.
    /// </summary>
    private static string? CompileAndEval(
        AliasRegistry? registry,
        string policyDefinitionJson,
        string inputJson)
    {
        using var program = AzurePolicyCompiler.CompilePolicyDefinition(registry, policyDefinitionJson);
        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetInputJson(inputJson);
        return vm.ExecuteEntryPoint("main");
    }

    // -----------------------------------------------------------------------
    // CompilePolicyDefinition tests
    // -----------------------------------------------------------------------

    [TestMethod]
    public void CompilePolicyDefinition_no_aliases_succeeds()
    {
        using var program = AzurePolicyCompiler.CompilePolicyDefinition(null, SimpleAuditDefinition);
        Assert.IsNotNull(program);
    }

    [TestMethod]
    public void CompilePolicyDefinition_with_aliases_succeeds()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        using var program = AzurePolicyCompiler.CompilePolicyDefinition(registry, HttpsDenyDefinition);
        Assert.IsNotNull(program);
    }

    [TestMethod]
    [ExpectedException(typeof(ArgumentNullException))]
    public void CompilePolicyDefinition_null_json_throws()
    {
        AzurePolicyCompiler.CompilePolicyDefinition(null, null!);
    }

    [TestMethod]
    [ExpectedException(typeof(InvalidOperationException))]
    public void CompilePolicyDefinition_invalid_json_throws()
    {
        AzurePolicyCompiler.CompilePolicyDefinition(null, @"{""not"": ""a definition""}");
    }

    // -----------------------------------------------------------------------
    // End-to-end evaluation tests
    // -----------------------------------------------------------------------

    [TestMethod]
    public void Eval_simple_rule_matching_resource_returns_effect()
    {
        var input = WrapInput(
            @"{""type"": ""microsoft.storage/storageaccounts""}");

        var result = CompileAndEval(null, SimpleAuditDefinition, input);
        Assert.IsNotNull(result, "expected a result for matching resource");

        var doc = JsonNode.Parse(result!)!;
        Assert.AreEqual("audit", doc["effect"]?.GetValue<string>(),
            $"expected 'audit' effect, got: {result}");
    }

    [TestMethod]
    public void Eval_simple_rule_non_matching_resource_returns_undefined()
    {
        var input = WrapInput(
            @"{""type"": ""microsoft.compute/virtualmachines""}");

        var result = CompileAndEval(null, SimpleAuditDefinition, input);
        Assert.IsNotNull(result);
        StringAssert.Contains(result!, "undefined",
            "expected undefined for non-matching resource type");
    }

    [TestMethod]
    public void Eval_alias_rule_non_compliant_returns_deny()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        // Non-compliant: HTTPS not enabled (normalized/lowercased form)
        var input = WrapInput(
            @"{""type"": ""microsoft.storage/storageaccounts"", ""supportshttpstrafficonly"": false}");

        using var program = AzurePolicyCompiler.CompilePolicyDefinition(registry, HttpsDenyDefinition);
        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetInputJson(input);

        var result = vm.ExecuteEntryPoint("main");
        Assert.IsNotNull(result);

        var doc = JsonNode.Parse(result!)!;
        Assert.AreEqual("deny", doc["effect"]?.GetValue<string>(),
            $"expected 'deny' for non-compliant resource, got: {result}");
    }

    [TestMethod]
    public void Eval_alias_rule_compliant_returns_undefined()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        // Compliant: HTTPS enabled
        var input = WrapInput(
            @"{""type"": ""microsoft.storage/storageaccounts"", ""supportshttpstrafficonly"": true}");

        using var program = AzurePolicyCompiler.CompilePolicyDefinition(registry, HttpsDenyDefinition);
        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetInputJson(input);

        var result = vm.ExecuteEntryPoint("main");
        Assert.IsNotNull(result);
        StringAssert.Contains(result!, "undefined",
            "expected undefined for compliant resource");
    }

    [TestMethod]
    public void Eval_definition_with_default_parameters()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        using var program = AzurePolicyCompiler.CompilePolicyDefinition(
            registry, PolicyDefinitionWithParams);
        using var vm = new Rvm();
        vm.LoadProgram(program);

        // Non-compliant resource
        var input = WrapInput(
            @"{""type"": ""microsoft.storage/storageaccounts"", ""supportshttpstrafficonly"": false}");
        vm.SetInputJson(input);

        var result = vm.ExecuteEntryPoint("main");
        Assert.IsNotNull(result);

        var doc = JsonNode.Parse(result!)!;
        // Default parameter value is "deny"
        Assert.AreEqual("deny", doc["effect"]?.GetValue<string>(),
            $"expected default 'deny' effect, got: {result}");
    }

    [TestMethod]
    public void Eval_with_normalized_arm_resource_end_to_end()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        // Simulate the full production flow:
        // 1. Start with an ARM resource
        var armResource = @"{
            ""type"": ""Microsoft.Storage/storageAccounts"",
            ""name"": ""mystorage"",
            ""location"": ""eastus"",
            ""properties"": {
                ""supportsHttpsTrafficOnly"": false,
                ""minimumTlsVersion"": ""TLS1_0""
            }
        }";

        // 2. Normalize via AliasRegistry
        var normalizedEnvelope = registry.NormalizeAndWrap(
            armResource,
            apiVersion: null,
            contextJson: "{}",
            parametersJson: "{}");
        Assert.IsNotNull(normalizedEnvelope);

        // 3. Compile the policy rule
        using var program = AzurePolicyCompiler.CompilePolicyDefinition(registry, HttpsDenyDefinition);

        // 4. Execute
        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetInputJson(normalizedEnvelope!);

        var result = vm.ExecuteEntryPoint("main");
        Assert.IsNotNull(result);

        var doc = JsonNode.Parse(result!)!;
        Assert.AreEqual("deny", doc["effect"]?.GetValue<string>(),
            $"expected 'deny' for non-HTTPS storage account, got: {result}");
    }

    [TestMethod]
    public void Eval_normalized_compliant_resource_end_to_end()
    {
        using var registry = new AliasRegistry();
        registry.LoadJson(StorageAliasesJson);

        var armResource = @"{
            ""type"": ""Microsoft.Storage/storageAccounts"",
            ""name"": ""secureastorage"",
            ""location"": ""westus"",
            ""properties"": {
                ""supportsHttpsTrafficOnly"": true,
                ""minimumTlsVersion"": ""TLS1_2""
            }
        }";

        var normalizedEnvelope = registry.NormalizeAndWrap(
            armResource,
            apiVersion: null,
            contextJson: "{}",
            parametersJson: "{}");
        Assert.IsNotNull(normalizedEnvelope);

        using var program = AzurePolicyCompiler.CompilePolicyDefinition(registry, HttpsDenyDefinition);
        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetInputJson(normalizedEnvelope!);

        var result = vm.ExecuteEntryPoint("main");
        Assert.IsNotNull(result);
        StringAssert.Contains(result!, "undefined",
            "expected undefined for compliant HTTPS storage account");
    }

    [TestMethod]
    public void Program_can_be_serialized_and_reloaded()
    {
        using var program = AzurePolicyCompiler.CompilePolicyDefinition(null, SimpleAuditDefinition);

        // Serialize to binary
        var binary = program.SerializeBinary();
        Assert.IsTrue(binary.Length > 0, "serialized program should not be empty");

        // Deserialize and run
        using var restored = Program.DeserializeBinary(binary, out var isPartial);
        Assert.IsFalse(isPartial, "program should not be partial");

        using var vm = new Rvm();
        vm.LoadProgram(restored);
        var input = WrapInput(@"{""type"": ""microsoft.storage/storageaccounts""}");
        vm.SetInputJson(input);

        var result = vm.ExecuteEntryPoint("main");
        Assert.IsNotNull(result);
        var doc = JsonNode.Parse(result!)!;
        Assert.AreEqual("audit", doc["effect"]?.GetValue<string>());
    }

    [TestMethod]
    public void Program_generates_listing()
    {
        using var program = AzurePolicyCompiler.CompilePolicyDefinition(null, SimpleAuditDefinition);
        var listing = program.GenerateListing();
        Assert.IsFalse(string.IsNullOrWhiteSpace(listing),
            "generated listing should not be empty");
    }

    // -----------------------------------------------------------------------
    // Context-dependent policy tests
    // -----------------------------------------------------------------------

    /// Policy definition that uses subscription() context function.
    private const string ContextPolicyDefinition = @"{
        ""policyRule"": {
            ""if"": {
                ""allOf"": [
                    { ""field"": ""type"", ""equals"": ""Microsoft.Storage/storageAccounts"" },
                    { ""value"": ""[subscription().subscriptionId]"", ""equals"": ""sub-123"" }
                ]
            },
            ""then"": { ""effect"": ""deny"" }
        }
    }";

    [TestMethod]
    public void Eval_context_policy_with_set_context_returns_effect()
    {
        using var program = AzurePolicyCompiler.CompilePolicyDefinition(null, ContextPolicyDefinition);
        using var vm = new Rvm();
        vm.LoadProgram(program);

        vm.SetContextJson(@"{""subscription"": {""subscriptionId"": ""sub-123""}}");

        var input = WrapInput(
            @"{""type"": ""microsoft.storage/storageaccounts""}");
        vm.SetInputJson(input);

        var result = vm.ExecuteEntryPoint("main");
        Assert.IsNotNull(result);
        var doc = JsonNode.Parse(result!)!;
        Assert.AreEqual("deny", doc["effect"]?.GetValue<string>(),
            $"expected 'deny' with matching context, got: {result}");
    }

    [TestMethod]
    public void Eval_context_policy_without_context_returns_undefined()
    {
        using var program = AzurePolicyCompiler.CompilePolicyDefinition(null, ContextPolicyDefinition);
        using var vm = new Rvm();
        vm.LoadProgram(program);

        // No context set — subscription() will be undefined
        var input = WrapInput(
            @"{""type"": ""microsoft.storage/storageaccounts""}");
        vm.SetInputJson(input);

        var result = vm.ExecuteEntryPoint("main");
        Assert.IsNotNull(result);
        StringAssert.Contains(result!, "undefined",
            "expected undefined without context set");
    }
}
