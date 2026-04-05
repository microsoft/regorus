// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System.Text.Json;
using System.Text.Json.Nodes;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Regorus.Tests;

[TestClass]
public sealed class AssumptionTests
{
    private const string SimplePolicy = """
        package test
        default allow = false
        allow if { input.role == "admin" }
        """;

    private const string AliasPolicy = """
        package test
        default allow = false

        role := input.identity.role
        expected_role := "release-admin"

        allow if {
            er := expected_role
            role == er
        }
        """;

    [TestMethod]
    public void Rvm_assumptions_populated_for_simple_policy()
    {
        using var engine = new Engine();
        engine.AddPolicy("test.rego", SimplePolicy);

        var entryPoints = new[] { "data.test.allow" };
        using var program = Program.CompileFromEngine(engine, entryPoints);

        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetExplanationSettings(
            enabled: true,
            valueMode: ExplanationValueMode.Full,
            conditionMode: ExplanationConditionMode.AllContributing,
            detail: ExplanationDetail.Full,
            assumeUnknownInput: true);

        vm.SetInputJson("{}");
        var result = vm.ExecuteEntryPoint("data.test.allow");
        Assert.AreEqual("true", result);

        var reportJson = vm.TakeCausalityReport();
        Assert.IsNotNull(reportJson, "RVM causality report should not be null");

        var report = JsonNode.Parse(reportJson!)!;

        var assumptions = report["assumptions"]?.AsArray();
        Assert.IsNotNull(assumptions, "assumptions should be present");
        Assert.IsTrue(assumptions!.Count > 0, "assumptions should not be empty");

        var first = assumptions[0]!;
        Assert.AreEqual("input.role", (string?)first["input_path"]);
        Assert.AreEqual("==", (string?)first["operator"]);
        Assert.AreEqual("admin", (string?)first["assumed_value"]);
    }

    [TestMethod]
    public void Rvm_assumptions_follow_aliases()
    {
        using var engine = new Engine();
        engine.AddPolicy("test.rego", AliasPolicy);

        var entryPoints = new[] { "data.test.allow" };
        using var program = Program.CompileFromEngine(engine, entryPoints);

        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetExplanationSettings(
            enabled: true,
            valueMode: ExplanationValueMode.Full,
            conditionMode: ExplanationConditionMode.AllContributing,
            detail: ExplanationDetail.Full,
            assumeUnknownInput: true);

        vm.SetInputJson("""{"identity": {"name": "alex"}}""");
        var result = vm.ExecuteEntryPoint("data.test.allow");
        Assert.AreEqual("true", result);

        var reportJson = vm.TakeCausalityReport();
        Assert.IsNotNull(reportJson);

        var report = JsonNode.Parse(reportJson!)!;
        var assumptions = report["assumptions"]?.AsArray();
        Assert.IsNotNull(assumptions);
        Assert.IsTrue(assumptions!.Count > 0, "assumptions should not be empty");

        Assert.AreEqual("input.identity.role", (string?)assumptions[0]!["input_path"]);
        Assert.AreEqual("==", (string?)assumptions[0]!["operator"]);
        Assert.AreEqual("release-admin", (string?)assumptions[0]!["assumed_value"]);
    }

    [TestMethod]
    public void Rvm_loop_witness_populated()
    {
        const string loopPolicy = """
            package test
            default allow = false
            allow if {
                n := input.values[_]
                n > 1
                n < 3
            }
            """;

        using var engine = new Engine();
        engine.AddPolicy("test.rego", loopPolicy);

        var entryPoints = new[] { "data.test.allow" };
        using var program = Program.CompileFromEngine(engine, entryPoints);

        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetExplanationSettings(
            enabled: true,
            valueMode: ExplanationValueMode.Full,
            conditionMode: ExplanationConditionMode.AllContributing,
            detail: ExplanationDetail.Standard);

        vm.SetInputJson("""{"values": [0, 2, 4]}""");
        var result = vm.ExecuteEntryPoint("data.test.allow");
        Assert.AreEqual("true", result);

        var reportJson = vm.TakeCausalityReport();
        Assert.IsNotNull(reportJson);

        var report = JsonNode.Parse(reportJson!)!;
        var rules = report["rules"]?.AsArray();
        Assert.IsNotNull(rules);
        Assert.IsTrue(rules!.Count > 0);

        // Find a condition with a witness
        bool foundWitness = false;
        foreach (var rule in rules)
        {
            var definitions = rule?["definitions"]?.AsArray();
            if (definitions == null) continue;
            foreach (var def in definitions)
            {
                var conditions = def?["conditions"]?.AsArray();
                if (conditions == null) continue;
                foreach (var cond in conditions)
                {
                    var witness = cond?["witness"];
                    if (witness != null && witness.GetValueKind() == JsonValueKind.Object)
                    {
                        foundWitness = true;
                        Assert.IsNotNull(witness["total_iterations"],
                            "witness should have total_iterations");
                        Assert.IsNotNull(witness["success_count"],
                            "witness should have success_count");
                        var total = (int?)witness["total_iterations"];
                        Assert.IsTrue(total > 0,
                            $"total_iterations should be > 0, got {total}");
                    }
                }
            }
        }

        Assert.IsTrue(foundWitness,
            $"expected at least one condition with a loop witness.\nReport:\n{reportJson}");
    }
}
