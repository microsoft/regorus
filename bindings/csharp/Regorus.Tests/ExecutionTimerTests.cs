// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Linq;
using System.Text.Json;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Regorus;

namespace Regorus.Tests;

[DoNotParallelize] // Uses global fallback config; must run sequentially.
[TestClass]
public class ExecutionTimerTests
{
    private const string Policy = @"
package limits.timer
import rego.v1

triplet_count := count([1 |
  x := data.values[_]
  y := data.values[_]
  z := data.values[_]
])
";

    private const string Query = "data.limits.timer.triplet_count";
    private const int ValueCount = 160;

    [TestMethod]
    public void Engine_limit_enforced()
    {
        Engine.ClearFallbackExecutionTimerConfig();
        using var engine = CreateEngine(ValueCount);
        var config = new ExecutionTimerConfig(TimeSpan.FromMilliseconds(2), checkInterval: 1);
        engine.SetExecutionTimerConfig(config);

        var ex = Assert.ThrowsException<InvalidOperationException>(() => engine.EvalRule(Query));
        StringAssert.Contains(ex.Message, "execution exceeded time limit");
    }

    [TestMethod]
    public void Fallback_applies_to_new_engines()
    {
        var fallback = new ExecutionTimerConfig(TimeSpan.FromMilliseconds(2), checkInterval: 1);
        Engine.SetFallbackExecutionTimerConfig(fallback);
        try
        {
            using var engine = CreateEngine(ValueCount);
            var ex = Assert.ThrowsException<InvalidOperationException>(() => engine.EvalRule(Query));
            StringAssert.Contains(ex.Message, "execution exceeded time limit");
        }
        finally
        {
            Engine.ClearFallbackExecutionTimerConfig();
        }
    }

    [TestMethod]
    public void Engine_override_relaxes_fallback()
    {
        var fallback = new ExecutionTimerConfig(TimeSpan.FromMilliseconds(2), checkInterval: 1);
        Engine.SetFallbackExecutionTimerConfig(fallback);
        try
        {
            using var engine = CreateEngine(ValueCount);
            var relaxed = new ExecutionTimerConfig(TimeSpan.FromSeconds(12), checkInterval: 1);
            engine.SetExecutionTimerConfig(relaxed);

            var resultJson = engine.EvalRule(Query);
            var result = JsonSerializer.Deserialize<int>(resultJson!);
            Assert.IsTrue(result > 0, "Expected a positive triplet count when limit is relaxed.");

            engine.ClearExecutionTimerConfig();
            var ex = Assert.ThrowsException<InvalidOperationException>(() => engine.EvalRule(Query));
            StringAssert.Contains(ex.Message, "execution exceeded time limit");
        }
        finally
        {
            Engine.ClearFallbackExecutionTimerConfig();
        }
    }

    [TestMethod]
    public void CompiledPolicy_limit_enforced()
    {
        var fallback = new ExecutionTimerConfig(TimeSpan.FromMilliseconds(2), checkInterval: 1);
        Engine.SetFallbackExecutionTimerConfig(fallback);
        try
        {
            using var policy = CreateCompiledPolicy(ValueCount);
            var ex = Assert.ThrowsException<InvalidOperationException>(() => policy.EvalWithInput("null"));
            StringAssert.Contains(ex.Message, "execution exceeded time limit");
        }
        finally
        {
            Engine.ClearFallbackExecutionTimerConfig();
        }
    }

    [TestMethod]
    public void CompiledPolicy_uses_engine_limits_only()
    {
        // Compiled policies no longer store per-policy execution timers; limits are managed by Engine.
        Engine.ClearFallbackExecutionTimerConfig();
        using var policy = CreateCompiledPolicy(ValueCount);
        var resultJson = policy.EvalWithInput("null");
        var result = JsonSerializer.Deserialize<int>(resultJson!);
        Assert.IsTrue(result > 0, "CompiledPolicy should evaluate using engine defaults without its own timer");
    }

    private static Engine CreateEngine(int valueCount)
    {
        var engine = new Engine();
        engine.AddPolicy("limits_timer.rego", Policy);
        engine.AddDataJson(CreateData(valueCount));
        return engine;
    }

    private static CompiledPolicy CreateCompiledPolicy(int valueCount)
    {
        var modules = new[] { new PolicyModule("limits_timer.rego", Policy) };
        return Compiler.CompilePolicyWithEntrypoint(CreateData(valueCount), modules, Query);
    }

    private static string CreateData(int valueCount)
    {
        var payload = new { values = Enumerable.Range(0, valueCount).ToArray() };
        return JsonSerializer.Serialize(payload);
    }
}
