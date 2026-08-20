// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Linq;
using System.Text.Json;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Regorus.Tests;

[TestClass]
public sealed class RvmMemoryBudgetTests
{
    private const ulong TightMemoryBudgetBytes = 64 * 1024;

    private const string Policy = """
package limits.memory
import rego.v1

large_array := json.unmarshal(data.large_json)
""";

    private const string EntryPoint = "data.limits.memory.large_array";

    [TestMethod]
    public void Memory_budget_must_be_non_zero()
    {
        Assert.ThrowsException<ArgumentOutOfRangeException>(() => new MemoryBudgetConfig(0));

        using var vm = new Rvm();
        Assert.ThrowsException<ArgumentOutOfRangeException>(() => vm.SetMemoryBudgetConfig(default));
    }

    [TestMethod]
    public void Execute_exceeding_memory_budget_throws_typed_exception()
    {
        using var program = CreateProgram();
        using var vm = CreateRvm(program);
        vm.SetMemoryBudgetConfig(new MemoryBudgetConfig(TightMemoryBudgetBytes));

        Assert.ThrowsException<RegorusMemoryBudgetExceededException>(() => vm.ExecuteEntryPoint(EntryPoint));
    }

    [TestMethod]
    public void Clearing_memory_budget_restores_unlimited_execution()
    {
        using var program = CreateProgram();
        using var vm = CreateRvm(program);
        vm.SetMemoryBudgetConfig(new MemoryBudgetConfig(TightMemoryBudgetBytes));
        Assert.ThrowsException<RegorusMemoryBudgetExceededException>(() => vm.ExecuteEntryPoint(EntryPoint));

        vm.ClearMemoryBudgetConfig();

        var result = vm.ExecuteEntryPoint(EntryPoint);
        Assert.IsFalse(string.IsNullOrWhiteSpace(result));
    }

    [TestMethod]
    public void Suspendable_execution_rejects_memory_budget()
    {
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.SetMemoryBudgetConfig(new MemoryBudgetConfig(1024));

        Assert.ThrowsException<RegorusMemoryBudgetUnsupportedException>(() => vm.Execute());
    }

    private static Program CreateProgram()
    {
        var modules = new[] { new PolicyModule("memory_budget.rego", Policy) };
        return Program.CompileFromModules(CreateData(), modules, new[] { EntryPoint });
    }

    private static Rvm CreateRvm(Program program)
    {
        var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetDataJson(CreateData());
        return vm;
    }

    private static string CreateData()
    {
        var values = Enumerable.Range(0, 200_000).ToArray();
        return JsonSerializer.Serialize(new
        {
            large_json = JsonSerializer.Serialize(values),
        });
    }
}
