// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text.Json;
using System.Threading;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Regorus.Tests;

[TestClass]
public sealed class RvmMemoryBudgetTests
{
    public TestContext TestContext { get; set; } = null!;

    private const ulong TightMemoryBudgetBytes = 64 * 1024;

    private const string Policy = """
package limits.memory
import rego.v1

large_array := json.unmarshal(data.large_json)
""";

    private const string EntryPoint = "data.limits.memory.large_array";

    private const string PreloadedResultPolicy = """
package limits.memory

large_string := data.large_string
""";

    private const string PreloadedResultEntryPoint = "data.limits.memory.large_string";

    private const string SuspendableHostAwaitPolicy = """
package limits.memory
import rego.v1

result := count(__builtin_host_await(
  __builtin_host_await(input.value, "first"),
  "second"
))
""";

    private const string SuspendableHostAwaitEntryPoint = "data.limits.memory.result";
    private const ulong SuspendableMemoryBudgetBytes = 768 * 1024;

    private const string NativeModulePolicy = """
package limits.native

result := 1
""";

    private const string NativeModuleEntryPoint = "data.limits.native.result";

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
    public void Serialization_budget_failure_leaves_error_state()
    {
        var data = JsonSerializer.Serialize(new
        {
            large_string = new string('x', 2 * 1024 * 1024),
        });
        var modules = new[] { new PolicyModule("memory_budget.rego", PreloadedResultPolicy) };
        using var program = Program.CompileFromModules(data, modules, new[] { PreloadedResultEntryPoint });
        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetDataJson(data);
        vm.SetMemoryBudgetConfig(new MemoryBudgetConfig(512 * 1024));

        Assert.ThrowsException<RegorusMemoryBudgetExceededException>(
            () => vm.ExecuteEntryPoint(PreloadedResultEntryPoint));

        var state = vm.GetExecutionState();
        Assert.IsNotNull(state);
        StringAssert.Contains(state, "Error { error: MemoryBudgetExceeded");
    }

    [TestMethod]
    public void Suspendable_budget_spans_compiled_host_await_thread_migration()
    {
        var modules = new[] { new PolicyModule("memory_budget.rego", SuspendableHostAwaitPolicy) };
        using var program = Program.CompileFromModules(
            """{"value":"request"}""",
            modules,
            new[] { SuspendableHostAwaitEntryPoint });
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.LoadProgram(program);
        vm.SetInputJson("""{"value":"request"}""");
        vm.SetMemoryBudgetConfig(new MemoryBudgetConfig(SuspendableMemoryBudgetBytes));

        Exception? executeError = null;
        Exception? firstResumeError = null;
        Exception? secondResumeError = null;
        string? finalResult = null;
        using var executeFinished = new ManualResetEventSlim();
        using var firstResumeFinished = new ManualResetEventSlim();

        var executeThread = new Thread(() =>
        {
            try
            {
                vm.Execute();
            }
            catch (Exception ex)
            {
                executeError = ex;
            }
            finally
            {
                executeFinished.Set();
            }
        });

        var firstResumeThread = new Thread(() =>
        {
            try
            {
                if (!executeFinished.Wait(TimeSpan.FromSeconds(30)))
                {
                    throw new TimeoutException("Execute did not finish.");
                }

                vm.Resume("\"first\"");
            }
            catch (Exception ex)
            {
                firstResumeError = ex;
            }
            finally
            {
                firstResumeFinished.Set();
            }
        });

        var secondResumeThread = new Thread(() =>
        {
            try
            {
                if (!firstResumeFinished.Wait(TimeSpan.FromSeconds(30)))
                {
                    throw new TimeoutException("First resume did not finish.");
                }

                finalResult = vm.Resume("\"second\"");
            }
            catch (Exception ex)
            {
                secondResumeError = ex;
            }
        });

        executeThread.Start();
        firstResumeThread.Start();
        secondResumeThread.Start();
        executeThread.Join();
        firstResumeThread.Join();
        secondResumeThread.Join();

        Assert.IsNull(executeError, executeError?.ToString());
        Assert.IsNull(firstResumeError, firstResumeError?.ToString());
        Assert.IsNull(secondResumeError, secondResumeError?.ToString());
        Assert.AreEqual("6", finalResult);
    }

    [TestMethod]
    public void Suspendable_resume_parse_exhaustion_throws_typed_exception()
    {
        var modules = new[] { new PolicyModule("memory_budget.rego", SuspendableHostAwaitPolicy) };
        using var program = Program.CompileFromModules(
            """{"value":"request"}""",
            modules,
            new[] { SuspendableHostAwaitEntryPoint });
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.LoadProgram(program);
        vm.SetInputJson("""{"value":"request"}""");
        vm.SetMemoryBudgetConfig(new MemoryBudgetConfig(SuspendableMemoryBudgetBytes));

        vm.Execute();
        vm.ClearMemoryBudgetConfig();
        vm.SetExecutionMode(ExecutionMode.RunToCompletion);
        vm.Resume(JsonSerializer.Serialize(new string('x', 450 * 1024)));

        Assert.ThrowsException<RegorusMemoryBudgetExceededException>(
            () => vm.Resume(JsonSerializer.Serialize(new string('y', 450 * 1024))));
        StringAssert.Contains(vm.GetExecutionState()!, "Error { error: MemoryBudgetExceeded");
    }

    [TestMethod]
    public void Package_native_module_is_identified_after_native_execution()
    {
        if (!OperatingSystem.IsWindows())
        {
            Assert.Inconclusive("The native module identity assertion requires a Windows DLL.");
            return;
        }

        var modules = new[] { new PolicyModule("native_module.rego", NativeModulePolicy) };
        using var program = Program.CompileFromModules(
            "{}",
            modules,
            new[] { NativeModuleEntryPoint });
        using var vm = new Rvm();
        vm.LoadProgram(program);

        Assert.AreEqual("1", vm.ExecuteEntryPoint(NativeModuleEntryPoint));

        using var process = Process.GetCurrentProcess();
        var nativeModule = process.Modules
            .Cast<ProcessModule>()
            .FirstOrDefault(module =>
                string.Equals(
                    module.ModuleName,
                    "regorus_ffi.dll",
                    StringComparison.OrdinalIgnoreCase));
        Assert.IsNotNull(nativeModule);

        var modulePath = nativeModule!.FileName;
        Assert.IsTrue(Path.IsPathFullyQualified(modulePath), modulePath);
        using var moduleStream = File.OpenRead(modulePath);
        var moduleHash = Convert.ToHexString(SHA256.HashData(moduleStream));
        TestContext.WriteLine($"REGORUS_NATIVE_MODULE_PATH={modulePath}");
        TestContext.WriteLine($"REGORUS_NATIVE_MODULE_SHA256={moduleHash}");
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
