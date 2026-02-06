// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Diagnostics;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Regorus;

namespace Regorus.Tests;

[TestClass]
[DoNotParallelize]
public class MemoryGrowthTests
{
    private static int Iterations =>
        int.TryParse(Environment.GetEnvironmentVariable("REGORUS_MEMORY_TEST_ITERS"), out var value) ? value : 50_000;

    private static int LogEvery =>
        int.TryParse(Environment.GetEnvironmentVariable("REGORUS_MEMORY_TEST_LOG_EVERY"), out var value) ? value : 500;

    private static int GcEvery
    {
        get
        {
            if (!int.TryParse(Environment.GetEnvironmentVariable("REGORUS_MEMORY_TEST_GC_EVERY"), out var value))
            {
                value = LogEvery;
            }

            return value <= 0 ? LogEvery : value;
        }
    }

    private static long? MaxWorkingSetDeltaBytes
    {
        get
        {
            if (!long.TryParse(Environment.GetEnvironmentVariable("REGORUS_MEMORY_TEST_MAX_DELTA_MB"), out var mb))
            {
                mb = 32;
            }

            if (mb <= 0)
            {
                return null;
            }

            return mb * 1024L * 1024L;
        }
    }

    private static ulong? GlobalRegorusMemoryLimitBytes
    {
        get
        {
            if (!ulong.TryParse(Environment.GetEnvironmentVariable("REGORUS_MEMORY_TEST_GLOBAL_REGORUS_LIMIT_MB"), out var mb))
            {
                return null;
            }

            if (mb == 0)
            {
                return null;
            }

            return mb * 1024UL * 1024UL;
        }
    }

    private static void WithOptionalGlobalRegorusMemoryLimit(Action action)
    {
        var priorLimit = MemoryLimits.GetGlobalMemoryLimit();
        try
        {
            if (GlobalRegorusMemoryLimitBytes is { } limit)
            {
                MemoryLimits.SetGlobalMemoryLimit(limit);
            }

            action();
        }
        finally
        {
            MemoryLimits.SetGlobalMemoryLimit(priorLimit);
        }
    }

    private static void ForceFullGc()
    {
        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
    }


    [TestMethod]
    public void Engine_create_eval_dispose_does_not_grow_working_set()
    {
        WithOptionalGlobalRegorusMemoryLimit(() =>
        {
            var process = Process.GetCurrentProcess();
            process.Refresh();
            var baseline = process.WorkingSet64;
            var maxDelta = 0L;
            var baselineManaged = GC.GetTotalMemory(false);
            var maxManagedDelta = 0L;

            for (var i = 1; i <= Iterations; i++)
            {
                using (var engine = new Engine())
                {
                    engine.AddPolicy("test.rego", "package test\nx = 1\nmessage = `Hello`");
                    _ = engine.EvalRule("data.test.message");
                }

                if (i % LogEvery == 0)
                {
                    process.Refresh();
                    var workingSet = process.WorkingSet64;
                    var managed = GC.GetTotalMemory(false);
                    var delta = workingSet - baseline;
                    var managedDelta = managed - baselineManaged;
                    if (delta > maxDelta)
                    {
                        maxDelta = delta;
                    }
                    if (managedDelta > maxManagedDelta)
                    {
                        maxManagedDelta = managedDelta;
                    }
                    Console.WriteLine($"\n\n\u001b[1m{i} ws_mb={workingSet / 1048576.0:F1} managed_mb={managed / 1048576.0:F1} delta_mb={delta / 1048576.0:F1}\u001b[0m\n\n");
                }
            }

            if (MaxWorkingSetDeltaBytes is { } limit)
            {
                Console.WriteLine($"\n\n\u001b[1mSUMMARY: max ws delta {maxDelta / 1048576.0:F1} MB (limit {limit / 1048576.0:F1} MB); max managed delta {maxManagedDelta / 1048576.0:F1} MB.\u001b[0m\n\n");
                Assert.IsTrue(
                    maxDelta <= limit,
                    $"Working set grew by {maxDelta / 1048576.0:F1} MB (limit {limit / 1048576.0:F1} MB). Managed heap max delta {maxManagedDelta / 1048576.0:F1} MB.");
            }
        });
    }

    [TestMethod]
    public void Engine_create_eval_finalize_does_not_grow_working_set()
    {
        WithOptionalGlobalRegorusMemoryLimit(() =>
        {
            var process = Process.GetCurrentProcess();
            process.Refresh();
            var baseline = process.WorkingSet64;
            var maxDelta = 0L;
            var baselineManaged = GC.GetTotalMemory(false);
            var maxManagedDelta = 0L;

            for (var i = 1; i <= Iterations; i++)
            {
                var engine = new Engine();
                engine.AddPolicy("test.rego", "package test\nx = 1\nmessage = `Hello`");
                _ = engine.EvalRule("data.test.message");

                if (i % GcEvery == 0)
                {
                    ForceFullGc();
                }

                if (i % LogEvery == 0)
                {
                    process.Refresh();
                    var workingSet = process.WorkingSet64;
                    var managed = GC.GetTotalMemory(false);
                    var delta = workingSet - baseline;
                    var managedDelta = managed - baselineManaged;
                    if (delta > maxDelta)
                    {
                        maxDelta = delta;
                    }
                    if (managedDelta > maxManagedDelta)
                    {
                        maxManagedDelta = managedDelta;
                    }
                    Console.WriteLine($"\n\n\u001b[1m{i} ws_mb={workingSet / 1048576.0:F1} managed_mb={managed / 1048576.0:F1} delta_mb={delta / 1048576.0:F1}\u001b[0m\n\n");
                }
            }

            if (MaxWorkingSetDeltaBytes is { } limit)
            {
                Console.WriteLine($"\n\n\u001b[1mSUMMARY: max ws delta {maxDelta / 1048576.0:F1} MB (limit {limit / 1048576.0:F1} MB); max managed delta {maxManagedDelta / 1048576.0:F1} MB.\u001b[0m\n\n");
                Assert.IsTrue(
                    maxDelta <= limit,
                    $"Working set grew by {maxDelta / 1048576.0:F1} MB (limit {limit / 1048576.0:F1} MB). Managed heap max delta {maxManagedDelta / 1048576.0:F1} MB.");
            }
        });
    }


    [TestMethod]
    public void Rvm_rehydrate_execute_dispose_does_not_grow_working_set()
    {
        WithOptionalGlobalRegorusMemoryLimit(() =>
        {
            var modules = new[]
            {
                new PolicyModule("test.rego", "package test\nallow = true"),
            };

            using var compiled = Program.CompileFromModules("{}", modules, new[] { "data.test.allow" });
            var serialized = compiled.SerializeBinary();

            var process = Process.GetCurrentProcess();
            process.Refresh();
            var baseline = process.WorkingSet64;
            var maxDelta = 0L;
            var baselineManaged = GC.GetTotalMemory(false);
            var maxManagedDelta = 0L;

            for (var i = 1; i <= Iterations; i++)
            {
                using (var vm = new Rvm())
                using (var program = Program.DeserializeBinary(serialized, out _))
                {
                    vm.LoadProgram(program);
                    vm.SetDataJson("{}");
                    vm.SetInputJson("{}");
                    _ = vm.ExecuteEntryPoint(0);
                }

                if (i % LogEvery == 0)
                {
                    process.Refresh();
                    var workingSet = process.WorkingSet64;
                    var managed = GC.GetTotalMemory(false);
                    var delta = workingSet - baseline;
                    var managedDelta = managed - baselineManaged;
                    if (delta > maxDelta)
                    {
                        maxDelta = delta;
                    }
                    if (managedDelta > maxManagedDelta)
                    {
                        maxManagedDelta = managedDelta;
                    }
                    Console.WriteLine($"\n\n\u001b[1m{i} ws_mb={workingSet / 1048576.0:F1} managed_mb={managed / 1048576.0:F1} delta_mb={delta / 1048576.0:F1}\u001b[0m\n\n");
                }
            }

            if (MaxWorkingSetDeltaBytes is { } limit)
            {
                Console.WriteLine($"\n\n\u001b[1mSUMMARY: max ws delta {maxDelta / 1048576.0:F1} MB (limit {limit / 1048576.0:F1} MB); max managed delta {maxManagedDelta / 1048576.0:F1} MB.\u001b[0m\n\n");
                Assert.IsTrue(
                    maxDelta <= limit,
                    $"Working set grew by {maxDelta / 1048576.0:F1} MB (limit {limit / 1048576.0:F1} MB). Managed heap max delta {maxManagedDelta / 1048576.0:F1} MB.");
            }
        });
    }

    [TestMethod]
    public void Rvm_rehydrate_execute_finalize_does_not_grow_working_set()
    {
        WithOptionalGlobalRegorusMemoryLimit(() =>
        {
            var modules = new[]
            {
                new PolicyModule("test.rego", "package test\nallow = true"),
            };

            using var compiled = Program.CompileFromModules("{}", modules, new[] { "data.test.allow" });
            var serialized = compiled.SerializeBinary();

            var process = Process.GetCurrentProcess();
            process.Refresh();
            var baseline = process.WorkingSet64;
            var maxDelta = 0L;
            var baselineManaged = GC.GetTotalMemory(false);
            var maxManagedDelta = 0L;

            for (var i = 1; i <= Iterations; i++)
            {
                var vm = new Rvm();
                var program = Program.DeserializeBinary(serialized, out _);
                vm.LoadProgram(program);
                vm.SetDataJson("{}");
                vm.SetInputJson("{}");
                _ = vm.ExecuteEntryPoint(0);

                if (i % GcEvery == 0)
                {
                    ForceFullGc();
                }

                if (i % LogEvery == 0)
                {
                    process.Refresh();
                    var workingSet = process.WorkingSet64;
                    var managed = GC.GetTotalMemory(false);
                    var delta = workingSet - baseline;
                    var managedDelta = managed - baselineManaged;
                    if (delta > maxDelta)
                    {
                        maxDelta = delta;
                    }
                    if (managedDelta > maxManagedDelta)
                    {
                        maxManagedDelta = managedDelta;
                    }
                    Console.WriteLine($"\n\n\u001b[1m{i} ws_mb={workingSet / 1048576.0:F1} managed_mb={managed / 1048576.0:F1} delta_mb={delta / 1048576.0:F1}\u001b[0m\n\n");
                }
            }

            if (MaxWorkingSetDeltaBytes is { } limit)
            {
                Console.WriteLine($"\n\n\u001b[1mSUMMARY: max ws delta {maxDelta / 1048576.0:F1} MB (limit {limit / 1048576.0:F1} MB); max managed delta {maxManagedDelta / 1048576.0:F1} MB.\u001b[0m\n\n");
                Assert.IsTrue(
                    maxDelta <= limit,
                    $"Working set grew by {maxDelta / 1048576.0:F1} MB (limit {limit / 1048576.0:F1} MB). Managed heap max delta {maxManagedDelta / 1048576.0:F1} MB.");
            }
        });
    }
}
