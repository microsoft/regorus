// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Text.Json;
using System.Threading;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Regorus.Tests;

[TestClass]
public sealed class RvmProgramTests
{
    private static Program CompileWithHostAwaitV2(
        string dataJson,
        IReadOnlyList<PolicyModule> modules,
        IReadOnlyList<string> entryPoints,
        IReadOnlyList<HostAwaitBuiltin> legacyHostAwaitBuiltins,
        IReadOnlyList<HostAwaitBuiltinV2> hostAwaitBuiltinsV2) =>
        Program.CompileFromModulesWithHostAwaitV2(
            dataJson,
            modules,
            entryPoints,
            legacyHostAwaitBuiltins,
            hostAwaitBuiltinsV2);

    private const string Policy = """
package demo
default allow = false
allow if {
  input.user == "alice"
  some role in data.roles[input.user]
  role == "admin"
  count(input.actions) > 0
}
""";

    private const string BuiltinNamesPolicy = """
package demo
import rego.v1

allow if {
  count(input.actions) > 0
  contains(input.user, "ali")
}
""";

    private const string Data = """
{
  "roles": {
    "alice": ["admin", "reader"]
  }
}
""";

    private const string Input = """
{
  "user": "alice",
  "actions": ["read"]
}
""";

    private const string HostAwaitPolicy = """
package demo
import rego.v1

default allow := false

allow if {
  input.account.active == true
  details := __builtin_host_await(input.account.id, "account")
  details.tier == "gold"
}
""";

    private const string HostAwaitInput = """
{
  "account": {
    "id": "acct-1",
    "active": true
  }
}
""";

    private const string CumulativeHostAwaitPolicy = """
package demo
import rego.v1

result := __builtin_host_await(
  __builtin_host_await(input.value, "first"),
  "second"
)
""";

    [TestMethod]
    public void Program_compile_and_execute_succeeds()
    {
        var modules = new[] { new PolicyModule("demo.rego", Policy) };
        var entryPoints = new[] { "data.demo.allow" };

        var program = Program.CompileFromModules(Data, modules, entryPoints);
        var listing = program.GenerateListing();
        Assert.IsFalse(string.IsNullOrWhiteSpace(listing), "listing should be generated");

        var binary = program.SerializeBinary();
        var rehydrated = Program.DeserializeBinary(binary, out var isPartial);
        Assert.IsFalse(isPartial, "program should be fully deserialized");

        using var vm = new Rvm();
        vm.LoadProgram(rehydrated);
        vm.SetDataJson(Data);
        vm.SetInputJson(Input);

        var result = vm.Execute();
        Assert.AreEqual("true", result, "expected allow=true");
    }

    [TestMethod]
    public void Program_get_builtin_names_for_empty_program_returns_empty_read_only_list()
    {
        using var program = Program.CreateEmpty();

        var names = program.GetBuiltinNames();
        Assert.AreEqual(0, names.Count);

        var mutableNames = names as IList<string>;
        Assert.IsNotNull(mutableNames);
        Assert.ThrowsException<NotSupportedException>(() => mutableNames!.Add("count"));
    }

    [TestMethod]
    public void Program_get_builtin_names_returns_compiled_names_in_table_order()
    {
        var modules = new[] { new PolicyModule("builtin_names.rego", BuiltinNamesPolicy) };
        using var program = Program.CompileFromModules("{}", modules, new[] { "data.demo.allow" });

        Assert.AreEqual("count,contains", string.Join(",", program.GetBuiltinNames()));
        Assert.AreEqual("count,contains", string.Join(",", program.GetBuiltinNames()));
    }

    [TestMethod]
    public void Program_get_builtin_names_is_read_only_without_mutating_the_program()
    {
        var modules = new[] { new PolicyModule("builtin_names.rego", BuiltinNamesPolicy) };
        using var program = Program.CompileFromModules("{}", modules, new[] { "data.demo.allow" });
        var names = program.GetBuiltinNames();

        var mutableNames = names as IList<string>;
        Assert.IsNotNull(mutableNames);
        Assert.ThrowsException<NotSupportedException>(() => mutableNames![0] = "changed");
        Assert.AreEqual("count,contains", string.Join(",", program.GetBuiltinNames()));
    }

    [TestMethod]
    public void Program_get_builtin_names_snapshot_survives_disposal_and_disposed_access_fails()
    {
        var modules = new[] { new PolicyModule("builtin_names.rego", BuiltinNamesPolicy) };
        var program = Program.CompileFromModules("{}", modules, new[] { "data.demo.allow" });
        var names = program.GetBuiltinNames();

        program.Dispose();

        Assert.AreEqual("count,contains", string.Join(",", names));
        Assert.ThrowsException<ObjectDisposedException>(() => program.GetBuiltinNames());
    }

    [TestMethod]
    public void Program_get_builtin_names_survives_binary_round_trip()
    {
        var modules = new[] { new PolicyModule("builtin_names.rego", BuiltinNamesPolicy) };
        using var program = Program.CompileFromModules("{}", modules, new[] { "data.demo.allow" });
        using var restored = Program.DeserializeBinary(program.SerializeBinary(), out var isPartial);

        Assert.IsFalse(isPartial);
        Assert.AreEqual("count,contains", string.Join(",", restored.GetBuiltinNames()));
    }

    [TestMethod]
    public void Program_get_builtin_names_excludes_registered_host_await_builtin_named_count()
    {
        var modules = new[] { new PolicyModule("builtin_names.rego", BuiltinNamesPolicy) };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("count", 1) };
        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            new[] { "data.demo.allow" },
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);

        Assert.AreEqual("contains", string.Join(",", program.GetBuiltinNames()));
    }

    [TestMethod]
    public void Program_get_builtin_names_excludes_zero_and_multi_arity_host_await_builtins()
    {
        const string policy = """
package demo
import rego.v1

allow if {
  empty := current_context()
  pair := lookup_pair(input.left, input.right)
  count([empty, pair]) == 2
}
""";
        var modules = new[] { new PolicyModule("builtin_names.rego", policy) };
        var hostAwaitBuiltins = new[]
        {
            new HostAwaitBuiltinV2("current_context", 0),
            new HostAwaitBuiltinV2("lookup_pair", 2),
        };
        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            new[] { "data.demo.allow" },
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);

        Assert.AreEqual("count", string.Join(",", program.GetBuiltinNames()));
    }

    [TestMethod]
    public void HostAwait_legacy_contract_is_name_only_and_v2_is_explicit()
    {
        Assert.IsNotNull(
            typeof(HostAwaitBuiltin).GetConstructor(new[] { typeof(string) }),
            "the legacy managed registration constructor must remain name-only");

        var assembly = typeof(Program).Assembly;
        var v2Type = assembly.GetType("Regorus.HostAwaitBuiltinV2");
        Assert.IsNotNull(v2Type, "the opt-in v2 registration type must be present");
        Assert.IsNotNull(
            v2Type!.GetConstructor(new[] { typeof(string), typeof(int) }),
            "the v2 registration constructor must take a fixed arity");

        var v2ListType = typeof(IReadOnlyList<>).MakeGenericType(v2Type);
        var method = typeof(Program).GetMethod(
            "CompileFromModulesWithHostAwaitV2",
            new[]
            {
                typeof(string),
                typeof(IReadOnlyList<PolicyModule>),
                typeof(IReadOnlyList<string>),
                typeof(IReadOnlyList<HostAwaitBuiltin>),
                v2ListType,
            });
        Assert.IsNotNull(method, "the v2 compile entrypoint must remain distinct");

        var legacyNativeType = assembly.GetType("Regorus.Internal.RegorusHostAwaitBuiltin");
        Assert.IsNotNull(legacyNativeType);
        Assert.AreEqual(IntPtr.Zero, Marshal.OffsetOf(legacyNativeType!, "name"));
        Assert.AreEqual(IntPtr.Size, Marshal.SizeOf(legacyNativeType!));
    }

    [TestMethod]
    public void SetMaxInstructions_zero_stops_execution_and_is_per_vm()
    {
        var modules = new[] { new PolicyModule("demo.rego", Policy) };
        var entryPoints = new[] { "data.demo.allow" };
        using var program = Program.CompileFromModules(Data, modules, entryPoints);

        using var limitedVm = new Rvm();
        limitedVm.SetMaxInstructions(0);
        limitedVm.LoadProgram(program);
        limitedVm.SetDataJson(Data);
        limitedVm.SetInputJson(Input);
        Assert.ThrowsException<InvalidOperationException>(
            () => limitedVm.Execute(),
            "zero must prohibit every instruction dispatch");

        using var independentVm = new Rvm();
        independentVm.LoadProgram(program);
        independentVm.SetDataJson(Data);
        independentVm.SetInputJson(Input);
        Assert.AreEqual("true", independentVm.Execute(), "VM limits must not be shared");
    }

    [TestMethod]
    public void SetMaxInstructions_replacement_applies_to_a_fresh_execution()
    {
        var modules = new[] { new PolicyModule("demo.rego", Policy) };
        var entryPoints = new[] { "data.demo.allow" };
        using var program = Program.CompileFromModules(Data, modules, entryPoints);
        using var vm = new Rvm();

        vm.SetMaxInstructions(0);
        vm.LoadProgram(program);
        vm.SetDataJson(Data);
        vm.SetInputJson(Input);
        Assert.ThrowsException<InvalidOperationException>(() => vm.Execute());

        vm.SetMaxInstructions(1000);
        Assert.AreEqual("true", vm.Execute(), "a fresh execution should start with zero consumed instructions");
    }

    [TestMethod]
    public void Execute_after_success_starts_a_fresh_execution()
    {
        var modules = new[] { new PolicyModule("demo.rego", Policy) };
        var entryPoints = new[] { "data.demo.allow" };
        using var program = Program.CompileFromModules(Data, modules, entryPoints);
        using var vm = new Rvm();
        vm.SetMaxInstructions(1000);
        vm.LoadProgram(program);
        vm.SetDataJson(Data);
        vm.SetInputJson(Input);

        Assert.AreEqual("true", vm.Execute());
        vm.SetInputJson(Input.Replace("\"alice\"", "\"bob\"", StringComparison.Ordinal));
        Assert.AreEqual("false", vm.Execute(), "a successful execution must not consume the next fresh execution");
    }

    [TestMethod]
    public void SetMaxInstructions_preserves_native_width_and_rejects_32_bit_overflow()
    {
        using var vm = new Rvm();

        if (IntPtr.Size == 4)
        {
            Assert.ThrowsException<ArgumentOutOfRangeException>(
                () => vm.SetMaxInstructions((ulong)uint.MaxValue + 1),
                "values wider than native usize must not be truncated");
        }
        else
        {
            vm.SetMaxInstructions(ulong.MaxValue);
        }
    }

    [TestMethod]
    public void SetMaxInstructions_rejects_a_disposed_vm()
    {
        var vm = new Rvm();
        vm.Dispose();

        Assert.ThrowsException<ObjectDisposedException>(() => vm.SetMaxInstructions(1));
    }

    [TestMethod]
    public void Program_compile_from_engine_succeeds()
    {
        using var engine = new Engine();
        engine.AddPolicy("demo.rego", Policy);

        var program = Program.CompileFromEngine(engine, new[] { "data.demo.allow" });
        using var vm = new Rvm();
        vm.LoadProgram(program);
        vm.SetDataJson(Data);
        vm.SetInputJson(Input);

        var result = vm.Execute();
        Assert.AreEqual("true", result, "expected allow=true");
    }

    [TestMethod]
    public void Program_host_await_suspend_and_resume_succeeds()
    {
        var modules = new[] { new PolicyModule("host_await.rego", HostAwaitPolicy) };
        var entryPoints = new[] { "data.demo.allow" };

        using var program = Program.CompileFromModules("{}", modules, entryPoints);
        using var vm = new Rvm();
        vm.SetExecutionMode(1);
        vm.LoadProgram(program);
        vm.SetInputJson(HostAwaitInput);

        var initial = vm.Execute();
        var state = vm.GetExecutionState();
        Assert.IsNotNull(state, "execution state should be available");
        StringAssert.Contains(state!, "HostAwait", "expected HostAwait suspension");

        var resumed = vm.Resume("{\"tier\":\"gold\"}");
        Assert.AreEqual("true", resumed, "expected allow=true after resume");
    }

    [TestMethod]
    public void SetMaxInstructions_host_await_resume_preserves_consumed_count()
    {
        var modules = new[] { new PolicyModule("host_await.rego", HostAwaitPolicy) };
        var entryPoints = new[] { "data.demo.allow" };

        using var program = Program.CompileFromModules("{}", modules, entryPoints);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.SetMaxInstructions(1000);
        vm.LoadProgram(program);
        vm.SetInputJson(HostAwaitInput);

        vm.Execute();
        StringAssert.Contains(vm.GetExecutionState()!, "HostAwait");

        vm.SetMaxInstructions(0);
        Assert.ThrowsException<InvalidOperationException>(
            () => vm.Resume("{\"tier\":\"gold\"}"),
            "lowering a suspended VM below its consumed count must reject the next dispatch");
        Assert.IsTrue(
            vm.GetExecutionState()!.Contains("Error", StringComparison.Ordinal),
            "instruction exhaustion must leave the VM in Error state");
        Assert.ThrowsException<InvalidOperationException>(
            () => vm.Resume("{\"tier\":\"gold\"}"),
            "Resume must be rejected after the VM enters Error state");

        vm.SetMaxInstructions(1000);
        vm.SetInputJson("""
{
  "account": {
    "id": "acct-2",
    "active": true
  }
}
""");
        vm.Execute();
        StringAssert.Contains(vm.GetHostAwaitArgument()!, "acct-2");
        Assert.AreEqual("true", vm.Resume("{\"tier\":\"gold\"}"));
    }

    [TestMethod]
    public void SetMaxInstructions_registered_host_await_resume_failure_allows_vm_reuse()
    {
        const string policy = """
package demo
import rego.v1

default allow := false
allow if { get_account(input.account_id) == "allow" }
""";
        var modules = new[] { new PolicyModule("registered_limits.rego", policy) };
        var entryPoints = new[] { "data.demo.allow" };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("get_account", 1) };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.SetMaxInstructions(1000);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"account_id\":\"acct-1\"}");

        vm.Execute();
        Assert.AreEqual("get_account", vm.GetHostAwaitIdentifier());
        using (var firstArgument = JsonDocument.Parse(vm.GetHostAwaitArgument()!))
        {
            Assert.AreEqual(JsonValueKind.Array, firstArgument.RootElement.ValueKind);
            Assert.AreEqual("acct-1", firstArgument.RootElement[0].GetString());
        }

        vm.SetMaxInstructions(0);
        Assert.ThrowsException<InvalidOperationException>(
            () => vm.Resume("\"allow\""),
            "instruction exhaustion after a packed HostAwait suspension must fail resume");
        Assert.IsTrue(vm.GetExecutionState()!.Contains("Error", StringComparison.Ordinal));
        Assert.IsNull(vm.GetHostAwaitIdentifier());
        Assert.IsNull(vm.GetHostAwaitArgument());
        Assert.ThrowsException<InvalidOperationException>(
            () => vm.Resume("\"allow\""),
            "resume must remain unavailable after instruction exhaustion");

        vm.SetMaxInstructions(1000);
        vm.SetInputJson("{\"account_id\":\"acct-2\"}");
        vm.Execute();
        Assert.AreEqual("get_account", vm.GetHostAwaitIdentifier());
        using (var secondArgument = JsonDocument.Parse(vm.GetHostAwaitArgument()!))
        {
            Assert.AreEqual(JsonValueKind.Array, secondArgument.RootElement.ValueKind);
            Assert.AreEqual("acct-2", secondArgument.RootElement[0].GetString());
        }

        Assert.AreEqual("true", vm.Resume("\"allow\""));
        Assert.IsNull(vm.GetHostAwaitIdentifier());
        Assert.IsNull(vm.GetHostAwaitArgument());
    }

    [TestMethod]
    public void SetMaxInstructions_supports_multiple_host_await_resumes()
    {
        var modules = new[] { new PolicyModule("multi.rego", MultiAwaitPolicy) };
        var entryPoints = new[] { "data.demo.greeting" };
        var hostAwaitBuiltins = new[]
        {
            new HostAwaitBuiltinV2("translate", 1),
            new HostAwaitBuiltinV2("lookup_user", 1),
        };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.SetMaxInstructions(1000);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"lang\":\"es\",\"user_id\":\"u1\"}");

        vm.Execute();
        StringAssert.Contains(vm.GetExecutionState()!, "HostAwait");

        vm.Resume("\"hola\"");
        StringAssert.Contains(vm.GetExecutionState()!, "HostAwait");

        var result = vm.Resume("{\"name\":\"Alice\"}");
        Assert.AreEqual("\"hola Alice\"", result);
    }

    [TestMethod]
    public void SetMaxInstructions_counts_sequential_cross_thread_resume_cumulatively()
    {
        var modules = new[] { new PolicyModule("cumulative.rego", CumulativeHostAwaitPolicy) };
        var entryPoints = new[] { "data.demo.result" };

        using var program = Program.CompileFromModules("{}", modules, entryPoints);
        var listing = GetListing(program);
        AssertCumulativeHostAwaitListing(listing);

        // The generated path is:
        // E: PC 0, 2, 3, 4, 5, 6 -> first HostAwait (6 dispatches).
        // R1: PC 7, 8 -> second HostAwait (2 dispatches).
        // R2: PC 9, 10, 1 -> completion (3 dispatches).
        const ulong executeToFirstSuspension = 6;
        const ulong firstResumeToSecondSuspension = 2;
        const ulong secondResumeToCompletion = 3;
        const ulong positiveLimit = 8;

        Assert.AreEqual(
            positiveLimit,
            executeToFirstSuspension + firstResumeToSecondSuspension);
        Assert.IsTrue(
            positiveLimit < executeToFirstSuspension
                + firstResumeToSecondSuspension
                + secondResumeToCompletion);
        Assert.IsTrue(
            firstResumeToSecondSuspension + secondResumeToCompletion <= positiveLimit);

        Console.WriteLine(
            $"RVM budget path: entry_points=[data.demo.result], listing_instructions=11, "
            + $"E={executeToFirstSuspension}, R1={firstResumeToSecondSuspension}, "
            + $"R2={secondResumeToCompletion}, N={positiveLimit}; "
            + "E+R1<=N<E+R1+R2 and R1+R2<=N.");

        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.SetMaxInstructions(positiveLimit);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"value\":\"initial\"}");

        using var executeFinished = new ManualResetEventSlim();
        using var resumeFinished = new ManualResetEventSlim();
        Exception? executeError = null;
        Exception? firstResumeError = null;
        Exception? secondResumeError = null;
        var executeThreadId = -1;
        var resumeThreadId = -1;
        var firstResumeState = string.Empty;

        var executeThread = new Thread(() =>
        {
            try
            {
                vm.Execute();
                executeThreadId = Thread.CurrentThread.ManagedThreadId;
            }
            catch (Exception ex)
            {
                executeError = ex;
            }
            finally
            {
                executeFinished.Set();
            }

            if (!resumeFinished.Wait(TimeSpan.FromSeconds(30)))
            {
                executeError ??= new TimeoutException("Resume thread did not complete.");
            }
        });

        var resumeThread = new Thread(() =>
        {
            try
            {
                if (!executeFinished.Wait(TimeSpan.FromSeconds(30)))
                {
                    throw new TimeoutException("Execute thread did not complete.");
                }

                resumeThreadId = Thread.CurrentThread.ManagedThreadId;
                vm.Resume("\"first\"");
            }
            catch (Exception ex)
            {
                firstResumeError = ex;
            }

            if (firstResumeError is null)
            {
                firstResumeState = vm.GetExecutionState()!;
                try
                {
                    vm.Resume("\"second\"");
                }
                catch (Exception ex)
                {
                    secondResumeError = ex;
                }
            }

            resumeFinished.Set();
        });

        executeThread.Start();
        resumeThread.Start();
        executeThread.Join();
        resumeThread.Join();

        Assert.IsNull(executeError, executeError?.ToString());
        Assert.IsNull(firstResumeError, firstResumeError?.ToString());
        Assert.IsNotNull(secondResumeError, "cumulative execution must exhaust the positive limit");
        Assert.AreNotEqual(executeThreadId, resumeThreadId, "continuation must use distinct threads");
        StringAssert.Contains(firstResumeState, "HostAwait");
        StringAssert.Contains(vm.GetExecutionState() ?? string.Empty, "InstructionLimitExceeded");
    }

    private static string GetListing(Program program)
    {
        var listing = program.GenerateListing();
        Assert.IsNotNull(listing);
        return listing!;
    }

    private static void AssertCumulativeHostAwaitListing(string listing)
    {
        var expectedInstructions = new[]
        {
            "; RVM Assembly - 11 instructions, 3 literals, 0 builtins",
            "000: CallRule",
            "001: Return",
            "002: RuleInit",
            "003:     LoadInput",
            "004:     IndexLiteral",
            "005:     Load",
            "006:     HostAwait",
            "007:     Load",
            "008:     HostAwait",
            "009:     Move",
            "010: } return from rule",
        };

        foreach (var expectedInstruction in expectedInstructions)
        {
            StringAssert.Contains(
                listing,
                expectedInstruction,
                $"compiled RVM listing changed; missing '{expectedInstruction}'");
        }
    }

    private const string GetAccountPolicy = """
package demo
import rego.v1

default allow := false

allow if {
  account := get_account({"id": input.account_id})
  account.status == "active"
}
""";

    [TestMethod]
    public void RegisteredHostAwait_Suspendable_SuspendAndResume()
    {
        var modules = new[] { new PolicyModule("account.rego", GetAccountPolicy) };
        var entryPoints = new[] { "data.demo.allow" };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("get_account", 1) };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"account_id\": \"acct-42\"}");

        // Execute — should suspend on get_account()
        vm.Execute();

        // Verify we're suspended due to HostAwait with identifier "get_account".
        var identifier = vm.GetHostAwaitIdentifier();
        Assert.AreEqual("get_account", identifier, "expected identifier to be get_account");

        var argument = vm.GetHostAwaitArgument();
        Assert.IsNotNull(argument, "expected non-null argument");
        StringAssert.Contains(argument!, "acct-42", "expected account_id in argument");

        // Resume with an account response
        var result = vm.Resume("{\"status\": \"active\", \"name\": \"Alice\"}");
        Assert.AreEqual("true", result, "expected allow=true after resume");
    }

    [TestMethod]
    public void RegisteredHostAwait_LegacyArrayInputIsPassedWithoutPacking()
    {
        const string policy = """
package demo
import rego.v1

result := echo([1, 2])
""";
        var modules = new[] { new PolicyModule("legacy_echo.rego", policy) };
        var entryPoints = new[] { "data.demo.result" };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltin("echo") };

        using var program = Program.CompileFromModules("{}", modules, entryPoints, hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.LoadProgram(program);

        vm.Execute();

        Assert.AreEqual("echo", vm.GetHostAwaitIdentifier());
        using var argument = JsonDocument.Parse(vm.GetHostAwaitArgument()!);
        Assert.AreEqual(JsonValueKind.Array, argument.RootElement.ValueKind);
        Assert.AreEqual(2, argument.RootElement.GetArrayLength());
        Assert.AreEqual(1, argument.RootElement[0].GetInt32());
        Assert.AreEqual(2, argument.RootElement[1].GetInt32());
        Assert.AreEqual("\"legacy-response\"", vm.Resume("\"legacy-response\""));
    }

    [TestMethod]
    public void RegisteredHostAwait_LegacyValuesRemainRaw()
    {
        const string policy = """
package demo
import rego.v1

result := [
  echo(7),
  echo("text"),
  echo(false),
  echo(null),
  echo([1, 2]),
  echo({"id": "x"})
]
""";
        var modules = new[] { new PolicyModule("legacy_values.rego", policy) };
        var entryPoints = new[] { "data.demo.result" };
        var legacyBuiltins = new[] { new HostAwaitBuiltin("echo") };
        var expectedArguments = new[] { "7", "\"text\"", "false", "null", "[1,2]", "{\"id\":\"x\"}" };

        using var program = Program.CompileFromModulesWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            legacyBuiltins,
            Array.Empty<HostAwaitBuiltinV2>());
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.LoadProgram(program);
        vm.Execute();

        string? finalResult = null;
        foreach (var expectedArgument in expectedArguments)
        {
            Assert.AreEqual("echo", vm.GetHostAwaitIdentifier());
            using var argument = JsonDocument.Parse(vm.GetHostAwaitArgument()!);
            Assert.AreEqual(expectedArgument, JsonSerializer.Serialize(argument.RootElement));
            finalResult = vm.Resume("\"host-response\"");
        }

        var finalResultJson = finalResult
            ?? throw new InvalidOperationException(
                "Expected the final HostAwait resume to return a result.");
        using var results = JsonDocument.Parse(finalResultJson);
        Assert.AreEqual(JsonValueKind.Array, results.RootElement.ValueKind);
        Assert.AreEqual(expectedArguments.Length, results.RootElement.GetArrayLength());
        foreach (var result in results.RootElement.EnumerateArray())
        {
            Assert.AreEqual("host-response", result.GetString());
        }
    }

    [TestMethod]
    public void RegisteredHostAwait_V2CompileSupportsLegacyAndPackedRegistrationsTogether()
    {
        const string policy = """
package demo
import rego.v1

legacy_value := echo(input.raw)
packed_value := combine(input.first, input.second)
result := {"legacy": legacy_value, "packed": packed_value}
""";
        var modules = new[] { new PolicyModule("mixed_host_await.rego", policy) };
        var entryPoints = new[] { "data.demo.result" };

        using var program = Program.CompileFromModulesWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            new[] { new HostAwaitBuiltin("echo") },
            new[] { new HostAwaitBuiltinV2("combine", 2) });
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"raw\":[1,2],\"first\":\"left\",\"second\":\"right\"}");

        vm.Execute();

        Assert.AreEqual("echo", vm.GetHostAwaitIdentifier());
        using (var legacyArgument = JsonDocument.Parse(vm.GetHostAwaitArgument()!))
        {
            Assert.AreEqual(JsonValueKind.Array, legacyArgument.RootElement.ValueKind);
            Assert.AreEqual(2, legacyArgument.RootElement.GetArrayLength());
            Assert.AreEqual(1, legacyArgument.RootElement[0].GetInt32());
        }

        vm.Resume("\"legacy-result\"");
        Assert.AreEqual("combine", vm.GetHostAwaitIdentifier());
        using (var packedArgument = JsonDocument.Parse(vm.GetHostAwaitArgument()!))
        {
            Assert.AreEqual(JsonValueKind.Array, packedArgument.RootElement.ValueKind);
            Assert.AreEqual(2, packedArgument.RootElement.GetArrayLength());
            Assert.AreEqual("left", packedArgument.RootElement[0].GetString());
            Assert.AreEqual("right", packedArgument.RootElement[1].GetString());
        }

        var result = vm.Resume("\"packed-result\"");
        var resultJsonText = result
            ?? throw new InvalidOperationException("Expected HostAwait resume to return a result.");
        using var resultJson = JsonDocument.Parse(resultJsonText);
        Assert.AreEqual("legacy-result", resultJson.RootElement.GetProperty("legacy").GetString());
        Assert.AreEqual("packed-result", resultJson.RootElement.GetProperty("packed").GetString());
    }

    [TestMethod]
    public void RegisteredHostAwait_MultipleInputs_ArePackedInOrder()
    {
        const string policy = """
package demo
import rego.v1

result := combine(input.left, input.right)
""";
        var modules = new[] { new PolicyModule("combine.rego", policy) };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("combine", 2) };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            new[] { "data.demo.result" },
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"left\":\"first\",\"right\":\"second\"}");

        vm.Execute();

        Assert.AreEqual("combine", vm.GetHostAwaitIdentifier());
        using var argumentJson = JsonDocument.Parse(vm.GetHostAwaitArgument()!);
        var arguments = argumentJson.RootElement;
        Assert.AreEqual(JsonValueKind.Array, arguments.ValueKind);
        Assert.AreEqual(2, arguments.GetArrayLength());
        Assert.AreEqual("first", arguments[0].GetString());
        Assert.AreEqual("second", arguments[1].GetString());
        Assert.AreEqual("\"combined\"", vm.Resume("\"combined\""));
    }

    [TestMethod]
    public void RegisteredHostAwait_ZeroInputs_ArePackedAsEmptyArray()
    {
        const string policy = """
package demo
import rego.v1

result := current_context()
""";
        var modules = new[] { new PolicyModule("context.rego", policy) };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("current_context", 0) };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            new[] { "data.demo.result" },
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.LoadProgram(program);
        vm.SetInputJson("{}");

        vm.Execute();

        Assert.AreEqual("current_context", vm.GetHostAwaitIdentifier());
        using var argumentJson = JsonDocument.Parse(vm.GetHostAwaitArgument()!);
        Assert.AreEqual(JsonValueKind.Array, argumentJson.RootElement.ValueKind);
        Assert.AreEqual(0, argumentJson.RootElement.GetArrayLength());
        Assert.AreEqual("\"context\"", vm.Resume("\"context\""));
    }

    private const string TranslatePolicy = """
package demo
import rego.v1

default greeting := "unknown"

greeting := msg if {
  msg := translate(input.lang)
}
""";

    [TestMethod]
    public void RegisteredHostAwait_RunToCompletion_WithPreloadedResponses()
    {
        var modules = new[] { new PolicyModule("translate.rego", TranslatePolicy) };
        var entryPoints = new[] { "data.demo.greeting" };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("translate", 1) };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.RunToCompletion);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"lang\": \"es\"}");

        // Pre-load a response for translate
        vm.SetHostAwaitResponses(new Dictionary<string, IReadOnlyList<string>>
        {
            ["translate"] = new[] { "\"hola\"" },
        });

        // Execute — translate returns "hola"
        var result = vm.Execute();
        Assert.AreEqual("\"hola\"", result, "expected greeting=hola");
    }

    [TestMethod]
    public void RegisteredHostAwait_CompileRejectsEmptyOrWhitespaceName()
    {
        var modules = new[] { new PolicyModule("noop.rego", "package demo\nallow := true\n") };
        var entryPoints = new[] { "data.demo.allow" };

        foreach (var badName in new[] { "", "   ", "\t" })
        {
            var builtins = new[] { new HostAwaitBuiltinV2(badName, 1) };
            Assert.ThrowsException<InvalidOperationException>(
                () => CompileWithHostAwaitV2(
                    "{}",
                    modules,
                    entryPoints,
                    Array.Empty<HostAwaitBuiltin>(),
                    builtins),
                $"expected compilation to reject empty/whitespace name '{badName}'");
        }
    }

    [TestMethod]
    public void RegisteredHostAwaitV2_ConstructorRejectsNegativeArgumentCount()
    {
        Assert.ThrowsException<ArgumentOutOfRangeException>(
            () => _ = new HostAwaitBuiltinV2("translate", -1));
    }

    [TestMethod]
    public void RegisteredHostAwait_NativeStructLayoutsPreserveLegacyAndV2Descriptors()
    {
        var legacyType = typeof(Regorus.Internal.RegorusHostAwaitBuiltin);
        Assert.AreEqual(IntPtr.Zero, Marshal.OffsetOf(legacyType, "name"));
        Assert.AreEqual(IntPtr.Size, Marshal.SizeOf(legacyType));

        var v2Type = typeof(Regorus.Internal.RegorusHostAwaitBuiltinV2);
        Assert.AreEqual(IntPtr.Zero, Marshal.OffsetOf(v2Type, "name"));
        Assert.AreEqual(IntPtr.Size, Marshal.OffsetOf(v2Type, "arg_count"));
        Assert.AreEqual(2 * IntPtr.Size, Marshal.SizeOf(v2Type));
    }

    [TestMethod]
    public void RegisteredHostAwait_CompileRejectsDuplicateRegistration()
    {
        var modules = new[] { new PolicyModule("noop.rego", "package demo\nallow := true\n") };
        var entryPoints = new[] { "data.demo.allow" };
        var builtins = new[]
        {
            new HostAwaitBuiltinV2("translate", 1),
            new HostAwaitBuiltinV2("translate", 1),
        };

        Assert.ThrowsException<InvalidOperationException>(
            () => CompileWithHostAwaitV2(
                "{}",
                modules,
                entryPoints,
                Array.Empty<HostAwaitBuiltin>(),
                builtins),
            "expected compilation to reject duplicate registration");
    }

    [TestMethod]
    public void RegisteredHostAwait_V2CompileRejectsNullRegistrationLists()
    {
        var modules = new[] { new PolicyModule("noop.rego", "package demo\nallow := true\n") };
        var entryPoints = new[] { "data.demo.allow" };

        Assert.ThrowsException<ArgumentNullException>(
            () => Program.CompileFromModulesWithHostAwaitV2(
                "{}",
                modules,
                entryPoints,
                null!,
                Array.Empty<HostAwaitBuiltinV2>()));
        Assert.ThrowsException<ArgumentNullException>(
            () => Program.CompileFromModulesWithHostAwaitV2(
                "{}",
                modules,
                entryPoints,
                Array.Empty<HostAwaitBuiltin>(),
                null!));
    }

    [TestMethod]
    public void RegisteredHostAwait_V2CompileRejectsDuplicateAcrossModes()
    {
        var modules = new[] { new PolicyModule("noop.rego", "package demo\nallow := true\n") };
        var entryPoints = new[] { "data.demo.allow" };

        Assert.ThrowsException<InvalidOperationException>(
            () => Program.CompileFromModulesWithHostAwaitV2(
                "{}",
                modules,
                entryPoints,
                new[] { new HostAwaitBuiltin("translate") },
                new[] { new HostAwaitBuiltinV2("translate", 1) }),
            "a name must not have both legacy and packed contracts");
    }

    [TestMethod]
    public void RegisteredHostAwait_LegacyCompileRejectsNonOneArity()
    {
        const string policy = """
package demo
import rego.v1

result := lookup()
""";
        var modules = new[] { new PolicyModule("legacy_arity.rego", policy) };
        var entryPoints = new[] { "data.demo.result" };

        Assert.ThrowsException<InvalidOperationException>(
            () => Program.CompileFromModules(
                "{}",
                modules,
                entryPoints,
                new[] { new HostAwaitBuiltin("lookup") }),
            "the legacy registration must reject zero-input calls");
    }

    [TestMethod]
    public void RegisteredHostAwait_CompileRejectsReservedName()
    {
        var modules = new[] { new PolicyModule("noop.rego", "package demo\nallow := true\n") };
        var entryPoints = new[] { "data.demo.allow" };
        var builtins = new[] { new HostAwaitBuiltin("__builtin_host_await") };

        Assert.ThrowsException<InvalidOperationException>(
            () => Program.CompileFromModules("{}", modules, entryPoints, builtins),
            "expected compilation to reject reserved __builtin_host_await identifier");
    }

    public static IEnumerable<object[]> EmbeddedNulIdentifierScenarios()
    {
        // Identifiers (registration name + response key) are raw C strings with
        // no downstream parser to catch truncation, so an embedded NUL would
        // silently mis-route. Both write-points reject it.
        yield return new object[]
        {
            "builtin name",
            (Action)(() => _ = new HostAwaitBuiltin("bad\0name")),
        };
        yield return new object[]
        {
            "v2 builtin name",
            (Action)(() => _ = new HostAwaitBuiltinV2("bad\0name", 1)),
        };
        yield return new object[]
        {
            "response identifier",
            (Action)(() =>
            {
                using var vm = new Rvm();
                vm.SetHostAwaitResponses(new Dictionary<string, IReadOnlyList<string>>
                {
                    ["bad\0id"] = new[] { "\"v\"" },
                });
            }),
        };
    }

    // A raw NUL in an identifier is rejected loudly at the public surface,
    // before Rust's CStr can silently truncate it.
    [DataTestMethod]
    [DynamicData(nameof(EmbeddedNulIdentifierScenarios), DynamicDataSourceType.Method)]
    public void RegisteredHostAwait_RejectsEmbeddedNulInIdentifier(string description, Action action)
    {
        Assert.ThrowsException<ArgumentException>(
            action,
            $"expected embedded NUL in {description} to be rejected before crossing the FFI boundary");
    }

    // A JSON-escaped null (\u0000) is six ASCII chars, not a raw NUL, so it
    // round-trips faithfully. Response values are not NUL-validated (client
    // responsibility, consistent with other JSON inputs).
    [TestMethod]
    public void RegisteredHostAwait_ResponseValueWithEscapedNul_RoundTrips()
    {
        var modules = new[] { new PolicyModule("translate.rego", TranslatePolicy) };
        var entryPoints = new[] { "data.demo.greeting" };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("translate", 1) };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.RunToCompletion);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"lang\": \"es\"}");

        vm.SetHostAwaitResponses(new Dictionary<string, IReadOnlyList<string>>
        {
            ["translate"] = new[] { "\"a\\u0000b\"" },
        });

        var result = vm.Execute();

        Assert.AreEqual("\"a\\u0000b\"", result);
    }

    // Same escaped-null round-trip on the resume path (customer-controlled JSON,
    // not NUL-validated).
    [TestMethod]
    public void RegisteredHostAwait_ResumeValueWithEscapedNul_RoundTrips()
    {
        var modules = new[] { new PolicyModule("translate.rego", TranslatePolicy) };
        var entryPoints = new[] { "data.demo.greeting" };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("translate", 1) };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"lang\": \"es\"}");

        vm.Execute();
        Assert.AreEqual("translate", vm.GetHostAwaitIdentifier());

        var result = vm.Resume("\"a\\u0000b\"");

        Assert.AreEqual("\"a\\u0000b\"", result);
    }

    // Failing scenario: a raw NUL in the resume value is not validated, but
    // Rust's CStr truncates at it and the truncated text ("a) is invalid JSON,
    // so it surfaces as a loud parse error. (A raw NUL that truncates to *valid*
    // JSON — e.g. "123\0456" -> 123 — is silently accepted, the accepted
    // binding-wide value contract shared with AddDataJson/SetInputJson.)
    [TestMethod]
    public void RegisteredHostAwait_ResumeValueWithRawNul_ThrowsFromParse()
    {
        var modules = new[] { new PolicyModule("translate.rego", TranslatePolicy) };
        var entryPoints = new[] { "data.demo.greeting" };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("translate", 1) };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.Suspendable);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"lang\": \"es\"}");

        vm.Execute();
        Assert.AreEqual("translate", vm.GetHostAwaitIdentifier());

        Assert.ThrowsException<InvalidOperationException>(
            () => vm.Resume("\"a\0b\""),
            "expected a raw NUL that truncates to invalid JSON to surface as a parse error");
    }

    [TestMethod]
    public void RegisteredHostAwait_GetAccessorsReturnNullWhenVmIsNotSuspended()
    {
        var modules = new[] { new PolicyModule("translate.rego", TranslatePolicy) };
        var entryPoints = new[] { "data.demo.greeting" };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("translate", 1) };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.RunToCompletion);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"lang\": \"es\"}");
        vm.SetHostAwaitResponses(new Dictionary<string, IReadOnlyList<string>>
        {
            ["translate"] = new[] { "\"hola\"" },
        });
        vm.Execute();

        // After run-to-completion completes successfully, the VM is no longer suspended.
        Assert.IsNull(vm.GetHostAwaitArgument(), "expected null argument when VM is not suspended");
        Assert.IsNull(vm.GetHostAwaitIdentifier(), "expected null identifier when VM is not suspended");
    }

    private const string TranslateNoDefaultPolicy = """
package demo
import rego.v1

# No default — if translate() can't produce a value, the entry point
# evaluation propagates the error to the caller.
result := translate(input.lang)
""";

    [TestMethod]
    public void RegisteredHostAwait_RunToCompletion_FailsWhenResponseQueueExhausted()
    {
        var modules = new[] { new PolicyModule("translate.rego", TranslateNoDefaultPolicy) };
        var entryPoints = new[] { "data.demo.result" };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltinV2("translate", 1) };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.RunToCompletion);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"lang\": \"es\"}");

        // No responses pre-loaded — translate has nothing to return.
        // Document the actual behavior: in run-to-completion mode the
        // missing-response error fails the rule body silently rather than
        // surfacing as an exception, so Execute() returns the literal
        // string `"<undefined>"` for an entry point that produced no value.
        // Asserting the exact return value locks this contract so any
        // future change (e.g. propagating an exception) shows up as a
        // test failure that has to be explicitly re-acknowledged.
        var actual = vm.Execute();
        Assert.AreEqual(
            "\"<undefined>\"",
            actual,
            "expected `\"<undefined>\"` when the response queue is exhausted");
    }

    private const string MultiAwaitPolicy = """
package demo
import rego.v1

default greeting := "unknown"

greeting := combined if {
  hello := translate(input.lang)
  user := lookup_user({"id": input.user_id})
  combined := sprintf("%s %s", [hello, user.name])
}
""";

    [TestMethod]
    public void RegisteredHostAwait_RunToCompletion_MultipleIdentifiersInSingleCall()
    {
        var modules = new[] { new PolicyModule("multi.rego", MultiAwaitPolicy) };
        var entryPoints = new[] { "data.demo.greeting" };
        var hostAwaitBuiltins = new[]
        {
            new HostAwaitBuiltinV2("translate", 1),
            new HostAwaitBuiltinV2("lookup_user", 1),
        };

        using var program = CompileWithHostAwaitV2(
            "{}",
            modules,
            entryPoints,
            Array.Empty<HostAwaitBuiltin>(),
            hostAwaitBuiltins);
        using var vm = new Rvm();
        vm.SetExecutionMode(ExecutionMode.RunToCompletion);
        vm.LoadProgram(program);
        vm.SetInputJson("{\"lang\": \"es\", \"user_id\": \"u1\"}");

        // Pre-load responses for BOTH identifiers in a single call.
        // The new IReadOnlyDictionary API atomically replaces ALL prior
        // responses, so this single call must carry every identifier the
        // policy may invoke during this run.
        vm.SetHostAwaitResponses(new Dictionary<string, IReadOnlyList<string>>
        {
            ["translate"] = new[] { "\"hola\"" },
            ["lookup_user"] = new[] { "{\"name\": \"Alice\"}" },
        });

        var result = vm.Execute();
        Assert.AreEqual("\"hola Alice\"", result, "expected combined greeting from both responses");
    }

}