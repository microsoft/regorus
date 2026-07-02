// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Regorus.Tests;

[TestClass]
public sealed class RvmProgramTests
{
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
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltin("get_account") };

        using var program = Program.CompileFromModules("{}", modules, entryPoints, hostAwaitBuiltins);
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
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltin("translate") };

        using var program = Program.CompileFromModules("{}", modules, entryPoints, hostAwaitBuiltins);
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
            var builtins = new[] { new HostAwaitBuiltin(badName) };
            Assert.ThrowsException<InvalidOperationException>(
                () => Program.CompileFromModules("{}", modules, entryPoints, builtins),
                $"expected compilation to reject empty/whitespace name '{badName}'");
        }
    }

    [TestMethod]
    public void RegisteredHostAwait_CompileRejectsDuplicateRegistration()
    {
        var modules = new[] { new PolicyModule("noop.rego", "package demo\nallow := true\n") };
        var entryPoints = new[] { "data.demo.allow" };
        var builtins = new[]
        {
            new HostAwaitBuiltin("translate"),
            new HostAwaitBuiltin("translate"),
        };

        Assert.ThrowsException<InvalidOperationException>(
            () => Program.CompileFromModules("{}", modules, entryPoints, builtins),
            "expected compilation to reject duplicate registration");
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

    [TestMethod]
    public void RegisteredHostAwait_GetAccessorsReturnNullWhenVmIsNotSuspended()
    {
        var modules = new[] { new PolicyModule("translate.rego", TranslatePolicy) };
        var entryPoints = new[] { "data.demo.greeting" };
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltin("translate") };

        using var program = Program.CompileFromModules("{}", modules, entryPoints, hostAwaitBuiltins);
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
        var hostAwaitBuiltins = new[] { new HostAwaitBuiltin("translate") };

        using var program = Program.CompileFromModules("{}", modules, entryPoints, hostAwaitBuiltins);
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
            new HostAwaitBuiltin("translate"),
            new HostAwaitBuiltin("lookup_user"),
        };

        using var program = Program.CompileFromModules("{}", modules, entryPoints, hostAwaitBuiltins);
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