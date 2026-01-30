// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
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
}