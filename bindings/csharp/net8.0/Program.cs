//-----------------------------------------------------------------------
// <copyright file="Program.cs" company="Microsoft">
//    Copyright (c)2012 Microsoft. All rights reserved.
// </copyright>
// <summary>
//    Contains code to test the Regorus class for C#
// and .NET 8.0 bindings. 
// </summary>
//-----------------------------------------------------------------------

using System.Diagnostics;

long nanosecPerTick = (1000L*1000L*1000L) / Stopwatch.Frequency;
var w = new Stopwatch();


// Force load of modules.
{
    var _e = new Regorus.Engine();
    var _j = System.Text.Json.JsonDocument.Parse("{}");
}

w.Restart();

var engine = new Regorus.Engine();

w.Stop();
var newEngineTicks = w.ElapsedTicks;


w.Restart();

// Load policies and data.
engine.AddPolicyFromFile("../../../tests/aci/framework.rego");
engine.AddPolicyFromFile("../../../tests/aci/api.rego");
engine.AddPolicyFromFile("../../../tests/aci/policy.rego");
engine.AddDataFromJsonFile("../../../tests/aci/data.json");


w.Stop();
var loadPoliciesTicks = w.ElapsedTicks;


w.Restart();

// Set input and eval rule.
engine.SetInputFromJsonFile("../../../tests/aci/input.json");
var value = engine.EvalQuery("data.framework.mount_overlay");
var valueDoc = System.Text.Json.JsonDocument.Parse(value);

w.Stop();
var evalTicks = w.ElapsedTicks;

Console.WriteLine("{0}", valueDoc);


Console.WriteLine("Engine creation took {0} msecs", (newEngineTicks*nanosecPerTick)/(1000.0*1000.0));
Console.WriteLine("Load policies and data took {0} msecs", (loadPoliciesTicks*nanosecPerTick)/(1000.0*1000.0));
Console.WriteLine("EvalQuery took {0} msecs", (evalTicks*nanosecPerTick)/(1000.0*1000.0));

engine = new Regorus.Engine();
engine.AddPolicy(
  "test.rego", 
  "package test\nx = 1\nmessage = `Hello`");

engine.SetEnableCoverage(true);
Console.WriteLine("{0}", engine.EvalRule("data.test.message"));
Console.WriteLine("{0}", engine.GetCoverageReportPretty());
