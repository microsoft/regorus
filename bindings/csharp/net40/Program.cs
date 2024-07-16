//-----------------------------------------------------------------------
// <copyright file="Program.cs" company="Microsoft">
//    Copyright (c)2012 Microsoft. All rights reserved.
// </copyright>
// <summary>
//    Contains code to test the Regorus Policy Engine base class for C#
// and .NET4.0 bindings. It can be built and tested in Windows only. 
// </summary>
//-----------------------------------------------------------------------
using System;
using System.Text;

using System.Diagnostics;
using Microsoft.WindowsAzure.Regorus.IaaS;

namespace regoregorus_test
{
    class Program
    {
        static void Main(string[] args)
        {
            long nanosecPerTick = (1000L * 1000L * 1000L) / Stopwatch.Frequency;
            var w = new Stopwatch();
            w.Restart();

            var engine = new RegorusPolicyEngine();

            w.Stop();
            var newEngineTicks = w.ElapsedTicks;


            w.Restart();

            // Load policies and data.
            engine.AddPolicyFromFile("../../../examples/extension_list/agent_extension_policy.rego");
            engine.AddDataFromJsonFile("../../../examples/extension_list/agent-extension-data-allow-only.json");


            w.Stop();
            var loadPoliciesTicks = w.ElapsedTicks;


            w.Restart();

            // Set input and eval query.
            engine.SetInputFromJsonFile("../../../examples/extension_list/agent-extension-input.json");
            var results = engine.EvalQuery("data.agent_extension_policy.extensions_to_download=x");
            Console.WriteLine("Download query test: \n {0}", results);

            results = engine.EvalQuery("data.agent_extension_policy.extensions_validated");
        
            Console.WriteLine("Signing validation test: \n {0}", results);

            engine.Dispose();

            w.Stop();
            var evalTicks = w.ElapsedTicks;

            Console.WriteLine("Engine creation took {0} msecs", (newEngineTicks * nanosecPerTick) / (1000.0 * 1000.0));
            Console.WriteLine("Load policies and data took {0} msecs", (loadPoliciesTicks * nanosecPerTick) / (1000.0 * 1000.0));
            Console.WriteLine("EvalQuery and print results took {0} msecs", (evalTicks * nanosecPerTick) / (1000.0 * 1000.0));
        }
    }
}

