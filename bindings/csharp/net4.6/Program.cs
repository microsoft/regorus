using System;
using System.Text;
using System.Text.Json;
using System.Diagnostics;

namespace regoregorus_test
{
    class Program
    {
        static void Main(string[] args)
        {
            long nanosecPerTick = (1000L * 1000L * 1000L) / Stopwatch.Frequency;
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
            engine.AddPolicyFromFile("../../../examples/extension_list/extension_policy.rego");
            engine.AddDataFromJsonFile("../../../examples/extension_list/extension-data.json");


            w.Stop();
            var loadPoliciesTicks = w.ElapsedTicks;


            w.Restart();

            // Set input and eval query.
            engine.SetInputFromJsonFile("../../../examples/extension_list/extension-input.json");
            var results = engine.EvalQuery("data.extension_policy.allowed_extensions");
            var resultsDoc = System.Text.Json.JsonDocument.Parse(results);

            w.Stop();
            var evalTicks = w.ElapsedTicks;

            Console.WriteLine("{0}", results);


            Console.WriteLine("Engine creation took {0} msecs", (newEngineTicks * nanosecPerTick) / (1000.0 * 1000.0));
            Console.WriteLine("Load policies and data took {0} msecs", (loadPoliciesTicks * nanosecPerTick) / (1000.0 * 1000.0));
            Console.WriteLine("EvalQuery took {0} msecs", (evalTicks * nanosecPerTick) / (1000.0 * 1000.0));
        }
    }
}

