using System;

namespace Benchmarks
{
    class Program
    {
        static void Main(string[] args)
        {
            Console.WriteLine("=== Regorus C# Benchmarks ===\n");

            // If "azure-policy-json" is passed, run only that benchmark.
            if (args.Length > 0 && args[0] == "azure-policy-json")
            {
                AzurePolicyJsonBenchmark.RunBenchmark();
                return;
            }

            // If "multi-policy" is passed, run the multi-policy benchmark.
            if (args.Length > 0 && args[0] == "multi-policy")
            {
                MultiPolicyBenchmark.RunBenchmark();
                return;
            }

            try
            {
                Console.WriteLine("Running Engine Evaluation Benchmark...");
                EngineEvaluationBenchmark.RunEngineEvaluationBenchmark();
            }
            catch (Exception ex)
            {
                Console.WriteLine($"Engine benchmark failed: {ex.Message}");
            }

            Console.WriteLine("\n" + new string('=', 80) + "\n");

            try
            {
                Console.WriteLine("Running Compiled Policy Evaluation Benchmark...");
                CompiledPolicyEvaluationBenchmark.RunCompiledPolicyEvaluationBenchmark();
            }
            catch (Exception ex)
            {
                Console.WriteLine($"Compiled policy benchmark failed: {ex.Message}");
            }

            Console.WriteLine("\n" + new string('=', 80) + "\n");

            try
            {
                Console.WriteLine("Running Azure Policy JSON Benchmark...");
                AzurePolicyJsonBenchmark.RunBenchmark();
            }
            catch (Exception ex)
            {
                Console.WriteLine($"Azure Policy JSON benchmark failed: {ex.Message}");
            }

            Console.WriteLine("\n=== Benchmarks Complete ===");
        }
    }
}
