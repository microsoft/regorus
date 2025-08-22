using System;

namespace Benchmarks
{
    class Program
    {
        static void Main(string[] args)
        {
            Console.WriteLine("=== Regorus C# Benchmarks ===\n");
            
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
            
            Console.WriteLine("\n=== Benchmarks Complete ===");
        }
    }
}
