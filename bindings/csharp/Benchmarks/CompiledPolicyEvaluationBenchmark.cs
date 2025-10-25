using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Regorus;

namespace Benchmarks
{
    public class CompiledPolicyEvaluationBenchmark
    {
        private static readonly string TestDataPath = Path.Combine(
            Directory.GetCurrentDirectory(), 
            "..", "..", "..",
            "benches", "evaluation", "test_data"
        );

        private static readonly (string PolicyFile, string[] InputFiles)[] PolicyInputFiles = new[]
        {
            ("rbac_policy.rego", new[] { "rbac_input.json", "rbac_input2.json", "rbac_input3.json" }),
            ("api_access_policy.rego", new[] { "api_access_input.json", "api_access_input2.json", "api_access_input3.json" }),
            ("data_sensitivity_policy.rego", new[] { "data_sensitivity_input.json", "data_sensitivity_input2.json", "data_sensitivity_input3.json" }),
            ("time_based_policy.rego", new[] { "time_based_input.json", "time_based_input2.json", "time_based_input3.json" }),
            ("data_processing_policy.rego", new[] { "data_processing_input.json", "data_processing_input2.json", "data_processing_input3.json" }),
            ("azure_vm_policy.rego", new[] { "azure_vm_input.json", "azure_vm_input2.json", "azure_vm_input3.json" }),
            ("azure_storage_policy.rego", new[] { "azure_storage_input.json", "azure_storage_input2.json", "azure_storage_input3.json" }),
            ("azure_keyvault_policy.rego", new[] { "azure_keyvault_input.json", "azure_keyvault_input2.json", "azure_keyvault_input3.json" }),
            ("azure_nsg_policy.rego", new[] { "azure_nsg_input.json", "azure_nsg_input2.json", "azure_nsg_input3.json" })
        };

        private static readonly string[] PolicyNames = new[]
        {
            "rbac_policy",
            "api_access_policy", 
            "data_sensitivity_policy",
            "time_based_policy",
            "data_processing_policy",
            "azure_vm_policy",
            "azure_storage_policy",
            "azure_keyvault_policy",
            "azure_nsg_policy"
        };

        private static List<(string Policy, string[] Inputs)> LoadPoliciesWithInputs()
        {
            var result = new List<(string Policy, string[] Inputs)>();
            
            foreach (var (policyFile, inputFiles) in PolicyInputFiles)
            {
                var policyPath = Path.Combine(TestDataPath, "policies", policyFile);
                var policy = File.ReadAllText(policyPath);
                
                var inputs = inputFiles.Select(inputFile =>
                {
                    var inputPath = Path.Combine(TestDataPath, "inputs", inputFile);
                    return File.ReadAllText(inputPath);
                }).ToArray();
                
                result.Add((policy, inputs));
            }
            
            return result;
        }

        private static List<CompiledPolicy> PrepareSharedCompiledPolicies()
        {
            var policiesWithInputs = LoadPoliciesWithInputs();
            var compiledPolicies = new List<CompiledPolicy>();
            
            foreach (var (policy, _) in policiesWithInputs)
            {
                var modules = new[] { new PolicyModule { Id = "policy.rego", Content = policy } };
                var compiled = Compiler.CompilePolicyWithEntrypoint("{}", modules, "data.bench.allow");
                compiledPolicies.Add(compiled);
            }
            
            return compiledPolicies;
        }

        public static void RunCompiledPolicyEvaluationBenchmark()
        {
            var cpuCount = Environment.ProcessorCount;
            var maxThreads = cpuCount * 2;
            var threadCounts = new List<int> { 1, 2 };
            
            // Add even numbers from 4 to maxThreads
            for (int i = 4; i <= maxThreads; i += 2)
            {
                threadCounts.Add(i);
            }
            
            Console.WriteLine($"Running compiled policy benchmark with max_threads: {maxThreads}");
            Console.WriteLine($"Testing with thread counts: {string.Join(", ", threadCounts)}");
            Console.WriteLine();

            // Benchmark both shared policies and per-iteration compilation
            var configurations = new[]
            {
                (true, "compiled_shared_policies"),
                (false, "compiled_per_iteration")
            };

            foreach (var (useSharedPolicies, groupName) in configurations)
            {
                Console.WriteLine($"=== {groupName} ===");

                foreach (var threads in threadCounts)
                {
                    RunCompiledPolicyBenchmark(threads, useSharedPolicies, groupName);
                }
                Console.WriteLine();
            }
        }

        public static void RunCompiledPolicyBenchmark(int threads, bool useSharedPolicies, string groupName)
        {
            const int warmupSeconds = 3;
            const int durationSeconds = 3;
            var policiesWithInputs = LoadPoliciesWithInputs();
            List<CompiledPolicy>? compiledPolicies = null;
            
            if (useSharedPolicies)
            {
                compiledPolicies = PrepareSharedCompiledPolicies();
            }
            
            Console.WriteLine($"Warming up with {threads} threads for {warmupSeconds} seconds...");
            
            // Warmup phase
            var (_, _, _, _) = RunBenchmarkPhase(threads, warmupSeconds, policiesWithInputs, compiledPolicies, useSharedPolicies, isWarmup: true);
            
            Console.WriteLine($"Running benchmark with {threads} threads for {durationSeconds} seconds...");
            
            // Actual benchmark phase
            var (totalEvaluations, evaluationTime, policyCounters, allocatedBytes) = RunBenchmarkPhase(threads, durationSeconds, policiesWithInputs, compiledPolicies, useSharedPolicies, isWarmup: false);

            // Calculate throughput based on pure evaluation time (consistent with Rust benchmark)
            var evalsPerSecond = totalEvaluations / evaluationTime.TotalSeconds;
            var kelemsPerSecond = evalsPerSecond / 1000.0;

            Console.WriteLine($"{groupName}/eval/{threads} threads");
            Console.WriteLine($"                        time:   [{evaluationTime.TotalMilliseconds:F2} ms]");
            Console.WriteLine($"                        thrpt:  [{kelemsPerSecond:F2} Kelem/s]");

            if (totalEvaluations > 0)
            {
                var bytesPerEval = allocatedBytes / (double)totalEvaluations;
                Console.WriteLine($"                        alloc:  [{bytesPerEval:F2} B/op] (total {allocatedBytes} B)");
            }

            // Clean up compiled policies if we created them
            if (compiledPolicies != null)
            {
                foreach (var policy in compiledPolicies)
                {
                    policy.Dispose();
                }
            }

            // Verify that all policies were evaluated
            var allEvaluated = policyCounters.Values.All(count => count > 0);

            if (allEvaluated)
            {
                Console.WriteLine("✓ All policies were evaluated successfully");
            }
            else
            {
                Console.WriteLine("ERROR: Some policies were never evaluated successfully!");
            }
        }

        private static (int totalEvaluations, TimeSpan evaluationTime, Dictionary<string, int> policyCounters, long allocatedBytes) RunBenchmarkPhase(
            int threads, 
            int durationSeconds, 
            List<(string Policy, string[] Inputs)> policiesWithInputs,
            List<CompiledPolicy>? compiledPolicies,
            bool useSharedPolicies,
            bool isWarmup)
        {
            var barrier = new Barrier(threads);
            var tasks = new Task[threads];
            var policyCounters = new Dictionary<string, int>();
            var evaluationTimes = new Dictionary<int, TimeSpan>();
            var lockObject = new object();
            var stopExecution = false;
            long allocatedBytes = 0;

            // Initialize counters
            foreach (var policyName in PolicyNames)
            {
                policyCounters[policyName] = 0;
            }

            var stopwatch = Stopwatch.StartNew();

            for (int threadId = 0; threadId < threads; threadId++)
            {
                int tid = threadId;
                tasks[threadId] = Task.Run(() =>
                {
                    long allocationStart = 0;
                    if (!isWarmup)
                    {
                        allocationStart = GC.GetAllocatedBytesForCurrentThread();
                    }

                    barrier.SignalAndWait();
                    
                    int evaluationCount = 0;
                    var localEvaluationTime = TimeSpan.Zero;
                    
                    while (!stopExecution)
                    {
                        // Use different policy for each iteration
                        int policyIdx = (tid + evaluationCount) % policiesWithInputs.Count;
                        var (policy, inputs) = policiesWithInputs[policyIdx];

                        // Use different input for the same policy based on iteration
                        int inputIdx = evaluationCount % inputs.Length;
                        var input = inputs[inputIdx];

                        try
                        {
                            // Measure only the evaluation call
                            var evalStopwatch = Stopwatch.StartNew();
                            
                            if (useSharedPolicies)
                            {
                                var result = compiledPolicies![policyIdx].EvalWithInput(input);
                            }
                            else
                            {
                                // Compile policy in each iteration
                                var modules = new[] { new PolicyModule { Id = "policy.rego", Content = policy } };
                                var compiled = Compiler.CompilePolicyWithEntrypoint("{}", modules, "data.bench.allow");
                                var result = compiled.EvalWithInput(input);
                                compiled.Dispose();
                            }
                            
                            evalStopwatch.Stop();
                            localEvaluationTime += evalStopwatch.Elapsed;
                            
                            // Track successful evaluations (only during actual benchmark, not warmup)
                            if (!isWarmup)
                            {
                                lock (lockObject)
                                {
                                    policyCounters[PolicyNames[policyIdx]]++;
                                }
                            }
                        }
                        catch (Exception)
                        {
                            // Ignore evaluation errors for benchmarking purposes
                        }
                        
                        evaluationCount++;
                    }
                    
                    // Store the actual evaluation time for this thread
                    if (!isWarmup)
                    {
                        lock (lockObject)
                        {
                            if (!evaluationTimes.ContainsKey(tid))
                                evaluationTimes[tid] = TimeSpan.Zero;
                            evaluationTimes[tid] = localEvaluationTime;
                        }

                        var allocationEnd = GC.GetAllocatedBytesForCurrentThread();
                        System.Threading.Interlocked.Add(ref allocatedBytes, allocationEnd - allocationStart);
                    }
                });
            }

            // Stop execution after the specified duration
            Task.Delay(TimeSpan.FromSeconds(durationSeconds)).ContinueWith(_ => stopExecution = true);

            Task.WaitAll(tasks);
            stopwatch.Stop();

            var totalEvaluations = policyCounters.Values.Sum();
            var totalEvaluationTime = evaluationTimes.Values.Aggregate(TimeSpan.Zero, (sum, time) => sum + time);
            
            // Use pure evaluation time (consistent with Rust benchmark)
            var evaluationTime = totalEvaluationTime == TimeSpan.Zero ? stopwatch.Elapsed : totalEvaluationTime;
            
            return (totalEvaluations, evaluationTime, policyCounters, allocatedBytes);
        }
    }
}
