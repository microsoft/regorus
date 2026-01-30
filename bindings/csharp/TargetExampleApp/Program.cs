// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System.Linq;
using System.Text.Json;

namespace TargetExampleApp;

class Program
{
    // Policy definition constants
    private const string AZURE_STORAGE_POLICY_DEFINITION = @"
package policy

import rego.v1

# Target declaration for Azure Policy
__target__ := ""target.tests.azure_policy""

default parameters.requiredTLSVersion = """"
default parameters.allowedPorts = []

# Policy rules for storage accounts
default allow := false

# Allow storage accounts with HTTPS-only traffic and proper encryption
allow if {
    input.type == ""Microsoft.Storage/storageAccounts""
    input.properties.supportsHttpsTrafficOnly == true
    input.properties.encryption.services.blob.enabled == true
    input.properties.minimumTlsVersion in [parameters.requiredTLSVersion]
}

# Allow network security groups with proper inbound rules
allow if {
    input.type == ""Microsoft.Network/networkSecurityGroups""
    count([rule | 
        rule := input.properties.securityRules[_]
        rule.properties.direction == ""Inbound""
        rule.properties.access == ""Allow""
        rule.properties.sourceAddressPrefix == ""*""
        rule.properties.destinationPortRange in [parameters.allowedPorts]
    ]) == 0
}";

    private const string AZURE_STORAGE_POLICY_ASSIGNMENT = @"
package policy

import rego.v1

parameters.requiredTLSVersion = ""TLS1_2""
parameters.allowedPorts = [""22"", ""3389""]";

    private const string EXECUTION_TIMER_POLICY = @"
package limits.timer
import rego.v1

triplet_count := count([1 |
    x := data.values[_]
    y := data.values[_]
    z := data.values[_]
])
";

    private const string EXECUTION_TIMER_QUERY = "data.limits.timer.triplet_count";
    private const int EXECUTION_TIMER_VALUE_COUNT = 40;

        private const string RVM_POLICY = """
package demo
import rego.v1

default allow := false

allow if {
        input.user == "alice"
        some role in data.roles[input.user]
        role == "admin"
}
""";

        private const string RVM_DATA = """
{
    "roles": {
        "alice": ["admin", "reader"]
    }
}
""";

        private const string RVM_INPUT = """
{
    "user": "alice"
}
""";

        private const string HOST_AWAIT_POLICY = """
package demo
import rego.v1

default allow := false

allow if {
    input.account.active == true
    details := __builtin_host_await(input.account.id, "account")
    details.tier == "gold"
}
""";

        private const string HOST_AWAIT_INPUT = """
    {
        "account": {
            "id": "acct-1",
            "active": true
        }
    }
    """;

    // Test data constants
    private const string COMPLIANT_STORAGE_ACCOUNT = @"{
  ""type"": ""Microsoft.Storage/storageAccounts"",
  ""name"": ""compliantstorageacct"",
  ""location"": ""eastus"",
  ""kind"": ""StorageV2"",
  ""properties"": {
    ""supportsHttpsTrafficOnly"": true,
    ""minimumTlsVersion"": ""TLS1_2"",
    ""allowBlobPublicAccess"": false,
    ""encryption"": {
      ""services"": {
        ""blob"": { ""enabled"": true },
        ""file"": { ""enabled"": true }
      }
    }
  },
  ""tags"": {
    ""environment"": ""production""
  }
}";

    private const string NON_COMPLIANT_STORAGE_ACCOUNT = @"{
  ""type"": ""Microsoft.Storage/storageAccounts"",
  ""name"": ""insecurestorageacct"",
  ""location"": ""westus"",
  ""kind"": ""Storage"",
  ""properties"": {
    ""supportsHttpsTrafficOnly"": false,
    ""minimumTlsVersion"": ""TLS1_0"",
    ""allowBlobPublicAccess"": true,
    ""encryption"": {
      ""services"": {
        ""blob"": { ""enabled"": false },
        ""file"": { ""enabled"": false }
      }
    }
  }
}";

    static void Main(string[] args)
    {
        Console.WriteLine("=== Regorus Target Example Application ===\n");

        try
        {
            DemonstrateTargetFunctionality();
            Console.WriteLine("\n=== Target demonstration completed successfully! ===");
        }
        catch (Exception ex)
        {
            Console.WriteLine($"Error: {ex.Message}");
            Environment.Exit(1);
        }
    }

    static void DemonstrateTargetFunctionality()
    {
        Console.WriteLine("REGORUS TARGET FUNCTIONALITY DEMONSTRATION");
        Console.WriteLine("==========================================");

        // 1. Register target using JSON from file
        var targetJsonPath = Path.Combine(AppContext.BaseDirectory, "azure_policy.target.json");
        var targetJson = File.ReadAllText(targetJsonPath);

        Console.WriteLine("1. Registering target from JSON file:");
        Console.WriteLine(targetJson);

        Regorus.TargetRegistry.RegisterFromJson(targetJson);
        Console.WriteLine($"Target registered. Registry contains {Regorus.TargetRegistry.Count} target(s)");
        Console.WriteLine($"Registered targets: {Regorus.TargetRegistry.ListNames()}");

        // 2. Compile policy for target
        var policyModules = new List<Regorus.PolicyModule>
        {
            new Regorus.PolicyModule($"definition-{Guid.NewGuid():N}", AZURE_STORAGE_POLICY_DEFINITION),
            new Regorus.PolicyModule($"assignment-{Guid.NewGuid():N}", AZURE_STORAGE_POLICY_ASSIGNMENT)
        };

        var policyDataJson = "{}";

        Console.WriteLine("\n2. Compiling policy for target...");
        using var compiledPolicy = Regorus.Compiler.CompilePolicyForTarget(policyDataJson, policyModules);
        Console.WriteLine("Policy compiled successfully!");

        // 2.5. Demonstrate policy information retrieval
        Console.WriteLine("\n2.5. Retrieving policy information:");
        DemonstratePolicyInfo(compiledPolicy);

        // 3. Evaluate with different inputs
        Console.WriteLine("\n3. Testing policy evaluation:");
        Console.WriteLine("Compliant storage account:");
        Console.WriteLine(COMPLIANT_STORAGE_ACCOUNT);

        var compliantResult = compiledPolicy.EvalWithInput(COMPLIANT_STORAGE_ACCOUNT);
        Console.WriteLine($"Result: {compliantResult}");

        Console.WriteLine("\nNon-compliant storage account:");
        Console.WriteLine(NON_COMPLIANT_STORAGE_ACCOUNT);

        var nonCompliantResult = compiledPolicy.EvalWithInput(NON_COMPLIANT_STORAGE_ACCOUNT);
        Console.WriteLine($"Result: {nonCompliantResult}");
        
        // 4. Demonstrate thread-safe concurrent evaluation
        Console.WriteLine("\n4. Testing concurrent evaluation from multiple threads:");
        DemonstrateConcurrentEvaluation(compiledPolicy);

        Console.WriteLine("\n5. Execution timer configuration:");
        DemonstrateExecutionTimer();

        Console.WriteLine("\n6. RVM program execution:");
        DemonstrateRvmUsage();

        Console.WriteLine("\n7. RVM program compilation from engine:");
        DemonstrateRvmCompileFromEngine();

        Console.WriteLine("\n8. RVM host await (suspend/resume):");
        DemonstrateRvmHostAwait();
    }

    static void DemonstrateConcurrentEvaluation(Regorus.CompiledPolicy compiledPolicy)
    {
        var testInputs = new[]
        {
            ("Thread-1-Compliant", COMPLIANT_STORAGE_ACCOUNT),
            ("Thread-2-NonCompliant", NON_COMPLIANT_STORAGE_ACCOUNT),
            ("Thread-3-Compliant", COMPLIANT_STORAGE_ACCOUNT.Replace("compliantstorageacct", "thread3storage")),
            ("Thread-4-NonCompliant", NON_COMPLIANT_STORAGE_ACCOUNT.Replace("insecurestorageacct", "thread4storage")),
            ("Thread-5-Compliant", COMPLIANT_STORAGE_ACCOUNT.Replace("compliantstorageacct", "thread5storage"))
        };

        Console.WriteLine($"Starting {testInputs.Length} concurrent evaluations...");
        
        var tasks = testInputs.Select(input => 
            Task.Run(() => {
                var (threadName, json) = input;
                var stopwatch = System.Diagnostics.Stopwatch.StartNew();
                
                // Multiple evaluations per thread to stress test
                var results = new List<string>();
                for (int i = 0; i < 1000; i++)
                {
                    var result = compiledPolicy.EvalWithInput(json);
                    results.Add(result);
                }
                
                stopwatch.Stop();
                var microseconds = stopwatch.ElapsedTicks * 1000000 / System.Diagnostics.Stopwatch.Frequency;
                
                // Verify all results are identical (thread safety)
                var firstResult = results[0];
                var allIdentical = results.All(r => r == firstResult);
                
                Console.WriteLine($"✓ {threadName}: {results.Count} evaluations in {microseconds}μs, " +
                                $"Results consistent: {allIdentical}");
                
                return (threadName, results.Count, microseconds, allIdentical);
            })
        ).ToArray();

        // Wait for all threads to complete
        var results = Task.WhenAll(tasks).Result;
        
        Console.WriteLine("\nConcurrency test results:");
        var totalEvaluations = results.Sum(r => r.Item2);
        var maxTime = results.Max(r => r.Item3);
        var allConsistent = results.All(r => r.allIdentical);
        
        Console.WriteLine($"✓ Total evaluations: {totalEvaluations}");
        Console.WriteLine($"✓ Max thread time: {maxTime}μs");
        Console.WriteLine($"✓ All threads consistent: {allConsistent}");
        Console.WriteLine($"✓ Approximate throughput: {totalEvaluations * 1000000.0 / maxTime:F0} evaluations/second");
        Console.WriteLine("✓ No locks required - CompiledPolicy is thread-safe!");
    }

    static void DemonstratePolicyInfo(Regorus.CompiledPolicy compiledPolicy)
    {
        Console.WriteLine("Getting policy metadata using GetPolicyInfo()...");
        
        try
        {
            var policyInfo = compiledPolicy.GetPolicyInfo();
            
            Console.WriteLine($"✓ Policy Information Retrieved:");
            Console.WriteLine($"  Target Name: {policyInfo.TargetName ?? "None"}");
            Console.WriteLine($"  Effect Rule: {policyInfo.EffectRule ?? "None"}");
            Console.WriteLine($"  Entrypoint Rule: {policyInfo.EntrypointRule}");
            
            Console.WriteLine($"  Module IDs ({policyInfo.ModuleIds.Count}):");
            foreach (var moduleId in policyInfo.ModuleIds)
            {
                Console.WriteLine($"    - {moduleId}");
            }
            
            Console.WriteLine($"  Applicable Resource Types ({policyInfo.ApplicableResourceTypes.Count}):");
            foreach (var resourceType in policyInfo.ApplicableResourceTypes)
            {
                Console.WriteLine($"    - {resourceType}");
            }
            
            if (policyInfo.Parameters != null && policyInfo.Parameters.Count > 0)
            {
                Console.WriteLine($"  Policy Parameters:");
                foreach (var parameterSet in policyInfo.Parameters)
                {
                    Console.WriteLine($"    From '{parameterSet.SourceFile}':");
                    Console.WriteLine($"      Parameters ({parameterSet.Parameters.Count}):");
                    foreach (var param in parameterSet.Parameters)
                    {
                        Console.WriteLine($"        - {param.Name} ({param.Type})");
                        if (param.Default != null)
                        {
                            Console.WriteLine($"          Default: {param.Default}");
                        }
                        if (!string.IsNullOrEmpty(param.Description))
                        {
                            Console.WriteLine($"          Description: {param.Description}");
                        }
                    }
                    
                    if (parameterSet.Modifiers.Count > 0)
                    {
                        Console.WriteLine($"      Modifiers ({parameterSet.Modifiers.Count}):");
                        foreach (var modifier in parameterSet.Modifiers)
                        {
                            Console.WriteLine($"        - {modifier.Name}: {modifier.Value}");
                        }
                    }
                }
            }
            else
            {
                Console.WriteLine("  No parameter information available");
            }
            
            // Demonstrate JSON serialization of policy info
            Console.WriteLine("\n✓ Policy Info as JSON:");
            var jsonOptions = new JsonSerializerOptions 
            { 
                WriteIndented = true,
                PropertyNamingPolicy = JsonNamingPolicy.CamelCase
            };
            var policyInfoJson = JsonSerializer.Serialize(policyInfo, jsonOptions);
            Console.WriteLine(policyInfoJson);
        }
        catch (Exception ex)
        {
            Console.WriteLine($"✗ Failed to get policy info: {ex.Message}");
        }
    }

    static void DemonstrateExecutionTimer()
    {
        var dataJson = JsonSerializer.Serialize(new
        {
            values = Enumerable.Range(0, EXECUTION_TIMER_VALUE_COUNT).ToArray()
        });

        var fallback = new Regorus.ExecutionTimerConfig(TimeSpan.FromMilliseconds(2), checkInterval: 1);
        var relaxed = new Regorus.ExecutionTimerConfig(TimeSpan.FromMilliseconds(1000), checkInterval: 1);

        Console.WriteLine($"  Configuring fallback timer (limit={fallback.Limit.TotalMilliseconds:F0} ms, interval={fallback.CheckInterval})...");

        Regorus.Engine.SetFallbackExecutionTimerConfig(fallback);
        try
        {
            using var engine = new Regorus.Engine();
            engine.AddPolicy("limits_timer.rego", EXECUTION_TIMER_POLICY);
            engine.AddDataJson(dataJson);

            Console.WriteLine("  Evaluating under fallback limit (expected failure)...");
            try
            {
                engine.EvalRule(EXECUTION_TIMER_QUERY);
                Console.WriteLine("  ⚠ Evaluation unexpectedly succeeded under fallback limit.");
            }
            catch (Exception ex)
            {
                Console.WriteLine($"  ✓ Fallback enforced: {ex.Message}");
            }

            Console.WriteLine($"  Applying per-engine override ({relaxed.Limit.TotalMilliseconds:F0} ms) and retrying...");
            engine.SetExecutionTimerConfig(relaxed);
            var result = engine.EvalRule(EXECUTION_TIMER_QUERY);
            Console.WriteLine($"  ✓ Override succeeded; triplet_count = {result}");

            Console.WriteLine("  Clearing engine override to restore fallback...");
            engine.ClearExecutionTimerConfig();
            try
            {
                engine.EvalRule(EXECUTION_TIMER_QUERY);
                Console.WriteLine("  ⚠ Evaluation unexpectedly succeeded after clearing override.");
            }
            catch (Exception ex)
            {
                Console.WriteLine($"  ✓ Fallback restored: {ex.Message}");
            }
        }
        finally
        {
            Regorus.Engine.ClearFallbackExecutionTimerConfig();
        }
    }

    static void DemonstrateRvmUsage()
    {
        var modules = new List<Regorus.PolicyModule>
        {
            new Regorus.PolicyModule("demo.rego", RVM_POLICY)
        };
        var entryPoints = new[] { "data.demo.allow" };

        using var program = Regorus.Program.CompileFromModules(RVM_DATA, modules, entryPoints);
        var binary = program.SerializeBinary();
        using var rehydrated = Regorus.Program.DeserializeBinary(binary, out var isPartial);
        if (isPartial)
        {
            throw new InvalidOperationException("RVM program deserialization returned a partial program.");
        }

        Console.WriteLine($"Serialized program size: {binary.Length} bytes");

        var listing = rehydrated.GenerateListing();

        Console.WriteLine("RVM listing:");
        Console.WriteLine(listing);

        using var vm = new Regorus.Rvm();
        vm.LoadProgram(rehydrated);
        vm.SetDataJson(RVM_DATA);
        vm.SetInputJson(RVM_INPUT);

        var result = vm.Execute();
        Console.WriteLine($"RVM result: {result}");
    }

    static void DemonstrateRvmCompileFromEngine()
    {
        using var engine = new Regorus.Engine();
        engine.AddPolicy("demo.rego", RVM_POLICY);
        engine.AddDataJson(RVM_DATA);

        var entryPoints = new[] { "data.demo.allow" };
        using var program = Regorus.Program.CompileFromEngine(engine, entryPoints);

        using var vm = new Regorus.Rvm();
        vm.LoadProgram(program);
        vm.SetDataJson(RVM_DATA);
        vm.SetInputJson(RVM_INPUT);

        var result = vm.ExecuteEntryPoint("data.demo.allow");
        Console.WriteLine($"RVM result from engine-compiled program: {result}");
    }

    static void DemonstrateRvmHostAwait()
    {
        var modules = new List<Regorus.PolicyModule>
        {
            new Regorus.PolicyModule("host_await.rego", HOST_AWAIT_POLICY)
        };
        var entryPoints = new[] { "data.demo.allow" };

        using var program = Regorus.Program.CompileFromModules("{}", modules, entryPoints);
        using var vm = new Regorus.Rvm();
        vm.SetExecutionMode(1);
        vm.LoadProgram(program);
        vm.SetInputJson(HOST_AWAIT_INPUT);

        var initial = vm.Execute();
        var state = vm.GetExecutionState();
        Console.WriteLine($"HostAwait initial result: {initial}");
        Console.WriteLine($"Execution state: {state}");

        var resumed = vm.Resume("{\"tier\":\"gold\"}");
        Console.WriteLine($"HostAwait resumed result: {resumed}");
    }
}
