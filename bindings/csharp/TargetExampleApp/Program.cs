// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

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
}
