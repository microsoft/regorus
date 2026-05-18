// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.Json;
using Regorus;
using YamlDotNet.RepresentationModel;

namespace Benchmarks
{
    /// <summary>
    /// Multi-policy benchmark that loads diverse real-world Azure Policy definitions
    /// from the regorus test suite YAML files and benchmarks each one.
    ///
    /// Also verifies that the evaluation results match the expected effects from
    /// the test cases, ensuring correctness across Rust, C# FFI, and PolicyService.
    /// </summary>
    public static class MultiPolicyBenchmark
    {
        // -------------------------------------------------------------------
        // Policy definitions to benchmark (paths relative to tests/azure_policy/cases/)
        // -------------------------------------------------------------------

        private static readonly (string FileName, string Label, string? ExpectedNote)[] Policies = new[]
        {
            ("e2e_nsg_rdp_access.yaml", "NSG RDP (count/wildcards)", "audit_exact_port_3389_from_internet"),
            ("e2e_storage_vnet_rules.yaml", "Storage VNet (count/allOf/anyOf)", "audit_default_action_allow"),
            ("e2e_cmk_disk_encryption.yaml", "CMK Disk Encrypt (huge anyOf/like/in)", "pass_vm_osdisk_with_cmk"),
            ("e2e_cosmos_max_throughput.yaml", "Cosmos MaxThroughput (greaterOrEquals)", "deny_sql_db_throughput_exceeds_max"),
            ("e2e_storage_ip_allowlist.yaml", "Storage IP Allowlist (count.where/notIn)", (string?)null),
            ("e2e_tags_inherit_modify.yaml", "Tags Inherit (modify/resourceGroup)", "modify_tag_differs"),
        };

        private static readonly string ProviderCachePath =
            Environment.GetEnvironmentVariable("PROVIDER_CACHE_JSON")
            ?? Path.Combine(Directory.GetCurrentDirectory(), "..", "..", "..", "..", "..", "provider-cache.json");

        // -------------------------------------------------------------------
        // Prepared policy for benchmarking
        // -------------------------------------------------------------------

        private class PreparedPolicy : IDisposable
        {
            public string Label { get; init; } = "";
            public Regorus.Program Program { get; init; } = null!;
            public string InputJson { get; init; } = "";
            public string ContextJson { get; init; } = "{}";
            public string? Effect { get; set; }
            public string? ExpectedEffect { get; set; }

            public void Dispose()
            {
                Program?.Dispose();
            }
        }

        // -------------------------------------------------------------------
        // Entry point
        // -------------------------------------------------------------------

        public static void RunBenchmark()
        {
            const int warmup = 100;
            const int iterations = 1000;

            Console.WriteLine("=== Multi-Policy Benchmark (C# FFI) ===\n");

            var casesDir = FindCasesDir();
            Console.WriteLine($"  Test cases: {casesDir}");

            // Load the full alias catalog.
            Console.WriteLine($"  Loading aliases from {ProviderCachePath}...");
            using var fullRegistry = new AliasRegistry();
            fullRegistry.LoadJson(File.ReadAllText(ProviderCachePath));

            // Prepare all policies.
            var policies = new List<PreparedPolicy>();
            foreach (var (fileName, label, expectedNote) in Policies)
            {
                try
                {
                    var prepared = PreparePolicy(casesDir, fileName, label, expectedNote, fullRegistry);
                    policies.Add(prepared);
                }
                catch (Exception ex)
                {
                    Console.WriteLine($"  SKIP {label}: {ex.Message}");
                }
            }

            // Also add the KeyVault policy (same as single-policy benchmark).
            policies.Insert(0, PrepareKeyVaultPolicy(fullRegistry));

            Console.WriteLine();

            // Print verification results.
            Console.WriteLine("--- Verification ---");
            foreach (var p in policies)
            {
                var status = p.ExpectedEffect == null ? "?" :
                    (p.Effect == p.ExpectedEffect ? "✓" : $"✗ (expected {p.ExpectedEffect})");
                Console.WriteLine($"  {status} {p.Label}: {p.Effect ?? "null"}");
            }
            Console.WriteLine();

            // Hot eval benchmark.
            Console.WriteLine("--- multi_policy/hot_eval ---");
            foreach (var p in policies)
            {
                using var vm = new Rvm();
                vm.LoadProgram(p.Program);
                vm.SetContextJson(p.ContextJson);

                // Warmup.
                for (int i = 0; i < warmup; i++)
                {
                    vm.SetInputJson(p.InputJson);
                    vm.ExecuteEntryPoint("main");
                }

                var timings = new double[iterations];
                var sw = new Stopwatch();
                for (int i = 0; i < iterations; i++)
                {
                    sw.Restart();
                    vm.SetInputJson(p.InputJson);
                    vm.ExecuteEntryPoint("main");
                    sw.Stop();
                    timings[i] = sw.Elapsed.TotalMicroseconds;
                }

                DisplayResults($"hot_eval/{p.Label}", timings, warmup, iterations);
            }

            // Cold eval benchmark.
            Console.WriteLine("--- multi_policy/cold_eval ---");
            foreach (var p in policies)
            {
                // Warmup.
                for (int i = 0; i < warmup; i++)
                {
                    using var vm = new Rvm();
                    vm.LoadProgram(p.Program);
                    vm.SetContextJson(p.ContextJson);
                    vm.SetInputJson(p.InputJson);
                    vm.ExecuteEntryPoint("main");
                }

                var timings = new double[iterations];
                var sw = new Stopwatch();
                for (int i = 0; i < iterations; i++)
                {
                    sw.Restart();
                    using var vm = new Rvm();
                    vm.LoadProgram(p.Program);
                    vm.SetContextJson(p.ContextJson);
                    vm.SetInputJson(p.InputJson);
                    vm.ExecuteEntryPoint("main");
                    sw.Stop();
                    timings[i] = sw.Elapsed.TotalMicroseconds;
                }

                DisplayResults($"cold_eval/{p.Label}", timings, warmup, iterations);
            }

            // Cleanup.
            foreach (var p in policies) p.Dispose();
        }

        // -------------------------------------------------------------------
        // Prepare a policy from a YAML test file
        // -------------------------------------------------------------------

        private static PreparedPolicy PreparePolicy(
            string casesDir,
            string fileName,
            string label,
            string? expectedNote,
            AliasRegistry fullRegistry)
        {
            var yamlPath = Path.Combine(casesDir, fileName);
            var yamlStr = File.ReadAllText(yamlPath);

            // Parse YAML.
            var yaml = new YamlStream();
            yaml.Load(new StringReader(yamlStr));
            var root = (YamlMappingNode)yaml.Documents[0].RootNode;

            // Get top-level policy_definition or policy_rule.
            string? topPolicyDef = GetScalar(root, "policy_definition");
            string? topPolicyRule = GetScalar(root, "policy_rule");

            // Load test-specific aliases for normalization.
            AliasRegistry? testRegistry = null;
            var aliasesFile = GetScalar(root, "aliases");
            if (aliasesFile != null)
            {
                var aliasesDir = Path.Combine(casesDir, "..", "aliases");
                var aliasesPath = Path.Combine(aliasesDir, aliasesFile);
                testRegistry = new AliasRegistry();
                testRegistry.LoadJson(File.ReadAllText(aliasesPath));
            }

            // Find the target case.
            var cases = (YamlSequenceNode)root.Children[new YamlScalarNode("cases")];
            YamlMappingNode? targetCase = null;

            if (expectedNote != null)
            {
                targetCase = cases.Children
                    .Cast<YamlMappingNode>()
                    .FirstOrDefault(c => GetScalar(c, "note") == expectedNote);
            }

            // Fall back to first non-skipped case with a resource.
            targetCase ??= cases.Children
                .Cast<YamlMappingNode>()
                .FirstOrDefault(c =>
                    GetScalar(c, "skip") != "true" &&
                    GetScalar(c, "want_parse_error") != "true" &&
                    GetScalar(c, "want_compile_error") != "true" &&
                    c.Children.ContainsKey(new YamlScalarNode("resource")));

            if (targetCase == null)
                throw new InvalidOperationException($"No benchmarkable case found in {fileName}");

            // Get policy source (case overrides top-level).
            var casePolicyDef = GetScalar(targetCase, "policy_definition");
            var casePolicyRule = GetScalar(targetCase, "policy_rule");

            string policyJson;
            bool isDefinition;
            if (casePolicyDef != null) { policyJson = casePolicyDef; isDefinition = true; }
            else if (casePolicyRule != null) { policyJson = casePolicyRule; isDefinition = false; }
            else if (topPolicyDef != null) { policyJson = topPolicyDef; isDefinition = true; }
            else if (topPolicyRule != null) { policyJson = topPolicyRule; isDefinition = false; }
            else throw new InvalidOperationException($"No policy found in {fileName}");

            // Compile.
            var program = isDefinition
                ? AzurePolicyCompiler.CompilePolicyDefinition(fullRegistry, policyJson)
                : AzurePolicyCompiler.CompilePolicyRule(fullRegistry, policyJson);

            // Build input: normalize the resource using the test-specific aliases.
            var resourceNode = targetCase.Children[new YamlScalarNode("resource")];
            var resourceJson = YamlNodeToJson(resourceNode);

            // Get parameters and context.
            string parametersJson = "{}";
            if (targetCase.Children.TryGetValue(new YamlScalarNode("parameters"), out var paramsNode))
                parametersJson = YamlNodeToJson(paramsNode);

            string contextJson = "{}";
            if (targetCase.Children.TryGetValue(new YamlScalarNode("context"), out var ctxNode))
                contextJson = YamlNodeToJson(ctxNode);

            string? apiVersion = GetScalar(targetCase, "api_version");

            // Normalize using the test-specific registry (for proper alias resolution of the
            // test resource type), falling back to the full registry.
            var normRegistry = testRegistry ?? fullRegistry;
            var envelope = normRegistry.NormalizeAndWrap(resourceJson, apiVersion, contextJson, parametersJson);

            if (envelope == null)
                throw new InvalidOperationException($"NormalizeAndWrap returned null for {fileName}");

            // Split the envelope: extract context separately (the VM needs SetContextJson).
            // The envelope has { resource, context, parameters }.
            string splitInputJson;
            string contextForVm;
            using (var envDoc = JsonDocument.Parse(envelope))
            {
                var envRoot = envDoc.RootElement;
                var resource = envRoot.GetProperty("resource").GetRawText();
                var parameters = envRoot.TryGetProperty("parameters", out var p) ? p.GetRawText() : "{}";
                splitInputJson = $"{{\"resource\":{resource},\"parameters\":{parameters}}}";
                contextForVm = envRoot.TryGetProperty("context", out var ctx) ? ctx.GetRawText() : "{}";
            }

            // Get expected effect.
            var wantEffect = GetScalar(targetCase, "want_effect");
            var wantUndefined = GetScalar(targetCase, "want_undefined");
            string? expectedEffect = null;
            if (wantUndefined == "true")
                expectedEffect = "undefined";
            else if (wantEffect != null)
                expectedEffect = wantEffect.ToLowerInvariant();

            // Sanity check: evaluate once.
            using var vm = new Rvm();
            vm.LoadProgram(program);
            vm.SetContextJson(contextForVm);
            vm.SetInputJson(splitInputJson);
            var result = vm.ExecuteEntryPoint("main");

            string? actualEffect = null;
            if (result == null || result == "<undefined>" || result == "\"<undefined>\"")
            {
                actualEffect = "undefined";
            }
            else
            {
                // Parse effect from result JSON: {"effect": "Deny"}
                try
                {
                    using var doc = JsonDocument.Parse(result);
                    if (doc.RootElement.TryGetProperty("effect", out var eff))
                        actualEffect = eff.GetString()?.ToLowerInvariant();
                    else if (doc.RootElement.TryGetProperty("details", out _))
                    {
                        // Modify effect returns details; check for effect field.
                        if (doc.RootElement.TryGetProperty("effect", out var modEff))
                            actualEffect = modEff.GetString()?.ToLowerInvariant();
                        else
                            actualEffect = "modify"; // Modify effects may not have explicit "effect" key.
                    }
                    else
                        actualEffect = result;
                }
                catch
                {
                    actualEffect = result;
                }
            }

            Console.WriteLine($"    {label}: case={GetScalar(targetCase, "note")} result={result ?? "null"}");

            testRegistry?.Dispose();

            return new PreparedPolicy
            {
                Label = label,
                Program = program,
                InputJson = splitInputJson,
                ContextJson = contextForVm,
                Effect = actualEffect,
                ExpectedEffect = expectedEffect,
            };
        }

        private static PreparedPolicy PrepareKeyVaultPolicy(AliasRegistry registry)
        {
            const string policyDef = @"{
  ""properties"": {
    ""displayName"": ""Key vaults should have soft delete enabled"",
    ""policyType"": ""BuiltIn"",
    ""mode"": ""Indexed"",
    ""parameters"": {
      ""effect"": {
        ""type"": ""String"",
        ""allowedValues"": [""Audit"", ""Deny"", ""Disabled""],
        ""defaultValue"": ""Deny""
      }
    },
    ""policyRule"": {
      ""if"": {
        ""allOf"": [
          { ""field"": ""type"", ""equals"": ""Microsoft.KeyVault/vaults"" },
          { ""not"": { ""field"": ""Microsoft.KeyVault/vaults/createMode"", ""equals"": ""recover"" } },
          { ""anyOf"": [
              { ""field"": ""Microsoft.KeyVault/vaults/enableSoftDelete"", ""exists"": ""false"" },
              { ""field"": ""Microsoft.KeyVault/vaults/enableSoftDelete"", ""equals"": ""false"" }
          ]}
        ]
      },
      ""then"": { ""effect"": ""[parameters('effect')]"" }
    }
  },
  ""id"": ""/providers/Microsoft.Authorization/policyDefinitions/1e66c121"",
  ""name"": ""1e66c121""
}";
            const string resource = @"{
    ""apiVersion"": ""2018-02-14"",
    ""name"": ""bswantestkv100"",
    ""location"": ""westus"",
    ""type"": ""Microsoft.KeyVault/vaults"",
    ""properties"": { ""sku"": { ""name"": ""Standard"", ""family"": ""A"" } },
    ""tags"": {},
    ""dependsOn"": []
}";

            var program = AzurePolicyCompiler.CompilePolicyDefinition(registry, policyDef);
            var envelope = registry.NormalizeAndWrap(resource, apiVersion: null, contextJson: "{}", parametersJson: "{}");

            // Split envelope into input and context.
            string kvInputJson;
            string kvContextJson;
            using (var envDoc = JsonDocument.Parse(envelope!))
            {
                var root = envDoc.RootElement;
                var res = root.GetProperty("resource").GetRawText();
                var parms = root.TryGetProperty("parameters", out var p) ? p.GetRawText() : "{}";
                kvInputJson = $"{{\"resource\":{res},\"parameters\":{parms}}}";
                kvContextJson = root.TryGetProperty("context", out var ctx) ? ctx.GetRawText() : "{}";
            }

            using var vm = new Rvm();
            vm.LoadProgram(program);
            vm.SetContextJson(kvContextJson);
            vm.SetInputJson(kvInputJson);
            var result = vm.ExecuteEntryPoint("main");

            string? actualEffect = null;
            if (result != null && result != "<undefined>")
            {
                try
                {
                    using var doc = JsonDocument.Parse(result);
                    if (doc.RootElement.TryGetProperty("effect", out var eff))
                        actualEffect = eff.GetString()?.ToLowerInvariant();
                }
                catch { actualEffect = result; }
            }
            else
            {
                actualEffect = "undefined";
            }

            return new PreparedPolicy
            {
                Label = "KeyVault SoftDelete (allOf/anyOf/not)",
                Program = program,
                InputJson = kvInputJson,
                ContextJson = kvContextJson,
                Effect = actualEffect,
                ExpectedEffect = "deny",
            };
        }

        // -------------------------------------------------------------------
        // YAML helpers
        // -------------------------------------------------------------------

        private static string FindCasesDir()
        {
            // Walk up from the benchmark exe to find the repo root.
            var dir = new DirectoryInfo(AppContext.BaseDirectory);
            while (dir != null)
            {
                var candidate = Path.Combine(dir.FullName, "tests", "azure_policy", "cases");
                if (Directory.Exists(candidate)) return candidate;
                dir = dir.Parent;
            }
            // Try CARGO_MANIFEST_DIR equivalent.
            var envDir = Environment.GetEnvironmentVariable("REGORUS_REPO");
            if (envDir != null)
            {
                var candidate = Path.Combine(envDir, "tests", "azure_policy", "cases");
                if (Directory.Exists(candidate)) return candidate;
            }
            throw new DirectoryNotFoundException(
                "Could not find tests/azure_policy/cases/. Set REGORUS_REPO env var.");
        }

        private static string? GetScalar(YamlMappingNode node, string key)
        {
            var scalarKey = new YamlScalarNode(key);
            if (node.Children.TryGetValue(scalarKey, out var val) && val is YamlScalarNode scalar)
                return scalar.Value;
            return null;
        }

        /// <summary>
        /// Convert a YAML node to a JSON string for passing to the FFI.
        /// </summary>
        private static string YamlNodeToJson(YamlNode node)
        {
            return node switch
            {
                YamlScalarNode scalar => ScalarToJson(scalar),
                YamlMappingNode mapping => MappingToJson(mapping),
                YamlSequenceNode sequence => SequenceToJson(sequence),
                _ => "null"
            };
        }

        private static string ScalarToJson(YamlScalarNode scalar)
        {
            if (scalar.Value == null) return "null";
            var val = scalar.Value;

            // Handle booleans.
            if (val.Equals("true", StringComparison.OrdinalIgnoreCase)) return "true";
            if (val.Equals("false", StringComparison.OrdinalIgnoreCase)) return "false";
            if (val == "null" || val == "~") return "null";

            // Handle numbers.
            if (double.TryParse(val, System.Globalization.NumberStyles.Any,
                System.Globalization.CultureInfo.InvariantCulture, out var num))
            {
                // Check if it's an integer.
                if (long.TryParse(val, out var intVal))
                    return intVal.ToString();
                return num.ToString(System.Globalization.CultureInfo.InvariantCulture);
            }

            // String — JSON-escape it.
            return JsonSerializer.Serialize(val);
        }

        private static string MappingToJson(YamlMappingNode mapping)
        {
            var entries = mapping.Children.Select(kv =>
            {
                var key = kv.Key is YamlScalarNode sk ? sk.Value ?? "" : YamlNodeToJson(kv.Key);
                var jsonKey = JsonSerializer.Serialize(key);
                var jsonVal = YamlNodeToJson(kv.Value);
                return $"{jsonKey}:{jsonVal}";
            });
            return "{" + string.Join(",", entries) + "}";
        }

        private static string SequenceToJson(YamlSequenceNode sequence)
        {
            var items = sequence.Children.Select(YamlNodeToJson);
            return "[" + string.Join(",", items) + "]";
        }

        // -------------------------------------------------------------------
        // Statistics display
        // -------------------------------------------------------------------

        private static void DisplayResults(string name, double[] timingsUs, int warmup, int iterations)
        {
            var sorted = (double[])timingsUs.Clone();
            Array.Sort(sorted);

            var mean = sorted.Average();
            var median = Percentile(sorted, 50);
            var min = sorted[0];
            var max = sorted[sorted.Length - 1];
            var p95 = Percentile(sorted, 95);
            var p99 = Percentile(sorted, 99);
            var variance = sorted.Select(t => (t - mean) * (t - mean)).Average();
            var stddev = Math.Sqrt(variance);

            Console.WriteLine($"  {name}");
            Console.WriteLine($"    Mean:   {FormatDuration(mean),-12}  Median: {FormatDuration(median),-12}  P99: {FormatDuration(p99)}");
        }

        private static double Percentile(double[] sortedData, int percentile)
        {
            var index = (int)Math.Ceiling(percentile / 100.0 * sortedData.Length) - 1;
            return sortedData[Math.Max(0, Math.Min(index, sortedData.Length - 1))];
        }

        private static string FormatDuration(double microseconds)
        {
            if (microseconds >= 1_000_000)
                return $"{microseconds / 1_000_000:F3} s";
            if (microseconds >= 1_000)
                return $"{microseconds / 1_000:F3} ms";
            return $"{microseconds:F3} μs";
        }
    }
}
