// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using Regorus;

namespace Benchmarks
{
    /// <summary>
    /// Benchmark for Azure Policy JSON compilation and evaluation via the
    /// regorus C# FFI bindings. Uses the same KeyVault soft-delete policy
    /// as the PolicyTester .NET benchmark and the Rust Criterion benchmark.
    /// </summary>
    public static class AzurePolicyJsonBenchmark
    {
        // -------------------------------------------------------------------
        // Test data — identical to the Rust benchmark and PolicyTester
        // -------------------------------------------------------------------

        private const string KeyVaultPolicyDefinition = @"{
  ""properties"": {
    ""displayName"": ""Key vaults should have soft delete enabled"",
    ""policyType"": ""BuiltIn"",
    ""mode"": ""Indexed"",
    ""description"": ""Deleting a key vault without soft delete enabled permanently deletes all secrets, keys, and certificates."",
    ""metadata"": { ""version"": ""2.0.0"", ""category"": ""Key Vault"" },
    ""parameters"": {
      ""effect"": {
        ""type"": ""String"",
        ""metadata"": { ""displayName"": ""Effect"" },
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
  ""id"": ""/providers/Microsoft.Authorization/policyDefinitions/1e66c121-a66a-4b1f-9b83-0fd99bf0fc2d"",
  ""name"": ""1e66c121-a66a-4b1f-9b83-0fd99bf0fc2d""
}";

        /// <summary>
        /// Path to provider-cache.json — the same alias metadata that the
        /// PolicyTester .NET benchmark uses. Ensures apples-to-apples comparison.
        /// Override with PROVIDER_CACHE_JSON environment variable.
        /// </summary>
        private static readonly string ProviderCachePath =
            Environment.GetEnvironmentVariable("PROVIDER_CACHE_JSON")
            ?? Path.Combine(Directory.GetCurrentDirectory(), "..", "..", "..", "..", "..", "provider-cache.json");

        /// <summary>Non-compliant: soft delete missing.</summary>
        private const string ResourceNoncompliant = @"{
    ""apiVersion"": ""2018-02-14"",
    ""name"": ""bswantestkv100"",
    ""location"": ""westus"",
    ""type"": ""Microsoft.KeyVault/vaults"",
    ""properties"": { ""sku"": { ""name"": ""Standard"", ""family"": ""A"" } },
    ""tags"": {},
    ""dependsOn"": []
}";

        /// <summary>Compliant: soft delete enabled.</summary>
        private const string ResourceCompliant = @"{
    ""apiVersion"": ""2018-02-14"",
    ""name"": ""bswantestkv100"",
    ""location"": ""westus"",
    ""type"": ""Microsoft.KeyVault/vaults"",
    ""properties"": { ""sku"": { ""name"": ""Standard"", ""family"": ""A"" }, ""enableSoftDelete"": true },
    ""tags"": {},
    ""dependsOn"": []
}";

        // -------------------------------------------------------------------
        // Entry point
        // -------------------------------------------------------------------

        public static void RunBenchmark()
        {
            const int warmup = 100;
            const int iterations = 1000;

            Console.WriteLine("=== Azure Policy JSON Benchmark (C# FFI) ===\n");

            // 1. Compile benchmark
            BenchCompile(warmup, iterations);
            Console.WriteLine();

            // 2. Hot eval benchmark (pre-compiled, reuse VM)
            BenchHotEval(warmup, iterations);
            Console.WriteLine();

            // 3. Cold eval benchmark (new VM per iteration)
            BenchColdEval(warmup, iterations);
            Console.WriteLine();

            // 4. End-to-end benchmark (compile + normalize + eval)
            BenchEndToEnd(warmup, iterations);
        }

        // -------------------------------------------------------------------
        // Helpers
        // -------------------------------------------------------------------

        private static AliasRegistry LoadAliases()
        {
            var json = File.ReadAllText(ProviderCachePath);
            var registry = new AliasRegistry();
            registry.LoadJson(json);
            Console.WriteLine($"  Loaded aliases from {ProviderCachePath}");
            return registry;
        }

        // -------------------------------------------------------------------
        // Compile benchmark
        // -------------------------------------------------------------------

        private static void BenchCompile(int warmup, int iterations)
        {
            Console.WriteLine("--- compile/keyvault_softdelete ---");

            using var registry = LoadAliases();

            // Warmup
            for (int i = 0; i < warmup; i++)
            {
                using var p = AzurePolicyCompiler.CompilePolicyDefinition(registry, KeyVaultPolicyDefinition);
            }

            var timings = new double[iterations];
            var sw = new Stopwatch();

            for (int i = 0; i < iterations; i++)
            {
                sw.Restart();
                using var p = AzurePolicyCompiler.CompilePolicyDefinition(registry, KeyVaultPolicyDefinition);
                sw.Stop();
                timings[i] = sw.Elapsed.TotalMicroseconds;
            }

            DisplayResults("compile/keyvault_softdelete", timings, warmup, iterations);
        }

        // -------------------------------------------------------------------
        // Hot eval — pre-compiled program, reuse VM
        // -------------------------------------------------------------------

        private static void BenchHotEval(int warmup, int iterations)
        {
            Console.WriteLine("--- hot_eval/keyvault_softdelete ---");

            using var registry = LoadAliases();

            // Compile once.
            using var program = AzurePolicyCompiler.CompilePolicyDefinition(registry, KeyVaultPolicyDefinition);

            // Normalize once.
            var inputNoncompliant = registry.NormalizeAndWrap(
                ResourceNoncompliant, apiVersion: null, contextJson: "{}", parametersJson: "{}");
            var inputCompliant = registry.NormalizeAndWrap(
                ResourceCompliant, apiVersion: null, contextJson: "{}", parametersJson: "{}");

            // --- Noncompliant ---
            {
                using var vm = new Rvm();
                vm.LoadProgram(program);

                // Warmup
                for (int i = 0; i < warmup; i++)
                {
                    vm.SetInputJson(inputNoncompliant!);
                    vm.ExecuteEntryPoint("main");
                }

                var timings = new double[iterations];
                var sw = new Stopwatch();
                for (int i = 0; i < iterations; i++)
                {
                    sw.Restart();
                    vm.SetInputJson(inputNoncompliant!);
                    vm.ExecuteEntryPoint("main");
                    sw.Stop();
                    timings[i] = sw.Elapsed.TotalMicroseconds;
                }

                DisplayResults("hot_eval/noncompliant", timings, warmup, iterations);
            }

            // --- Compliant ---
            {
                using var vm = new Rvm();
                vm.LoadProgram(program);

                for (int i = 0; i < warmup; i++)
                {
                    vm.SetInputJson(inputCompliant!);
                    vm.ExecuteEntryPoint("main");
                }

                var timings = new double[iterations];
                var sw = new Stopwatch();
                for (int i = 0; i < iterations; i++)
                {
                    sw.Restart();
                    vm.SetInputJson(inputCompliant!);
                    vm.ExecuteEntryPoint("main");
                    sw.Stop();
                    timings[i] = sw.Elapsed.TotalMicroseconds;
                }

                DisplayResults("hot_eval/compliant", timings, warmup, iterations);
            }
        }

        // -------------------------------------------------------------------
        // Cold eval — new VM per iteration
        // -------------------------------------------------------------------

        private static void BenchColdEval(int warmup, int iterations)
        {
            Console.WriteLine("--- cold_eval/keyvault_softdelete ---");

            using var registry = LoadAliases();

            using var program = AzurePolicyCompiler.CompilePolicyDefinition(registry, KeyVaultPolicyDefinition);

            var inputNoncompliant = registry.NormalizeAndWrap(
                ResourceNoncompliant, apiVersion: null, contextJson: "{}", parametersJson: "{}");

            // Warmup
            for (int i = 0; i < warmup; i++)
            {
                using var vm = new Rvm();
                vm.LoadProgram(program);
                vm.SetInputJson(inputNoncompliant!);
                vm.ExecuteEntryPoint("main");
            }

            var timings = new double[iterations];
            var sw = new Stopwatch();
            for (int i = 0; i < iterations; i++)
            {
                sw.Restart();
                using var vm = new Rvm();
                vm.LoadProgram(program);
                vm.SetInputJson(inputNoncompliant!);
                vm.ExecuteEntryPoint("main");
                sw.Stop();
                timings[i] = sw.Elapsed.TotalMicroseconds;
            }

            DisplayResults("cold_eval/noncompliant", timings, warmup, iterations);
        }

        // -------------------------------------------------------------------
        // End-to-end — compile + normalize + eval
        // -------------------------------------------------------------------

        private static void BenchEndToEnd(int warmup, int iterations)
        {
            Console.WriteLine("--- end_to_end/keyvault_softdelete ---");

            using var registry = LoadAliases();

            // Warmup
            for (int i = 0; i < warmup; i++)
            {
                using var p = AzurePolicyCompiler.CompilePolicyDefinition(registry, KeyVaultPolicyDefinition);
                var envelope = registry.NormalizeAndWrap(
                    ResourceNoncompliant, apiVersion: null, contextJson: "{}", parametersJson: "{}");
                using var vm = new Rvm();
                vm.LoadProgram(p);
                vm.SetInputJson(envelope!);
                vm.ExecuteEntryPoint("main");
            }

            var timings = new double[iterations];
            var sw = new Stopwatch();
            for (int i = 0; i < iterations; i++)
            {
                sw.Restart();
                using var p = AzurePolicyCompiler.CompilePolicyDefinition(registry, KeyVaultPolicyDefinition);
                var envelope = registry.NormalizeAndWrap(
                    ResourceNoncompliant, apiVersion: null, contextJson: "{}", parametersJson: "{}");
                using var vm = new Rvm();
                vm.LoadProgram(p);
                vm.SetInputJson(envelope!);
                vm.ExecuteEntryPoint("main");
                sw.Stop();
                timings[i] = sw.Elapsed.TotalMicroseconds;
            }

            DisplayResults("end_to_end/noncompliant", timings, warmup, iterations);
        }

        // -------------------------------------------------------------------
        // Statistics display (matches PolicyTester bench output format)
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

            Console.WriteLine($"  Benchmark: {name}");
            Console.WriteLine($"    Warmup:   {warmup}");
            Console.WriteLine($"    Measured: {iterations}");
            Console.WriteLine($"    Mean:     {FormatDuration(mean)}");
            Console.WriteLine($"    Median:   {FormatDuration(median)}");
            Console.WriteLine($"    StdDev:   {FormatDuration(stddev)}");
            Console.WriteLine($"    Min:      {FormatDuration(min)}");
            Console.WriteLine($"    Max:      {FormatDuration(max)}");
            Console.WriteLine($"    P95:      {FormatDuration(p95)}");
            Console.WriteLine($"    P99:      {FormatDuration(p99)}");
            Console.WriteLine();
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
