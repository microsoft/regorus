# Regorus C# API Documentation

This document describes the C# API for Regorus, focusing on the compiled policy approach for high-performance policy evaluation.

## Overview

The Regorus C# bindings provide a modern, thread-safe API for compiling and evaluating Open Policy Agent (OPA) Rego policies. The API is designed around pre-compiled policies that can be evaluated efficiently multiple times with different inputs.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    CompiledPolicy Workflow                      │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│  Policy Modules │    │   Target/Schema  │    │   Static Data   │
│  (.rego files)  │    │    Registries    │    │     (JSON)      │
└─────────┬───────┘    └────────┬─────────┘    └─────────┬───────┘
          │                     │                        │
          └─────────────────────┼────────────────────────┘
                                │
                                ▼
                    ┌─────────────────────────┐
                    │        Compile          │
                    │  ┌─────────────────────┐│
                    │  │ Parse & Analyze     ││
                    │  │ Infer Resource Types││
                    │  │ Build AST & Rules   ││
                    │  │ Target Integration  ││
                    │  └─────────────────────┘│
                    └─────────────┬───────────┘
                                  │
                                  ▼
                      ┌─────────────────────────┐
                      │    CompiledPolicy       │
                      │ ┌─────────────────────┐ │
                      │ │ AST & Rules         │ │
                      │ │ Target Info         │ │
                      │ │ Resource Types      │ │
                      │ │ Function Table      │ │
                      │ │ Compiled Modules    │ │
                      │ └─────────────────────┘ │
                      └─────────────┬───────────┘
                                    │
                                    ▼
                          ┌─────────────────────┐
                          │    Service Cache    │
                          │ (Policy Framework,  │
                          │  MS Graph, etc.)    │
                          │ ┌─────────────────┐ │
                          │ │ CompiledPolicy  │ │ ◄─── Same LOCK-FREE policy
                          │ │    (cached)     │ │      instance shared across
                          │ └─────────────────┘ │      all threads
                          └─────────┬───────────┘
                                    │
                            ┌───────┼───────┬───────┐
                            │       │       │       │
                            ▼       ▼       ▼       ▼
                    ┌─────────────┐ ┌─────────────┐ ┌─────────────┐
                    │  Thread 1   │ │  Thread 2   │ │  Thread N   │
                    │             │ │             │ │             │
                    │ input1 ────▶│ │ input2 ────▶│ │ inputN ────▶│
                    │ ◄─── result │ │ ◄─── result │ │ ◄─── result │
                    └─────────────┘ └─────────────┘ └─────────────┘

┌─────────────────────────────────────────────────────────────────┐
│                        Key Benefits                             │
├─────────────────────────────────────────────────────────────────┤
│ ✓ Compile Once, Evaluate Many     ✓ Lock-Free Concurrent Eval   │
│ ✓ No Re-parsing Overhead          ✓ Reference Counting Safety   │
│ ✓ Reduced GC Pressure             ✓ Proper Resource Management  │
│ ✓ Cache-Friendly Design           ✓ Target System Integration   │
└─────────────────────────────────────────────────────────────────┘
```

## Key Features

- **Pre-compiled Policies**: Compile once, evaluate many times for optimal performance
- **Target System Support**: Built-in support for Azure Policy targets with resource type inference
- **Thread Safety**: All operations are thread-safe without external synchronization
- **Registry Management**: Centralized management of targets and schemas
- **Policy Introspection**: Rich metadata about compiled policies

## Core Classes

### CompiledPolicy

The `CompiledPolicy` class represents a pre-compiled Rego policy that can be evaluated efficiently.

```csharp
public sealed class CompiledPolicy : IDisposable
{
    // Evaluate the policy with input data
    public string? EvalWithInput(string inputJson);
    
    // Get comprehensive policy metadata
    public PolicyInfo GetPolicyInfo();
    
    // Dispose of unmanaged resources
    public void Dispose();
}
```

**Thread Safety**: All methods are thread-safe. Multiple threads can call `EvalWithInput()` concurrently, and `Dispose()` will safely wait for active evaluations to complete.

### Compiler

The `Compiler` class provides static methods for compiling policies.

```csharp
public static class Compiler
{
    // Compile a policy with a specific entrypoint rule
    public static CompiledPolicy CompilePolicyWithEntrypoint(
        string dataJson, 
        IEnumerable<PolicyModule> modules, 
        string entryPointRule);
    
    // Compile a target-aware policy (requires azure_policy feature)
    public static CompiledPolicy CompilePolicyForTarget(
        string dataJson, 
        IEnumerable<PolicyModule> modules);
}
```

### PolicyModule

Represents a single policy module to be compiled. Each PolicyModule corresponds to a Rego file (.rego), and each Rego file defines a Rego package using the `package` declaration at the top of the file.

```csharp
public struct PolicyModule
{
    public string Id { get; set; }
    public string Content { get; set; }
    
    public PolicyModule(string id, string content);
}
```

**Properties:**
- `Id`: A unique identifier for the module, typically the filename (e.g., "policy.rego", "rules/storage.rego")
- `Content`: The complete Rego policy content, including the `package` declaration and all rules

**Example:**
```csharp
var module = new PolicyModule("storage-policy.rego", @"
    package azure.storage
    import rego.v1
    
    default allow := false
    allow if input.type == ""Microsoft.Storage/storageAccounts""
");
```

### PolicyInfo

Provides comprehensive metadata about a compiled policy.

```csharp
public class PolicyInfo
{
    // List of module identifiers
    public List<string> ModuleIds { get; set; }
    
    // Target name (for target-aware policies)
    public string? TargetName { get; set; }
    
    // Resource types this policy can evaluate
    public List<string> ApplicableResourceTypes { get; set; }
    
    // Primary rule/entrypoint
    public string EntrypointRule { get; set; }
    
    // Effect rule (for target-aware policies)
    public string? EffectRule { get; set; }
    
    // Policy parameters
    public List<PolicyParameters> Parameters { get; set; }
}
```

## Registry Classes

### TargetRegistry

Manages target definitions for Azure Policy-style evaluations.

```csharp
public static class TargetRegistry
{
    // Register a target from JSON
    public static void RegisterFromJson(string targetJson);
    
    // Check if a target exists
    public static bool Contains(string name);
    
    // List all registered targets
    public static string ListNames();
    
    // Remove a target
    public static bool Remove(string name);
    
    // Clear all targets
    public static void Clear();
    
    // Get count of registered targets
    public static int Count { get; }
    
    // Check if registry is empty
    public static bool IsEmpty { get; }
}
```

### SchemaRegistry

Manages schema definitions for validation.

```csharp
public static class SchemaRegistry
{
    // Register resource schemas
    public static void RegisterResourceSchema(string name, string schemaJson);
    public static bool ContainsResourceSchema(string name);
    public static string ListResourceSchemas();
    
    // Register effect schemas
    public static void RegisterEffectSchema(string name, string schemaJson);
    public static bool ContainsEffectSchema(string name);
    public static string ListEffectSchemas();
    
    // Clear methods
    public static void ClearResourceSchemas();
    public static void ClearEffectSchemas();
}
```

## Usage Examples

### Basic Policy Compilation and Evaluation

```csharp
// Define policy modules
var modules = new List<PolicyModule>
{
    new PolicyModule("policy.rego", @"
        package example
        import rego.v1
        
        default allow := false
        allow if input.user == ""admin""
    ")
};

// Compile the policy
using var policy = Compiler.CompilePolicyWithEntrypoint("{}", modules, "data.example.allow");

// Evaluate with different inputs
var result1 = policy.EvalWithInput(@"{""user"": ""admin""}");  // true
var result2 = policy.EvalWithInput(@"{""user"": ""guest""}");  // false
```

### Target-Aware Policy (Azure Policy Style)

```csharp
// Register target definition
TargetRegistry.RegisterFromJson(@"{
    ""name"": ""azure.storage"",
    ""resource_schema_selector"": ""type"",
    ""resource_types"": {
        ""Microsoft.Storage/storageAccounts"": {
            ""schema"": { /* JSON Schema */ }
        }
    }
}");

// Define policy with target
var modules = new List<PolicyModule>
{
    new PolicyModule("policy.rego", @"
        package policy
        import rego.v1
        
        __target__ := ""azure.storage""
        
        default effect := ""deny""
        effect := ""allow"" if {
            input.type == ""Microsoft.Storage/storageAccounts""
            input.properties.supportsHttpsTrafficOnly == true
        }
    ")
};

// Compile for target
using var policy = Compiler.CompilePolicyForTarget("{}", modules);

// Evaluate Azure resource
var resource = @"{
    ""type"": ""Microsoft.Storage/storageAccounts"",
    ""properties"": {
        ""supportsHttpsTrafficOnly"": true
    }
}";

var result = policy.EvalWithInput(resource);  // "allow"
```

### Policy Introspection

```csharp
// Get policy metadata
var info = policy.GetPolicyInfo();

Console.WriteLine($"Target: {info.TargetName}");
Console.WriteLine($"Effect Rule: {info.EffectRule}");
Console.WriteLine($"Modules: {string.Join(", ", info.ModuleIds)}");
Console.WriteLine($"Resource Types: {string.Join(", ", info.ApplicableResourceTypes)}");

// Access parameters
if (info.Parameters != null && info.Parameters.Count > 0)
{
    foreach (var parameterSet in info.Parameters)
    {
        Console.WriteLine($"Module: {parameterSet.SourceFile}");
        foreach (var param in parameterSet.Parameters)
        {
            Console.WriteLine($"Parameter: {param.Name} ({param.Type})");
            if (param.Default != null)
                Console.WriteLine($"  Default: {param.Default}");
        }
    }
}
```

### Concurrent Evaluation

```csharp
// CompiledPolicy is thread-safe
var tasks = Enumerable.Range(0, 100).Select(i => 
    Task.Run(() => policy.EvalWithInput($@"{{""id"": {i}}}"))
).ToArray();

var results = await Task.WhenAll(tasks);
```

## Performance Considerations

### Compilation Overhead

- Policy compilation has significant overhead due to parsing and analysis
- **Best Practice**: Compile once, reuse many times
- Consider caching compiled policies for repeated use

### Memory Management

- `CompiledPolicy` manages unmanaged resources
- **Always** dispose of compiled policies using `using` statements or explicit `Dispose()`
- Disposal is thread-safe and waits for active evaluations

### Thread Safety

- All classes are thread-safe for concurrent reads/evaluations
- Registry modifications should be done during initialization
- No external synchronization required

## Error Handling

All methods throw `Exception` on errors with descriptive messages:

```csharp
try
{
    var policy = Compiler.CompilePolicyWithEntrypoint(data, modules, rule);
    var result = policy.EvalWithInput(input);
}
catch (Exception ex)
{
    Console.WriteLine($"Error: {ex.Message}");
}
```

## Feature Flags

Some functionality requires specific Rust feature flags:

- **azure_policy**: Required for target-aware compilation and policy parameters
- Without this feature, target-related methods will not be available

## Version Compatibility

- Requires .NET Standard 2.0 or later
- Compatible with .NET Framework 4.6.1+, .NET Core 2.0+, .NET 5+
- Uses System.Text.Json for JSON serialization (added as dependency)

## Best Practices

1. **Compile Once, Evaluate Many**: Pre-compile policies for repeated evaluation
2. **Use Disposable Pattern**: Always dispose of CompiledPolicy instances
3. **Thread-Safe Design**: Take advantage of built-in thread safety
4. **Registry Setup**: Configure targets and schemas during application startup
5. **Error Handling**: Wrap operations in try-catch blocks for robust error handling
6. **Performance Monitoring**: Monitor evaluation times for performance optimization

## Migration from Engine-Based API

If migrating from an engine-based approach:

```csharp
// Old approach (if it existed)
// var engine = new Engine();
// engine.AddPolicy("policy.rego", policyContent);
// engine.SetInputJson(inputJson);
// var result = engine.EvalRule("data.policy.allow");

// New compiled approach
var modules = new[] { new PolicyModule("policy.rego", policyContent) };
using var policy = Compiler.CompilePolicyWithEntrypoint("{}", modules, "data.policy.allow");
var result = policy.EvalWithInput(inputJson);
```

The compiled approach provides better performance for repeated evaluations and clearer resource management.
