# Regorus CSharp

**Regorus** is

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
   interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

See main [Regorus page](https://github.com/microsoft/regorus) for more details about the project.

# Building

## Github Actions

The simplest way to build a Nuget for Regorus' C# bindings is to use Github Actions. The action to do so is named `bindings/csharp` and is defined in `.github/workflows/test-csharp.yml`.

There are two ways to trigger a Nuget build.
1. Runs are triggered automatically whenever a push or pull request is made to the `main` branch.
2. A run can be triggered manually by navigating to the action in the Github UI and clicking `Run workflow`. This option allows you to generate a Nuget for any branch, which is useful when testing the integration of in-progress changes to Regorus with other projects. Nuget files that are generated via this flow will have a `manualtrigger` suffix appended to their version number, making it easy to distinguish them from Nugets generated using the `main` branch.
![Image displaying the run workflow button](docs/images/readme/manuallytriggeringrun.png)

Once the workflow run completes, the generated Nuget can be downloaded by following these steps:
1. Open the run.
2. Click on `Build Regorus nuget` on the left.
3. Expand the `Upload Regorus nuget` step.
4. Click the `Artifact download URL` link at the bottom.
5. Save and extract the downloaded zip file to find the `.nupkg` file.
![Image displaying the download URL link](docs/images/readme/downloadnuget.png)

## Local

The `cargo xtask` runner provides helpers for local builds:

1. `cargo xtask ffi` builds the `bindings/ffi` crate for the host platform in debug mode. Add `--target <triple>` (repeatable) to cross-compile, or `--release` to produce optimised artefacts. Results land under `bindings/ffi/target/<triple>/<profile>`.
2. `cargo xtask nuget` reuses those artefacts to pack the C# library. It defaults to debug builds for the host but accepts `--target`, `--release`, `--artifacts-dir <path>` to reuse existing binaries, and `--enforce-artifacts` to require every officially supported platform.
3. `cargo xtask test-csharp` ensures a NuGet is available (rebuilding when required or when `--force-nuget` is passed) and then runs `Regorus.Tests`, `TestApp`, and `TargetExampleApp` against it. The command accepts the same build flags as `cargo xtask nuget`.

## Memory Usage Safeguards

The C# bindings expose allocator-backed memory tracking utilities via the static `Regorus.MemoryLimits` helper. Typical usage:

```csharp
// Restrict total allocations to 128 MiB for the process
Regorus.MemoryLimits.SetGlobalMemoryLimit(128 * 1024 * 1024);

// Optional: tune how frequently each thread flushes its allocation counters
Regorus.MemoryLimits.SetThreadFlushThresholdOverride(256 * 1024);

// Engine operations throw InvalidOperationException with the allocator message if the budget is exceeded
using var engine = new Regorus.Engine();
var veryLargeJson = new string('x', 128 * 1024);
try
{
    engine.SetInputJson(veryLargeJson);
}
catch (InvalidOperationException ex)
{
    Console.WriteLine($"Allocator reported: {ex.Message}");
}

// Restore defaults once done
Regorus.MemoryLimits.SetGlobalMemoryLimit(null);
Regorus.MemoryLimits.SetThreadFlushThresholdOverride(null);
```

See bindings/csharp/Regorus.Tests/RegorusTests.cs for scenario coverage and bindings/csharp/TargetExampleApp/Program.cs for end-to-end usage.

## RVM Usage Example

The RVM API lets you compile a program from modules/entrypoints and execute it in a VM:

```csharp
using Regorus;

const string Policy = """
package demo
default allow = false
allow if {
  input.user == "alice"
  some role in data.roles[input.user]
  role == "admin"
}
""";

const string Data = """
{ "roles": { "alice": ["admin"] } }
""";

const string Input = """
{ "user": "alice" }
""";

var modules = new[] { new PolicyModule("demo.rego", Policy) };
var entryPoints = new[] { "data.demo.allow" };

using var program = Program.CompileFromModules(Data, modules, entryPoints);
var listing = program.GenerateListing();

using var vm = new Rvm();
vm.LoadProgram(program);
vm.SetDataJson(Data);
vm.SetInputJson(Input);

var result = vm.Execute();
Console.WriteLine($"allow: {result}");
```
