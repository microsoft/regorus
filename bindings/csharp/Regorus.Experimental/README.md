# Microsoft.Regorus.Experimental

`Microsoft.Regorus.Experimental` contains opt-in .NET bindings for Regorus explanations and partial
evaluation. It can be referenced alongside the standard `Microsoft.Regorus` package.

The package loads the separately named `regorus_experimental_ffi` native library. Its APIs and
report formats are experimental and may change between prerelease versions.

The standard and experimental packages load separate native runtimes. Memory limits, cache
settings, fallback timers, and other global settings configured through `Microsoft.Regorus` do not
apply to `Microsoft.Regorus.Experimental`; configure both when both packages are used. Their
exception types are also distinct.

Use the standard package when explanation or partial-evaluation APIs are not required.
