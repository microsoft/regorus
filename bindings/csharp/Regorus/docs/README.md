C# Bindings for Regorus

## Loaded package components

`Engine.GetPolicyPackageComponents()` returns JSON with one row per loaded
module, in insertion order:

```json
[
  {
    "source_file": "policy.rego",
    "components": ["graph", "definition", "1.0.0"]
  }
]
```

This example represents `package graph.definition["1.0.0"]`, not the nested
package `graph.definition["1"]["0"]["0"]`. Components are decoded strings;
literal dots and escaped characters stay within their component. No synthetic
`data` prefix is included. Repeated packages and source-file labels are retained,
including modules without rules. A source label is not a unique module ID.
An empty engine returns `[]`. The getter does not prepare or evaluate policies.

`AddPolicy` and `GetPolicyPackageNames` keep their existing legacy dot-joined
results, which cannot distinguish these two package declarations. Use the new
component arrays when comparing package identity rather than splitting those
legacy strings.

The native library must provide `regorus_engine_get_policy_package_components`.
Update the native library together with the managed binding. Calling this method
with an older native library throws `EntryPointNotFoundException`; it does not
fall back to flattened names. Existing methods keep their existing native calls.