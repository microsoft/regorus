<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Azure Policy Aliases and Normalization

Deep knowledge about the Azure Policy alias system and ARM resource
normalization. Read this before modifying alias resolution, the normalizer,
or the denormalizer.

See also `azure-policy-language.md` for the overall Azure Policy compilation
pipeline.

## What Aliases Are

Azure Policy uses "aliases" to refer to Azure resource properties in a
provider-independent way:

```
Full alias:  Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly
Short name:  supportsHttpsTrafficOnly
ARM path:    properties.supportsHttpsTrafficOnly
```

The alias system bridges between:
- **Policy authors** — who write conditions using alias paths
- **ARM resources** — which have nested JSON structures with varying casing

## Alias Registry

### Loading Sources

**Control-plane aliases** — loaded from Azure provider metadata:
```
GET /providers?$expand=resourceTypes/aliases
```
Produces `ProviderAliases` with resource type → alias mappings.

**Data-plane aliases** — loaded from data policy manifests for `.Data`
namespaces (e.g., `Microsoft.KeyVault.Data/vaults/secrets`).

### Registry Structure

```rust
struct AliasRegistry {
    // Maps full alias name → alias metadata
    aliases: BTreeMap<String, AliasInfo>,
    // Maps resource type → list of aliases
    resource_type_aliases: BTreeMap<String, Vec<String>>,
}
```

The registry provides:
- Alias path segments (for navigating ARM JSON)
- Alias type metadata (string, array, object, etc.)
- Default path mappings when aliases are absent

## Normalization Pipeline

The normalizer transforms ARM resource JSON into a flat structure that
the policy compiler can evaluate directly.

### Input: ARM Resource JSON

```json
{
  "type": "Microsoft.Storage/storageAccounts",
  "id": "/subscriptions/.../storageAccounts/myaccount",
  "name": "myaccount",
  "location": "eastus",
  "properties": {
    "supportsHttpsTrafficOnly": true,
    "networkAcls": {
      "defaultAction": "Deny",
      "virtualNetworkRules": [
        { "id": "/subscriptions/.../subnets/default" }
      ]
    }
  }
}
```

### Output: Normalized Resource

```json
{
  "type": "microsoft.storage/storageaccounts",
  "id": "/subscriptions/.../storageAccounts/myaccount",
  "name": "myaccount",
  "location": "eastus",
  "supportshttpstrafficonly": true,
  "networkacls.defaultaction": "Deny",
  "networkacls.virtualnetworkrules": [
    { "id": "/subscriptions/.../subnets/default" }
  ]
}
```

### Normalization Steps

1. **Copy root fields** (lowercased): `type`, `id`, `kind`, `name`,
   `location`, `identity`, `zones`, `sku`, `plan`, `tags`

2. **Merge properties** — contents of `properties` are merged into the
   result at the top level

3. **Apply alias path resolution**:
   - Each alias has a path (e.g., `properties.networkAcls.defaultAction`)
   - The normalizer navigates the ARM JSON using path segments
   - The extracted value is placed at the alias short name (lowercased)

4. **Handle sub-resources** — sub-resource types (e.g., extensions on VMs)
   are extracted from arrays and normalized separately

5. **Array element handling** — `[*]` in alias paths triggers iteration
   over array elements; each element is normalized independently

6. **Case folding** — all property names are lowercased for
   case-insensitive matching (Azure ARM is case-insensitive)

### Key Complexity: Case Preservation

ARM JSON casing is preserved through normalization and denormalization.
The normalizer records original casing to enable round-trip fidelity.
This matters for Modify/Append effects that construct output JSON.

## Denormalization

The denormalizer converts flat normalized paths back to nested ARM JSON
structure. This is needed for:
- **Modify effect** — construct the resource patch to apply
- **Append effect** — construct fields to add to the resource

### Denormalization Challenge

Given a flat path like `networkacls.defaultaction = "Allow"`, the
denormalizer must reconstruct:

```json
{
  "properties": {
    "networkAcls": {
      "defaultAction": "Allow"
    }
  }
}
```

This requires knowing:
- Where `properties` nesting begins (alias metadata)
- Original casing of each path segment
- Whether intermediate nodes are objects or arrays

## Compiler Integration

### Alias Map

The compiler receives an alias map: `BTreeMap<String, String>` mapping
alias short names to full ARM paths. This is populated from the
`AliasRegistry` for the specific resource type being evaluated.

### Field Compilation

When compiling a `field` condition:

```json
{ "field": "supportsHttpsTrafficOnly", "equals": true }
```

1. Look up field name in alias map
2. If found: compile as property access on normalized input
3. If dynamic (`[concat(...)]`): compile ARM expression, use result as key
4. Emit `Index`/`IndexLiteral`/`ChainedIndex` instructions

### Metadata Accumulation

During compilation, the compiler tracks:
- `observed_aliases` — all alias names referenced
- `observed_field_kinds` — static fields, dynamic fields, `[*]` wildcards
- `observed_resource_types` — resource types from field conditions
- `observed_has_dynamic_fields` — whether ARM expressions appear as fields

This metadata supports policy analysis and optimization.

## Wildcard Semantics

### Unbound `[*]` (outside count)

```json
{ "field": "securityRules[*].destinationPortRange", "equals": "443" }
```

Implicit `allOf` — **every** element must match. The compiler generates
a `LoopStart { mode: Every }` instruction.

### Bound `[*]` (inside count)

```json
{
  "count": {
    "field": "securityRules[*]",
    "where": { "field": "securityRules[*].destinationPortRange", "equals": "443" }
  },
  "greaterOrEquals": 1
}
```

Iteration with counting — each element is tested, matching ones are
counted. The compiler generates `LoopStart { mode: Count }`.

### Multi-level Wildcards

```json
{ "field": "outer[*].inner[*].value" }
```

Nested loops: outer levels use `ForEach`, innermost carries the semantic
operator. The compiler maintains a binding stack to track scope.

## `current()` Function

Inside `count.where` blocks, `current()` refers to the current iteration
element:

```json
{
  "count": {
    "value": "[parameters('items')]",
    "name": "item",
    "where": {
      "value": "[current('item').status]",
      "equals": "active"
    }
  }
}
```

The compiler binds the loop variable and makes it accessible via
`current()` calls in ARM template expressions.

## Existence vs Null

Azure Policy distinguishes between missing fields and null values:

- **Missing field** → `Undefined` in regorus Value system
- **Null field** → `Value::Null`

For most operators, the compiler emits `CoalesceUndefinedToNull` to
treat missing as null. The `exists` operator is the exception — it
specifically tests for field presence:

```json
{ "field": "optionalProperty", "exists": true }   // Field must be present
{ "field": "optionalProperty", "exists": false }  // Field must be absent
```

## Key Invariants

1. **Normalization before compilation** — aliases are resolved during
   normalization, not at compile time or runtime

2. **Case-insensitive everywhere** — all field name comparisons use
   lowercased strings

3. **`[*]` context matters** — same syntax has different semantics
   inside vs outside `count` expressions

4. **Round-trip fidelity** — normalize → denormalize must preserve
   original ARM JSON casing for Modify/Append effects

5. **Missing = null (mostly)** — `CoalesceUndefinedToNull` is the
   default; `exists` is the exception

## Common Pitfalls

1. **Alias path segments** — paths like `properties.a.b` must be split
   correctly. Dots in property names (rare but possible) need escaping.

2. **Sub-resource normalization** — sub-resources have their own type
   and their own alias set. Don't normalize with parent's aliases.

3. **Array vs scalar** — some aliases point to arrays, others to scalars.
   The `[*]` wildcard only works on arrays. Applying it to a scalar
   is a compile-time error.

4. **Dynamic field resolution order** — ARM template expressions in
   field positions are evaluated at runtime. The alias map must be
   available at runtime for dynamic alias resolution.
