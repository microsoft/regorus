<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Azure Policy Language

Deep knowledge about the Azure Policy language extension in
`src/languages/azure_policy/`. Read this before modifying Azure Policy
parsing, compilation, or evaluation.

## How Azure Policy Differs from Rego

| Aspect | Azure Policy | Rego |
|--------|--------------|------|
| **Syntax** | JSON-based declarative constraints | Prolog-like logic language |
| **Compilation** | JSON → AST → RVM bytecode | Source → AST → RVM bytecode |
| **Logic model** | `allOf`/`anyOf`/`not` combinators | Set comprehensions, rules |
| **Effects** | Policy decision directives (Deny, Audit, Modify, ...) | Returns values |
| **Templating** | ARM template expressions `[concat(...)]` | No templating |
| **Field access** | Direct properties + aliases for resource types | Dot-notation queries |

Despite these differences, Azure Policy compiles to the **same RVM bytecode**
as Rego. The shared VM executes both languages.

## Directory Structure

```
src/languages/azure_policy/
  mod.rs                    Module root
  parser/                   JSON → PolicyRule AST (6 files)
  compiler/                 AST → RVM Program (14 files)
  ast/                      Span-annotated AST types
  aliases/                  ARM resource alias normalization
    normalizer/             ARM JSON → flat alias paths
    denormalizer/           Flat paths → ARM JSON structure
  expr.rs                   ARM template expression sub-parser
  strings/                  Case folding, key normalization
```

## AST Types

### Policy Rule Structure

```
PolicyRule
  ├── condition: Constraint    // "if" clause
  └── then_block: ThenBlock    // "then" clause with effect
```

### Constraint Hierarchy

```rust
enum Constraint {
    AllOf { constraints: Vec<Constraint> },   // AND — all must match
    AnyOf { constraints: Vec<Constraint> },   // OR — any must match
    Not { constraint: Box<Constraint> },      // Negation
    Condition(Box<Condition>),                // Leaf condition
}

struct Condition {
    lhs: Lhs,              // What to evaluate (Field, Value, or Count)
    operator: OperatorNode, // How to compare (19 operators)
    rhs: ValueOrExpr,       // What to compare against
}
```

### 19 Operators

Contains, ContainsKey, Equals, Greater, GreaterOrEquals, Exists, In, Less,
LessOrEquals, Like, Match, MatchInsensitively, NotContains, NotContainsKey,
NotEquals, NotIn, NotLike, NotMatch, NotMatchInsensitively.

### Effects

```rust
enum EffectKind {
    Deny, Audit, Append, AuditIfNotExists, DeployIfNotExists,
    Disabled, Modify, DenyAction, Manual, Other,
}
```

**Note:** Effect compilation is not yet fully implemented — the compiler
has stubs for effect handling.

## Compilation to RVM

Azure Policy compiles directly to RVM bytecode through a dedicated compiler:

```rust
pub fn compile_policy_rule(rule: &PolicyRule) -> Result<Rc<Program>>
pub fn compile_policy_definition(defn: &PolicyDefinition) -> Result<Rc<Program>>
pub fn compile_policy_definition_with_aliases(rule, alias_map, modifiable) -> Result<Rc<Program>>
```

The compiler:
1. Parses JSON → `PolicyRule` AST
2. Compiles constraints to RVM instructions (shared VM)
3. Populates metadata (language annotation "azure_policy", effect info)
4. Resolves parameter defaults
5. Optionally resolves aliases

### Compiler State

```rust
struct Compiler {
    program: Program,                    // Shared RVM program being built
    register_counter: u8,               // Register allocation
    alias_map: BTreeMap<String, String>,// Alias resolution
    parameter_defaults: Option<Value>,  // Default parameter values
    cached_input_reg: Option<u8>,       // Cached LoadInput register
    cached_context_reg: Option<u8>,     // Cached LoadContext register
}
```

## Alias System

Azure Policy uses "aliases" to refer to resource properties in a normalized
way. The alias system has two phases:

### Normalizer

Converts ARM JSON resource representations to flat structures with alias
paths. Handles:
- Nested resource properties
- Sub-resource types (e.g., `Microsoft.Compute/virtualMachines/extensions`)
- Array element access
- Case-insensitive property matching

### Denormalizer

Converts flat alias paths back to ARM JSON structure. This is needed for
Modify/Append effects that need to construct resource representations.

**Key complexity**: Casing must survive round-trip. ARM JSON casing is
preserved through normalization and denormalization.

## ARM Template Expressions

Azure Policy conditions can contain ARM template expressions:

```json
{
    "field": "[concat(field('Microsoft.Storage/storageAccounts/name'), '/default')]",
    "equals": "[parameters('storageName')]"
}
```

The expression parser (`expr.rs`) handles:
- Recursive descent parsing (`.`, `()`, `[]` operators)
- Unknown symbols enabled in lexer mode
- 65,536 character column limit for deeply nested expressions
- Functions: `concat()`, `field()`, `parameters()`, etc.

## Count Expressions

Azure Policy supports counting with optional `where` clauses:

```json
{
    "count": {
        "field": "Microsoft.Network/networkSecurityGroups/securityRules[*]",
        "where": { "field": "...", "equals": "..." }
    },
    "greater": 0
}
```

The compiler handles count with existence-pattern optimization — common
patterns like "count > 0" can be compiled as existence checks.

## Wildcard Handling

The `[*]` wildcard in field references creates implicit iteration:

```json
{ "field": "Microsoft.Network/securityRules[*].destinationPortRange" }
```

When a wildcard is unbound, it creates an implicit `allOf` — the condition
must hold for ALL elements. The compiler generates appropriate iteration
code in the RVM.

## Integration Points

Azure Policy integrates with the shared infrastructure:
- **RVM Program**: compiled output is the same `Program` struct as Rego
- **Value type**: evaluation uses the same `Value` enum
- **Engine**: accessible via `Engine::compile_for_target()` when the
  `azure_policy` feature is enabled
- **CompiledPolicy**: wraps the RVM program with metadata

## Key Invariants

1. **Case-insensitive matching** — Azure Policy field names are
   case-insensitive. All comparisons must use case-folded strings.

2. **Alias resolution order** — aliases must be resolved before compilation.
   Missing aliases produce compile-time errors, not runtime errors.

3. **Wildcard semantics** — `[*]` is implicitly "for all" unless inside a
   count expression where it becomes "for each".

4. **Effect metadata** — the compiled program must carry effect information
   in metadata, not in the instruction stream.
