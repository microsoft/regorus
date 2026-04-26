<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Azure RBAC Language

Deep knowledge about the Azure RBAC condition language extension in
`src/languages/azure_rbac/`. Read this before modifying RBAC evaluation.

## How RBAC Differs from Rego and Azure Policy

| Aspect | Azure RBAC | Azure Policy | Rego |
|--------|-----------|-------------|------|
| **Purpose** | Access control conditions | Resource compliance | General policy |
| **Execution** | Direct interpretation | RVM compilation | RVM or interpreter |
| **Syntax** | Condition expression strings | JSON constraints | Rego source |
| **Logic** | AND/OR/NOT + quantifiers | allOf/anyOf/not | Rules + comprehensions |
| **Builtins** | 40+ ABAC functions | 19 operators | 100+ OPA builtins |

**Key difference**: RBAC uses **direct interpretation** (no RVM compilation).
It has its own `ConditionInterpreter` that evaluates condition strings directly.

## Directory Structure

```
src/languages/azure_rbac/
  mod.rs              Module root
  interpreter.rs      Direct evaluation engine (66 lines)
  ast/                Expression types (8 files)
    expr.rs           ConditionExpr enum — 15+ variants
    context.rs        EvaluationContext (Principal, Resource, Request, Environment)
    operators.rs      Operator definitions
    literals.rs       Literal types (string, number, bool, datetime, time, set, list)
    references.rs     Attribute references
    spans.rs          Source location tracking
  parser/             Condition string → AST (3 files)
  builtins/           40+ ABAC condition functions (14 files)
  test_cases/         40+ YAML test files
```

## Evaluation Context

RBAC evaluation happens against a rich context:

```rust
struct EvaluationContext {
    principal: Principal,           // Who is accessing
    resource: Resource,             // What is being accessed
    request: RequestContext,        // What action is requested
    environment: EnvironmentContext, // When/where (time, network)
    action: Option<String>,         // Control-plane action
    suboperation: Option<String>,   // Sub-operation identifier
}

struct Principal {
    id: String,
    principal_type: PrincipalType,  // User, Group, ServicePrincipal, MSI
    custom_security_attributes: Value,
}

struct Resource {
    id: String,
    resource_type: String,
    scope: String,
    attributes: Value,
}
```

## Expression Types

The RBAC AST represents condition expressions:

```rust
enum ConditionExpr {
    Logical(LogicalExpression),           // AND/OR
    Unary(UnaryExpression),              // NOT, exists, notExists
    Binary(BinaryExpression),            // Operator comparisons
    FunctionCall(FunctionCallExpression), // ToLower, Substring, etc.
    AttributeReference(AttributeReference),  // principal.id, resource.attributes.env
    ArrayExpression(ArrayExpression),     // ANY/ALL quantifiers
    Identifier(IdentifierExpression),
    VariableReference(VariableReference), // Loop variables
    PropertyAccess(PropertyAccessExpression),
    // Literals: String, Number, Bool, Null, DateTime, Time, Set, List
}
```

## Condition Interpreter

The interpreter evaluates conditions directly (no compilation step):

```rust
struct ConditionInterpreter<'a> {
    context: &'a EvaluationContext,
}

impl ConditionInterpreter {
    fn evaluate_str(&self, condition: &str) -> Result<bool>
    fn evaluate_condition_expression(&self, cond: &ConditionExpression) -> Result<bool>
    fn evaluate_bool(&self, expr: &ConditionExpr) -> Result<bool>
    fn evaluate_value(&self, expr: &ConditionExpr) -> Result<Value>
}
```

### Evaluation Flow

1. Parse condition string → `ConditionExpression` with `ConditionExpr` AST
2. Recursively evaluate:
   - **Logical**: AND/OR with short-circuit evaluation
   - **Unary**: NOT, exists (check if attribute is present), notExists
   - **Binary**: delegate to `RbacBuiltinEvaluator` for comparison
   - **Function calls**: evaluate with built-in RBAC functions
   - **Array expressions**: ANY/ALL quantifiers over collections
   - **Attribute references**: resolve from evaluation context

## RBAC Builtins (40+ functions)

Organized by category:

| Category | Functions |
|----------|-----------|
| **Strings** | StringEquals, StringEqualsIgnoreCase, StringLike, StringMatches, StringNotEquals, ... |
| **Numbers** | NumericEquals, NumericGreaterThan, NumericInRange, ... |
| **Booleans** | BoolEquals, BoolNotEquals |
| **GUIDs** | GuidEquals, GuidNotEquals |
| **DateTime** | DateTimeEquals, DateTimeGreaterThan, DateTimeInRange, ... |
| **Time of Day** | TimeOfDayEquals, TimeOfDayGreaterThan, TimeOfDayInRange, ... |
| **IP** | IpMatch, IpNotMatch, IpInRange |
| **Lists** | ListContains, ListNotContains, NormalizeList, NormalizeSet |
| **Actions** | ActionMatches, SubOperationMatches |
| **Quantifiers** | ANY, ALL, EXISTS |

Each builtin is an enum variant in `RbacBuiltin` used for direct dispatch
in `BinaryExpression` evaluation.

## Key Invariants

1. **No RVM backend** — RBAC is pure interpretation. Changes to the RVM do
   not affect RBAC evaluation.

2. **Short-circuit evaluation** — AND/OR evaluate left-to-right and stop
   early. This is semantically important (not just an optimization).

3. **Attribute resolution** — attributes are resolved from the evaluation
   context at evaluation time. Missing attributes may produce errors or
   false depending on the operator.

4. **Case sensitivity** — string comparisons have both case-sensitive and
   case-insensitive variants. Use the correct one.

## Testing

40+ YAML test files in `test_cases/` provide comprehensive coverage.
Each test case specifies a condition string, evaluation context, and
expected result.
