<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Rego Semantics

Deep knowledge about how regorus evaluates Rego policies. Read this before
modifying `src/interpreter.rs`, `src/scheduler.rs`, `src/compiler/`, or
any evaluation-related code.

## Evaluation Model

Regorus is a **compile-then-execute** engine. Key passes:

```
Source → Lexer → Parser → AST → Compiler (scheduling, destructuring, loop hoisting) → Execution
```

The compiler pre-computes:
- **Destructuring plans**: how to bind variables from patterns
- **Schedules**: statement execution order within rule bodies
- **Loop hoisting**: which iterations can be computed at compile time

Runtime evaluation is then straightforward — no runtime planning.

## Rule Evaluation

### Rule Types

**Complete rules** — produce a single value:
```rego
allow = true { input.role == "admin" }
```

**Partial rules** — can have multiple bodies, first success wins:
```rego
allow { input.role == "admin" }
allow { input.role == "superuser" }
```
Bodies are evaluated in order. When one succeeds, remaining bodies are skipped.

**Default rules** — fallback when no rule produces a value:
```rego
default allow = false
```
Default rules are explicitly skipped during normal rule evaluation. They fire
only when the path is `Undefined` and no complete rule exists.

**Precedence**: `initial data > evaluated rules > default rules`

### Rule Caching

Evaluated rules are tracked in `self.processed` set to prevent re-evaluation.
Once a rule has been evaluated for a given context, it won't be re-evaluated
unless the context changes (e.g., via `with` keyword).

## Unification and Destructuring

Regorus does **NOT use a traditional unification algorithm**. Instead:

1. The **compiler** analyzes patterns and generates `DestructuringPlan`s
2. At runtime, `execute_destructuring_plan()` matches values against patterns
3. Returns `true` (match succeeded, variables bound) or `false` (no match)

This is more like pattern matching than Prolog-style unification. There is no
occurs check, no variable-to-variable binding chains.

## Backtracking

Backtracking in regorus is **limited and explicit** — it only occurs with
`some...in` expressions:

```rego
some x in collection
```

The backtracking mechanism:
1. Save current scope
2. Iterate over the collection
3. For each element, bind variables and evaluate remaining statements
4. If remaining statements fail, restore scope and try next element
5. Succeed if any element leads to successful evaluation

**There is no implicit backtracking** in other contexts. Statements in a rule
body execute sequentially — if one fails, the entire rule body fails (no
trying alternatives for previous statements).

## Undefined Propagation in Evaluation

### Boolean and Comparison Operations

```
Undefined <op> anything  →  Undefined
anything <op> Undefined  →  Undefined
```

This applies to all binary operations: `==`, `!=`, `<`, `>`, `<=`, `>=`,
`+`, `-`, `*`, `/`, `%`, `&`, `|`.

### Negation (the subtle case)

```
not true      →  false
not false     →  true
not Undefined →  true
```

`not Undefined` is `true` because negating "this expression has no value"
means "the condition is not met" which is truthy. This is correct OPA
semantics.

### Reference Chains

```rego
x = input.a.b.c
```

If `input.a` exists but `input.a.b` doesn't, the entire reference returns
`Undefined`. The interpreter navigates the path and returns `Undefined` at the
first missing component.

### Collection Literals

```rego
arr = [1, x, 3]   # If x is Undefined, arr is Undefined (not [1, 3])
```

Any `Undefined` element poisons the entire collection literal. This is not
intuitive but matches OPA semantics.

### Builtin Arguments

```rego
count(x)   # If x is Undefined, result is Undefined
```

If any argument to a builtin is `Undefined`, the result is `Undefined`. The
function is never called.

### Rule Body Statements

When a statement in a rule body evaluates to `Undefined` or `false`, the
rule body fails. Statements must succeed sequentially:

```rego
allow {
    input.role == "admin"    # If Undefined → body fails here
    input.active == true     # Never reached
}
```

## Virtual Documents (Rules as Data)

Rules materialize into the `data` object. When code references `data.pkg.rule`,
the interpreter:

1. Checks if the path has initial data (from `add_data()`)
2. If not, looks for rules that define that path
3. Evaluates those rules (if not already cached)
4. Returns the result

`ensure_rule_evaluated()` is the trigger — it's called during path navigation
when a reference might resolve to a rule-defined value.

## The `with` Keyword

`with` temporarily overrides data, input, or functions during evaluation:

```rego
x = eval { y = f(1) with f as g }
```

Implementation pattern (save/modify/restore):
1. Save current state (data, input, processed rules, rule values, with_functions)
2. Apply overrides — modify `self.with_document` and related state
3. Clear `self.processed` to allow re-evaluation with new overrides
4. Evaluate the expression
5. Restore original state

**Function override types:**
- `FunctionModifier::Value(v)` — replace function with a constant value
- `FunctionModifier::Function(path)` — replace function with another function

## Comprehensions

All comprehensions follow the same pattern:

1. Push new context with `output_expr` and collection type
2. Evaluate the query (generates solutions)
3. For each solution, evaluate `output_expr` and add to context's collection
4. Pop context and return accumulated collection

**Array comprehension**: `[expr | query]` → ordered array of expr values
**Set comprehension**: `{expr | query}` → set of expr values
**Object comprehension**: `{key: value | query}` → object of key-value pairs

## Scheduling

The scheduler (`src/scheduler.rs`) determines statement execution order within
rule bodies. This is a **compile-time** optimization that:

1. Analyzes variable dependencies between statements
2. Orders statements to minimize wasted work
3. Moves ground-truth checks (constants, type checks) before expensive iterations
4. Hoists loop-invariant computations

The schedule is pre-computed and stored — the interpreter follows it directly.

## OPA Conformance

Regorus targets faithful OPA semantics. The conformance suite (`tests/opa.rs`)
runs the official OPA test cases. Key areas where conformance matters:

- **Undefined propagation** — must match OPA exactly
- **Error messages** — builtin error messages are compared literally
- **Type coercion** — number handling, string comparison
- **Rule indexing** — which rules fire for which inputs
- **Comprehension behavior** — ordering, deduplication

When behavior differs from OPA, it's a bug unless documented as an intentional
extension (gated behind `rego-extensions` feature).

## Common Pitfalls

1. **Treating Undefined as false** — see value-semantics.md for the full story
2. **Forgetting `not Undefined = true`** — the most common subtle bug
3. **Collection literal with Undefined element** — entire collection becomes Undefined
4. **Rule body short-circuit** — first failing statement stops the body
5. **Default rule precedence** — defaults only fire when path is truly Undefined
6. **`with` scope** — overrides only apply to the expression, not siblings
7. **Virtual document evaluation order** — rules may evaluate lazily
