<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Interpreter Architecture

Deep knowledge about the tree-walking interpreter (`src/interpreter.rs`).
This is a 4,400+ line file and the legacy execution path. Read this before
modifying evaluation logic.

## Core Data Structures

### Interpreter State

```rust
pub struct Interpreter {
    compiled_policy: Rc<CompiledPolicyData>,
    data: Value,                           // Data document (rules materialize here)
    input: Value,                          // User-provided input
    with_document: Value,                  // Temporary overrides via `with`
    scopes: Vec<Scope>,                    // Variable binding stack
    contexts: Vec<Context>,                // Evaluation context stack
    processed: BTreeSet<Ref<Rule>>,        // Rules already evaluated
    processed_paths: Value,                // Data paths already evaluated
    rule_values: RuleValues,               // Cached rule evaluation results
    active_rules: Vec<Ref<Rule>>,          // Stack for cycle detection
    loop_var_values: ExprLookup,           // Loop variable cache
    builtins_cache: BTreeMap<..., Value>,   // Builtin result cache
    execution_timer: ExecutionTimer,       // Time limit enforcement
    extensions: Map<String, (u8, Rc<Box<dyn Extension>>)>,
    with_functions: BTreeMap<String, FunctionModifier>,
}
```

### Context Stack

Each query/rule evaluation pushes a `Context`:

```rust
struct Context {
    key_expr: Option<ExprRef>,      // Object comprehension key
    output_expr: Option<ExprRef>,   // Output value expression
    value: Value,                   // Accumulated results
    result: Option<QueryResult>,    // For user queries (bindings + expressions)
    rule_ref: Option<ExprRef>,      // Reference to current rule
    rule_value: Value,              // Computed rule value
    is_compr: bool,                 // Comprehension context
    is_set: bool,                   // Set rule context
    is_old_style_set: bool,         // Legacy set syntax
    early_return: bool,             // Break out of evaluation
}
```

Contexts are pushed for: rule bodies, comprehensions, user queries. The
context determines how results are collected (array, set, object, or query
result bindings).

### Scope Stack

Variables are tracked in a stack of scopes:

```rust
type Scope = BTreeMap<SourceStr, Value>;
```

Each function/rule call pushes a new scope. Variable lookup searches from
innermost to outermost scope.

## Evaluation Call Hierarchy

```
eval_rule()                          Entry: evaluate a named rule
  └─ eval_rule_impl()               Dispatch by rule type (Spec/Default/Func)
       └─ eval_rule_bodies()         Evaluate rule body alternatives
            └─ eval_query()          Execute a query (ordered statements)
                 └─ eval_stmts()     Execute statements in scheduled order
                      └─ eval_stmt() Single statement dispatch
                           └─ eval_stmt_impl()
                                ├─ Expr → eval_expr()
                                ├─ SomeIn → eval_some_in()
                                ├─ SomeVars → variable declaration
                                ├─ NotExpr → negation wrapper
                                └─ Every → eval_every()

eval_expr()                          Expression dispatcher (25+ variants)
  ├─ Literals → direct Value
  ├─ Var/RefDot/RefBrack → eval_chained_ref_dot_or_brack()
  ├─ BinExpr → eval_bin_expr()
  ├─ BoolExpr → eval_bool_expr()
  ├─ ArithExpr → eval_arith_expr()
  ├─ Call → eval_call()
  ├─ ArrayCompr/SetCompr/ObjectCompr → eval_*_compr()
  ├─ Array/Set/Object → eval_array/set/object()
  └─ AssignExpr → execute_destructuring_plan()
```

## Rule Evaluation Lifecycle

### 1. Rule Discovery

When code references `data.pkg.rule`, the interpreter calls
`ensure_rule_evaluated()` which:
1. Checks if the path has initial data (from `add_data()`)
2. Looks for rules that define that path in `compiled_policy.rules`
3. Evaluates those rules if not already in `self.processed`

### 2. Rule Bodies

A rule can have multiple bodies (alternatives). Bodies are evaluated in order.
**First successful body wins** — remaining bodies are skipped.

```rego
allow { condition_a }  # Body 1
allow { condition_b }  # Body 2 — only tried if body 1 fails
```

### 3. Result Collection

Results are collected into `ctx.value` based on rule type:
- **Complete rules**: single Value
- **Partial set rules**: `Value::Set` accumulating members
- **Partial object rules**: `Value::Object` accumulating key-value pairs

### 4. Data Materialization

`update_rule_value()` navigates the rule's path and inserts the result into
`self.data`. This is how rules become "virtual documents" accessible via
`data.pkg.rule`.

**Precedence**: initial data > evaluated rules > default rules.

## Variable Lookup

`lookup_var()` is the main variable resolution function. The search order:

1. Local scopes (innermost to outermost)
2. `input` document (if name is "input")
3. `data` document (if name is "data") — triggers lazy rule evaluation
4. Imported variables from other packages
5. Returns `Undefined` if not found

**Key subtlety**: Looking up a `data` path may trigger rule evaluation, which
may trigger further lookups — this is how lazy evaluation chains work.

## The `with` Modifier

`with` temporarily overrides data, input, or functions during evaluation:

```rego
x = eval { y = f(1) with f as g with data.config as override }
```

### State Save/Restore Pattern

The interpreter saves 7 fields as a tuple before applying `with`:
```rust
(with_document, input, data, processed, processed_paths, with_functions, rule_values)
```

After applying overrides:
- `self.processed` is cleared (forces re-evaluation with new context)
- `self.rule_values` is cleared
- The expression is evaluated
- All 7 fields are restored

**Function overrides**:
- `FunctionModifier::Value(v)` — replace function with constant
- `FunctionModifier::Function(path)` — replace with another function

## Cycle Detection

The interpreter tracks `active_rules` (a stack of currently-evaluating rules).
If the same rule appears twice in the stack, a cycle is detected and an error
is raised with a "depends on" chain for debugging.

## Destructuring Plans

The interpreter executes pre-computed `DestructuringPlan`s for pattern matching
in assignments and `some...in` bindings:

- `DestructuringPlan::Var` — bind to variable
- `DestructuringPlan::Ignore` — wildcard `_`
- `DestructuringPlan::EqualityValue` — match against literal
- `DestructuringPlan::Array` — destructure array elements
- `DestructuringPlan::Object` — destructure object fields

Plans are computed at compile time by `src/compiler/destructuring_planner/`.

## Performance-Critical Paths

- **Loop variable caching** (`loop_var_values`): avoids re-evaluating loop
  expressions on each iteration
- **Builtin result caching** (`builtins_cache`): memoizes pure builtin calls
- **Rule processing tracking** (`processed`): prevents redundant evaluation
- **Execution timer**: cooperative checking with amortized overhead

## Known TODOs in Code

The interpreter has ~15 TODO comments indicating areas of active development:
- Recursive calls with different values for same expression
- Type coercion behavior verification
- With modifier optimization (delay state restore)
- Variable lookup timing questions
- Copy optimization for paths

These indicate areas where the code is known to be evolving. Extra care
is needed when modifying near these comments.

## Connection to RVM

Both the interpreter and RVM:
- Use the same `BUILTINS` registry
- Share the `Value` type
- Use the same `CompiledPolicyData` (schedules, hoisted loops)
- Produce the same results for the same inputs (semantic equivalence)

When implementing features, they must work in **both** execution paths.
