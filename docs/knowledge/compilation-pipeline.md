<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Compilation Pipeline

Deep knowledge about the scheduler, loop hoisting, and destructuring planner.
Read this before modifying `src/scheduler.rs` or `src/compiler/`.

## Pipeline Overview

```
AST (with eidx, sidx, qidx indices)
    ↓
Scheduler  — determines statement execution order via topological sort
    ↓
LoopHoister — identifies loops to hoist and creates binding plans
    ↓
RVM Compiler — generates bytecode using hoisted info (if RVM feature)
    ↓
Program — bytecode + literal table + metadata
```

The interpreter also uses the scheduler and hoister output directly (without
the RVM compiler step).

## AST Indexing

Every AST node carries an index for O(1) lookup of pre-computed information:

- `Expr.eidx: u32` — unique expression index within a module
- `LiteralStmt.sidx: u32` — statement index within a query
- `Query.qidx: u32` — query index within a module

These indices are assigned sequentially during parsing and used as keys into
lookup tables by the scheduler and hoister.

## Scheduler (`src/scheduler.rs`, ~1,218 lines)

### Purpose

Determine safe statement execution order within rule bodies. Statements may
define and use variables, creating dependencies:

```rego
allow {
    user := input.user           # defines 'user'
    role := user.role            # uses 'user', defines 'role'
    role == "admin"              # uses 'role'
}
```

The scheduler topologically sorts statements so each statement's dependencies
are satisfied before it executes.

### Core Data Structures

```rust
struct Definition<Str> {
    var: Str,               // Variable being defined (empty string = condition-only)
    used_vars: Vec<Str>,    // Variables this definition depends on
}

struct StmtInfo<Str> {
    definitions: Vec<Definition<Str>>,  // A statement can define multiple vars
}

struct QuerySchedule {
    scope: Scope,           // Variable binding information
    order: Vec<u16>,        // Computed statement execution order
}
```

### Scheduling Algorithm

The `schedule()` function performs topological sort:

1. **Build dependency map**: `defining_stmts` maps each variable to the
   statements that define it
2. **Initialize**: track `defined_vars` (set), `scheduled` (bool array)
3. **Process variables in discovery order**:
   - For each variable, try to schedule all statements that define it
   - A statement is schedulable when all its `used_vars` are already defined
   - When a statement is scheduled, all its `defined_vars` become available
   - This cascades — newly defined vars may unblock other statements
4. **Handle cycles**: if not all statements scheduled, fall back to source order

**Multi-definition statements**: A single statement can define multiple
variables (e.g., `x, y := foo()`). These are handled with a queue-based
approach that processes definitions within the statement iteratively.

**Empty-variable statements**: Condition-only statements (like `x > 10`) use
an empty string as the variable name. These are re-evaluated whenever any
variable becomes defined, since they may become schedulable.

### Analysis Pipeline

`Analyzer.analyze()`:
1. Add rules and aliases to scopes
2. Gather functions into `FunctionTable`
3. For each module → for each rule → for each query body:
   - `analyze_query()` examines each statement
   - Extracts `StmtInfo` (what variables defined/used)
   - Calls `schedule()` to get execution order
   - Stores result in `Schedule` lookup table

## Loop Hoisting (`src/compiler/hoist.rs`, ~914 lines)

### Purpose

Identify iteration patterns that can be pre-computed and optimized:

```rego
# Before hoisting: interpreter must figure out iteration at runtime
x[i] > 5    # Is 'i' a bound variable or should we iterate?

# After hoisting: pre-computed as a loop with known structure
HoistedLoop { key: i, collection: x, loop_type: IndexIteration }
```

### Core Data Structures

```rust
struct HoistedLoop {
    loop_expr: Option<ExprRef>,   // The expression that generates the loop
    key: Option<ExprRef>,         // Index/key variable
    value: ExprRef,               // Iteration value
    collection: ExprRef,          // Collection being iterated
    loop_type: LoopType,          // IndexIteration or Walk
}

struct HoistedLoopsLookup {
    statement_loops: Lookup<Vec<HoistedLoop>>,    // Per-statement loops
    expr_loops: Lookup<Vec<HoistedLoop>>,         // Per-output-expression loops
    expr_binding_plans: Lookup<BindingPlan>,       // Per-assignment binding plans
    query_contexts: Lookup<ScopeContext>,           // Per-query scope info
}
```

The `Lookup` type uses 2D indexing: `(module_index, item_index)`.

### What Gets Hoisted

**Index iteration**: `x[i]` where `i` is unbound → iterate over indices of `x`

**Walk builtin**: `walk(input, [path, value])` → tree traversal loop

**NOT hoisted**: `x[i]` where `i` is already bound (just an index access)

### ScopeContext

The hoister tracks variable binding state during analysis:

```rust
struct ScopeContext {
    context_type: ContextType,           // Rule/Comprehension/Every/Query
    bound_vars: BTreeSet<String>,        // All bound variables
    current_scope_bound_vars: BTreeSet<String>,  // Newly bound in this scope
    unbound_vars: BTreeSet<String>,      // Declared but not yet bound
    local_vars: BTreeSet<String>,        // Scheduler-tracked locals
}
```

The key method `should_hoist_as_loop()` determines whether a variable access
should be a loop: true if the variable is unbound, local (per scheduler), or
not in the bound set.

### Analysis Flow

```
LoopHoister.populate()
  → populate_module()
    → populate_rule()  — bind parameters, extract key/value expressions
      → populate_query()  — process statements in scheduled order
        → populate_statement()  — analyze literals, store hoisted loops
          → analyze_expr()  — recursive expression analysis
            → detect RefBrack with unbound index → HoistedLoop
            → detect walk() call → HoistedLoop
            → detect assignment → BindingPlan
```

## Destructuring Planner (`src/compiler/destructuring_planner/`)

### Purpose

Create plans for pattern matching in assignments, parameters, and `some...in`:

```rego
[x, y] := func()          # Array destructuring
{a: b} := obj             # Object destructuring
some k, v in collection    # some-in binding
```

### Plan Types

```rust
enum DestructuringPlan {
    Var(Span),                    // Bind value to variable
    Ignore,                       // Wildcard (_)
    EqualityExpr(ExprRef),        // Match against expression
    EqualityValue(Value),         // Match against literal
    Array { element_plans },      // Recursive array destructuring
    Object { field_plans, dynamic_fields },  // Recursive object destructuring
}

enum BindingPlan {
    Destructuring(DestructuringPlan),
    Assignment(AssignmentPlan),
    SomeIn(SomeInPlan),
    LoopIndex(LoopIndexPlan),
    Parameter(ParameterPlan),
}
```

### Assignment Plans

Two assignment operators have different binding semantics:

- **`:=`** (ColonEquals): Only LHS can bind variables. Strict.
- **`=`** (Equals): Both sides can bind. Two-pass analysis needed.

### Variable Binding Context

```rust
trait VariableBindingContext {
    fn is_var_unbound(&self, var_name: &str, scoping: ScopingMode) -> bool;
    fn has_same_scope_binding(&self, var_name: &str) -> bool;
}
```

`ScopingMode::RespectParent` prevents shadowing. `ScopingMode::AllowShadowing`
allows it (used for function parameters).

## Key Invariants

1. **Scheduled order must respect dependencies** — if statement B uses a
   variable defined by statement A, A must execute before B.

2. **Hoisted loops must match runtime behavior** — the hoister's analysis of
   bound vs unbound must match what the interpreter/RVM sees at runtime.

3. **Binding plans must be complete** — every variable that appears in a
   destructuring pattern must have a binding plan (Var, Ignore, or Equality).

4. **Lookup indices must be consistent** — the same `(module_index, eidx/sidx/qidx)`
   must refer to the same AST node across scheduler, hoister, and executor.

## Common Pitfalls

1. **Scope context inheritance** — child contexts (comprehensions, every)
   inherit bound_vars from parent but have their own new bindings.

2. **Multi-definition statements** — a single `=` can bind variables on
   both sides, creating complex dependency chains.

3. **Loop hoisting vs bound variables** — `x[i]` is a loop only if `i` is
   unbound. Mistakenly hoisting a bound index access creates incorrect
   iteration behavior.

4. **Query schedule vs source order** — the scheduled order may differ from
   source order. Code that assumes source order will break.
