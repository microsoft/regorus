# Destructuring Planner

The destructuring planner pre-computes how Rego assignments, function parameters, loop indices, and `some ... in` expressions bind variables. By materializing explicit plans during compilation, the interpreter can execute complex binding patterns without re-inspecting the abstract syntax tree (AST) each time an expression runs.

```
+--------------+      +----------------------------+      +-------------------+
| AST walker   | ---> | Destructuring planner core | ---> | BindingPlans table |
+--------------+      +----------------------------+      +-------------------+
        |                        |   ^                              |
        |                        v   |                              v
        |                +------------------+            +-------------------+
        |                | ScopeContext     | <--------> | Planner utilities |
        |                +------------------+            +-------------------+
        v
+------------------+
| Scheduler output |
+------------------+

Downstream compiler passes reuse the same plans:

```
BindingPlans table
  |
  +--> Rego VM compiler (RVM) for bytecode emission
  +--> Type propagation pass
  +--> Constant folding and other analyzers
```
```

## Planner building blocks

### Scope awareness

The planner relies on `ScopeContext` implementations to answer two questions for every variable candidate:

| Question                                   | Method                         | Why it matters                                                         |
| :----------------------------------------- | :----------------------------- | :--------------------------------------------------------------------- |
| "Is this name currently unbound?"         | `is_var_unbound(var, scoping)` | Determines whether a symbol becomes a new binding or should be treated as an equality check. |
| "Has this scope already introduced the name?" | `has_same_scope_binding(var)` | Blocks same-scope rebinding for `:=` while still permitting shadowing in child scopes. |

The planner uses two scoping modes:

| Scoping mode    | Description                                                                 | Used by                                                     |
| :-------------- | :-------------------------------------------------------------------------- | :---------------------------------------------------------- |
| `RespectParent` | Honors existing bindings. Only treats names that are not yet visible as new bindings. | `=` comparisons, loop indices, `some ... in` value/key plans. |
| `AllowShadowing` | Allows new bindings even if the name is defined in an ancestor scope.       | Function parameters, `:=` LHS, `some ... in` overlay contexts. |

### Plan families

Three layers of plan types describe the complete binding strategy.

#### `DestructuringPlan`

| Variant                               | Purpose                                            | Notes on bindings                                               |
| :------------------------------------- | :------------------------------------------------- | :-------------------------------------------------------------- |
| `Var(span)`                            | Bind the complete value to the variable at `span`. | Adds the variable to the current scope.                         |
| `Ignore`                               | Consume a wildcard (`_`).                          | No bindings emitted.                                            |
| `EqualityExpr(expr)`                   | Require runtime equality with a dynamic expression. | Used when a candidate variable is already bound.                |
| `EqualityValue(value)`                 | Require equality with a literal known at compile time. | Enables static structural checks.                               |
| `Array { element_plans }`              | Destructure arrays element-by-element.             | Recursively nests `DestructuringPlan` values.                   |
| `Object { field_plans, dynamic_fields }` | Destructure objects. Literal keys use `field_plans`; dynamic keys appear in `dynamic_fields`. | Ensures literal shape compatibility during planning. |

#### `AssignmentPlan`

| Variant           | Triggers                    | Binding behavior                                                                 |
| :--------------- | :-------------------------- | :-------------------------------------------------------------------------------- |
| `ColonEquals`     | `:=`                        | Only LHS may introduce bindings; RHS must match structure/literals. Same-scope rebinding raises an error. |
| `EqualsBindLeft`  | `=` where LHS has free vars | Binds the LHS pattern after structural + literal checks.                          |
| `EqualsBindRight` | `=` where RHS has free vars | Symmetric to `EqualsBindLeft`.                                                    |
| `EqualsBothSides` | `=` where both sides have free vars | Flattens matching sub-expressions into `(value_expr, plan)` pairs and orders them using dependency analysis. |
| `EqualityCheck`   | `=` with no free vars       | Pure equality comparison.                                                         |
| `WildcardMatch`   | `=` when either side is `_` | Short-circuits to avoid materializing a plan.                                     |

#### `BindingPlan`

| Variant      | Created by                          | Typical consumers                                   |
| :----------- | :---------------------------------- | :-------------------------------------------------- |
| `Assignment` | `create_assignment_binding_plan`    | Rule bodies for `:=` and `=`.                       |
| `LoopIndex`  | `create_loop_index_binding_plan`    | Hoisted loops and comprehensions.                   |
| `Parameter`  | `create_parameter_binding_plan`     | Functions and rule heads.                           |
| `SomeIn`     | `create_some_in_binding_plan`       | `some key, value in collection` statements.         |

## Planner workflow

1. **Entry point selection** — The compiler pass decides which helper to call based on the AST node (assignment, comprehension, function parameter, etc.).
2. **Pattern inspection** — `create_destructuring_plan` walks the candidate pattern and records which names would become new bindings under the selected scoping rules.
3. **Conflict detection** — The planner asks the context for same-scope bindings and raises `VariableAlreadyDefined` when a duplicate `:=` appears in the same block.
4. **Structural validation** — Helpers such as `ensure_structural_compatibility` and `ensure_literal_match` verify that literal shapes are consistent.
5. **Plan assembly** — The resulting `DestructuringPlan`, `AssignmentPlan`, or higher-level `BindingPlan` is stored in the binding lookup table for quick interpreter access.

### Example flow

```
[Rule body] -- := --> [create_assignment_binding_plan]
                         |
                         v
                [create_destructuring_plan]
                         |
                  +------v--------------+
                  | ScopeContext checks |
                  +------+--------------+
                         |
             +-----------v-----------+
             | AssignmentPlan::ColonEquals |
             +-----------+-----------+
                         |
               stores in BindingPlans table
```

## Worked examples

Each example shows the original Rego snippet, the resulting binding plan, and highlights of the emitted bindings.

### 1. Nested `:=` patterns

```rego
package test

result := {
  "outer": outer,
  "inner": inner,
  "tag": tag,
} if {
  [outer, {"meta": {"inner": inner, "tag": tag}}] := [
    "alpha",
    {"meta": {"inner": "omega", "tag": "v1"}},
  ]
}
```

Plan overview:

```
BindingPlan::Assignment
└── AssignmentPlan::ColonEquals
    ├── lhs_expr: array pattern
    └── lhs_plan: DestructuringPlan::Array
        ├── [0] -> Var("outer")
        └── [1] -> DestructuringPlan::Object
            └── key "meta": DestructuringPlan::Object
                ├── key "inner": Var("inner")
                └── key "tag": Var("tag")
```

| New binding | Source span | Notes |
| --- | --- | --- |
| `outer` | LHS array index 0 | New symbol in scope. |
| `inner` | Object field `meta.inner` | Shares scope with `outer`. |
| `tag` | Object field `meta.tag` | Must not reappear in same `:=` block. |

### 2. Symmetric `=` binding

```rego
package test

values := [[left_id, right_id, val] |
  some left, right, left_id, right_id, val
  data.transitions[_] = [left, right]
  [{"id": left_id, "next": {"target": right_id}}, {"id": right_id, "payload": {"value": val}}] = [left, right]
]
```

Plan fragments:

```
BindingPlan::Assignment
└── AssignmentPlan::EqualsBothSides
    └── element_pairs (ordered)
        1. value_expr -> rhs[0]
           plan -> DestructuringPlan::Object
                 key "id"   -> Var("left_id")
                 key "next" -> DestructuringPlan::Object { key "target" -> Var("right_id") }
        2. value_expr -> rhs[1]
           plan -> DestructuringPlan::Object
                 key "id"      -> Var("right_id")
                 key "payload" -> DestructuringPlan::Object { key "value" -> Var("val") }
```

Dependency ordering ensures `left_id` is available before `right_id`/`val` comparisons run.

### 3. Function parameter destructuring

```rego
package test

# f([id, payload]) := payload
f([id, payload]) := result {
  result := payload
}
```

```
BindingPlan::Parameter
└── param_expr: array pattern
    destructuring_plan:
      Array
      ├── [0] -> Var("id")
      └── [1] -> Var("payload")
```

Both bindings use `ScopingMode::AllowShadowing`, allowing `id` or `payload` to shadow outer names when the function executes.

### 4. `some ... in` loop

```rego
package test

some user, record in data.users
record.role == "admin"
```

Plan summary:

```
BindingPlan::SomeIn
├── collection_expr: data.users
├── key_plan: DestructuringPlan::Var("user")
└── value_plan: DestructuringPlan::Var("record")
```

Tables for bindings:

| Element | Plan | New bindings |
| --- | --- | --- |
| `key_plan` | `Var("user")` | Introduces `user` if unbound. |
| `value_plan` | `Var("record")` | Introduces `record`. |

Literal arrays used in `collection_expr` are checked so the planner can report mismatched element shapes upfront.

### 5. Rebinding error detection

```rego
package test

flag := true if {
  value := "initial"
  value := "shadowed"
}
```

```
BindingPlan::Assignment
└── AssignmentPlan::ColonEquals (lhs := value)
```

During planning, the second `:=` consults `has_same_scope_binding("value")` which returns `true`. The planner emits `BindingPlannerError::VariableAlreadyDefined` and compilation reports:

```
error: var `value` used before definition below
```

## Interpreter handoff

Planned bindings are stored in the same lookup tables as hoisted loops. At runtime the interpreter:

1. Fetches the `BindingPlan` using `(module_id, expr_idx)`.
2. Executes the plan, binding or validating values without re-walking the AST.
3. Falls back to legacy evaluation if a plan is missing (useful for incremental compilation or mixed modules).

This division keeps the hot execution path small while letting the compiler perform aggressive validation and error reporting ahead of time.
