<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Rego Compiler

Deep knowledge about the Rego → RVM bytecode compiler in
`src/languages/rego/compiler/`. Read this before modifying rule compilation,
expression codegen, register allocation, or optimization passes.

See also `compilation-pipeline.md` for the scheduler and loop hoisting stages
that feed into this compiler.

## Module Structure

```
src/languages/rego/compiler/
  mod.rs               Compiler struct, scope management, register allocation
  core.rs              Variable resolution, register helpers, instruction emission
  program.rs           finish() — default rules, rule info construction, metadata
  rules.rs             Worklist algorithm, per-definition rule compilation
  queries.rs           Statement compilation, loop hoisting integration
  expressions.rs       Expression dispatch, recursive compilation
  references.rs        Chained reference parsing (obj.a[x].b[y])
  function_calls.rs    Builtin vs. user-defined function dispatch
  loops.rs             `every` quantifier, loop mode handling
  comprehensions.rs    Array/Set/Object comprehension compilation
  destructuring.rs     Function parameter binding/validation
  error.rs             Error types with span tracking
```

## Worklist Algorithm

Rule compilation uses a worklist (depth-first queue) rather than
recursive descent. This provides three benefits:

1. **Dependency ordering** — rules are compiled in reference order
2. **Recursion detection** — a call stack tracks in-progress rules
3. **Deduplication** — already-compiled rules are skipped

```
while worklist not empty:
    pop (rule_path, call_stack) from worklist
    if rule_path in call_stack → compile-time recursion error
    if rule_path already compiled → skip
    push rule_path onto call_stack
    compile all definitions of rule_path
    mark rule as compiled
```

When compiling a rule body encounters `CallRule` to another rule, that
target rule is pushed onto the worklist. This ensures rules are compiled
in call order.

## Variable Resolution

The compiler resolves variable names through a priority chain
(`core.rs`):

```
1. "input"  → emit LoadInput (cached per rule definition)
2. "data"   → emit LoadData (cached per rule definition)
3. scope    → use bound register from current scope
4. fallback → treat as rule call: data.{package}.{name}
```

**Input/data caching**: `LoadInput` and `LoadData` are emitted at most
once per rule definition. The cached register is reused for subsequent
references. The cache is reset between definitions to prevent stale state.

## Register Allocation

### Three-Tier Strategy

**Dispatch window** — initial registers for entry point dispatch and
temporary work. Sized by `dispatch_window_size`.

**Per-rule window** — max registers within any single rule definition.
Register 0 is always the result accumulator. The VM allocates a fixed
frame per rule based on `max_rule_window_size`.

**Per-definition reset** — `register_counter` resets to 0 at each
definition start. This minimizes frame size and enables tail calls.

### Special Registers

| Register | Purpose |
|----------|---------|
| 0 | Rule result accumulator |
| `current_input_register` | Cached `LoadInput` (per definition) |
| `current_data_register` | Cached `LoadData` (per definition) |
| 0..N-1 (functions) | Function parameter bindings |

**Limit**: u8 register counter (max 255). The compiler asserts
`register_counter < 255`.

## Expression Compilation

Each `Expr` variant maps to one or more RVM instructions:

| Expr | Instructions | Notes |
|------|-------------|-------|
| Literal (Num/Str/Bool) | `Load` | Literals go to literal table |
| `true`/`false`/`null` | `LoadTrue`/`LoadFalse`/`LoadNull` | Special-cased |
| Var (in scope) | — | Reuse bound register |
| Var (unresolved) | `CallRule` | Treat as rule reference |
| RefDot | `IndexLiteral` | Literal key optimization |
| RefBrack | `Index` or loop | Depends on bound/unbound index |
| Chained ref | `ChainedIndex` | `obj.a[x].b[y]` → single instruction |
| ArithExpr | `Add`/`Sub`/`Mul`/`Div`/`Mod` | |
| BoolExpr | `Eq`/`Ne`/`Lt`/`Le`/`Gt`/`Ge` | |
| Not | `Not` | |
| Call (builtin) | `BuiltinCall` | Via builtin_call_params table |
| Call (user) | `FunctionCall` | Via function_call_params table |
| ArrayCompr | `ComprehensionBegin..Yield..End` | Mode: Array |
| SetCompr | `ComprehensionBegin..Yield..End` | Mode: Set |
| ObjectCompr | `ComprehensionBegin..Yield..End` | Mode: Object |
| Every | `LoopStart { mode: Every }` | Quantifier loop |
| SomeIn | `LoopStart` | Iteration with binding |
| UnaryMinus | `Sub` (0 - x) | |

### Chained References

Multi-level property access like `input.request.headers["content-type"]`
compiles to a single `ChainedIndex` instruction with parameters:

```rust
ChainedIndexParams {
    dest: u8,
    root: ChainedIndexRoot,     // Var or Expr
    components: Vec<Component>, // Field(literal_idx) or Expr(register)
}
```

This avoids emitting multiple `Index` instructions and intermediate
registers.

## Rule Type Compilation

### Complete Rules

```rego
allow := input.admin == true
```

- Body compiled as normal statements
- Success: `RuleReturn {}` (stores result in register 0)
- **Static value optimization**: if all definitions yield the same constant,
  the rule gets `early_exit_on_first_success = true` — VM stops after
  first successful definition

### Partial Set Rules

```rego
ports contains p if { ... }
```

- Emit `ComprehensionYield { value_reg, key_reg: None }`
- Result register accumulates a set of all yielded values

### Partial Object Rules

```rego
people[name] = age if { ... }
```

- Emit `ComprehensionYield { value_reg, key_reg: Some(k) }`
- Result register accumulates key-value pairs

### Functions

```rego
f(x, y) := x + y
```

- Parameters bound to registers 0..N-1 before body compilation
- `DestructuringSuccess {}` emitted after parameter validation
- Consistent parameter count enforced across all definitions
- After compilation, `FunctionInfo` recorded with param names

## Comprehension Compilation

All comprehensions follow the same pattern:

```
ComprehensionBegin { mode, collection_reg, body_start, end }
  [body: hoisted loops → statements → ComprehensionYield]
ComprehensionEnd {}
```

Modes: `Array`, `Set`, `Object`. The VM creates the appropriate
collection type and appends each yielded value.

**Context stack**: the compiler pushes a comprehension context to
track that yield should go to the comprehension (not the rule).

## Optimization Passes

### Constant Folding

`try_eval_const()` evaluates pure expressions at compile time:
- Array/Set/Object literals with all-constant elements
- Index operations on constant collections
- Result stored in literal table, emitted as `Load`

### Static Value Detection

After compiling all definitions of a complete rule, the compiler checks
if every definition yields the same static value. If so:
- `early_exit_on_first_success = true`
- VM stops after first successful definition body
- Common pattern: `default allow := false` + `allow := true { ... }`

### Literal Key Optimization

`obj["literal"]` compiles to `IndexLiteral { literal_idx }` instead of
loading the string into a register and using `Index`. Avoids a register
allocation and a `Load` instruction.

### Lazy Builtin Indexing

Builtins are assigned indices only when first used during compilation.
The builtin info table contains only actually-referenced builtins,
kept in deterministic order (BTreeMap).

## Compile-Time Safety

### Recursion Detection

The worklist's call stack detects compile-time recursion:
```
Rule A calls Rule B calls Rule A → error
```
This prevents infinite compilation loops for mutually recursive rules.

### Register Overflow

`alloc_register()` asserts `register_counter < 255`. If a rule body
requires more than 255 registers, compilation fails rather than silently
wrapping.

## Program Output

The compiler produces `Arc<Program>` containing:

```rust
struct Program {
    instructions: Vec<Instruction>,        // Bytecode stream
    literals: Vec<Value>,                  // Constant value table
    builtin_info_table: Vec<BuiltinInfo>,  // Referenced builtins
    rule_infos: Vec<RuleInfo>,             // Rule metadata
    entry_points: IndexMap<String, usize>, // Rule path → instruction offset
    instruction_data: InstructionData,     // Extended params tables
    span_infos: Vec<SpanInfo>,             // Source mapping (1:1 with instructions)
}
```

Every instruction has a corresponding `SpanInfo` for source mapping,
enabling debugging and IDE integration.

## Key Invariants

1. **Register 0 = result** — every rule's result is in register 0
2. **Input/data cache reset per definition** — prevents stale references
3. **Worklist ordering** — rules compiled in call-graph order
4. **Instruction ↔ SpanInfo 1:1** — every instruction has source location
5. **Literal table is append-only** — indices are stable after emission

## Common Pitfalls

1. **Scope nesting** — comprehensions and `every` push new scopes.
   Variables bound in inner scopes are not visible in outer scopes.

2. **Hoisted loop coordination** — the compiler must query the hoisting
   table for each statement to know which loops to emit. Missing a
   hoisted loop causes incorrect variable binding at runtime.

3. **Multi-definition rules** — each definition resets registers but
   shares the same `RuleInfo`. The `definitions` array in `RuleInfo`
   records instruction ranges for each definition.

4. **Function parameter count** — all definitions of a function must
   have the same number of parameters. The compiler enforces this.

5. **Builtin vs user function** — the compiler must distinguish builtin
   calls (which use `BuiltinCall` with the builtin registry) from user
   function calls (which use `FunctionCall` with the rule index).
