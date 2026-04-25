<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Engine API

Deep knowledge about the public `Engine` API (`src/engine.rs`). Read this
before modifying the engine's public interface or evaluation flow.

## Engine Structure

```rust
pub struct Engine {
    modules: Rc<Vec<Ref<Module>>>,              // Loaded policy modules
    interpreter: Interpreter,                    // Execution engine
    prepared: bool,                             // Compilation state flag
    rego_v1: bool,                              // Language version
    execution_timer_config: Option<ExecutionTimerConfig>,
    policy_length_config: PolicyLengthConfig,    // File size limits
}
```

## Primary API Flow

### 1. Policy Loading

```rust
pub fn add_policy(&mut self, path: String, rego: String) -> Result<String>
pub fn add_policy_from_file(&mut self, path: impl AsRef<Path>) -> Result<String>
```

- Parses Rego source via Lexer → Parser → AST
- Returns the package name (e.g., `"data.test"`)
- Sets `prepared = false` to trigger recompilation on next eval
- Enforces `PolicyLengthConfig` limits

### 2. Data and Input

```rust
pub fn add_data(&mut self, data: Value) -> Result<()>  // Merge into data document
pub fn add_data_json(&mut self, data: &str) -> Result<()>
pub fn set_input(&mut self, input: Value)
pub fn set_input_json(&mut self, input: &str) -> Result<()>
pub fn clear_data(&mut self)
```

`add_data()` merges into the existing data document. It requires the value
to be an object (checked). Conflict detection on merge.

### 3. Evaluation

| Method | Returns | Use Case |
|--------|---------|----------|
| `eval_rule(rule)` | `Value` | Direct rule evaluation (fast) |
| `eval_query(query, tracing)` | `QueryResults` | OPA-compatible with bindings |
| `eval_bool_query(query)` | `bool` | Boolean shortcut |
| `eval_allow_query()` | `bool` | Common deny-by-default pattern |
| `eval_modules(tracing)` | `Value` | Evaluate all loaded modules |

### 4. Compilation (for repeated evaluation)

```rust
pub fn compile_for_target(&mut self) -> Result<CompiledPolicy>
pub fn compile_with_entrypoint(&mut self, rule: &Rc<str>) -> Result<CompiledPolicy>
```

Returns `CompiledPolicy` — an immutable, precompiled artifact that can be
evaluated many times with different inputs:

```rust
let compiled = engine.compile_for_target()?;
// Later, potentially in a different thread:
let result = compiled.eval_with_input(input)?;
```

### 5. Configuration

```rust
pub fn set_rego_v0(&mut self, enabled: bool)     // Language version
pub fn set_execution_timer_config(config)         // Timeout limits
pub fn set_policy_length_config(config)           // File size limits
pub fn set_strict_builtin_errors(b: bool)         // Error vs Undefined for type mismatches
pub fn add_extension(name, arity, func)           // Custom functions
```

## CompiledPolicy

```rust
pub struct CompiledPolicy {
    inner: Rc<CompiledPolicyData>,
}

struct CompiledPolicyData {
    modules: Rc<Vec<Ref<Module>>>,
    schedule: Option<Rc<Schedule>>,           // Pre-computed statement order
    rules: Map<String, Vec<Ref<Rule>>>,       // Rule path → rules
    default_rules: Map<String, Vec<...>>,     // Default rules
    imports: BTreeMap<String, Ref<Expr>>,
    functions: FunctionTable,                 // User-defined functions
    rule_paths: Set<String>,
    loop_hoisting_table: HoistedLoopsLookup,  // Pre-computed loop info
    data: Option<Value>,                      // Preloaded data
    strict_builtin_errors: bool,
    extensions: Map<String, (u8, Rc<Box<dyn Extension>>)>,
}
```

**Benefits of CompiledPolicy:**
- Schedule, loop hoisting, and function table pre-computed once
- Can be cloned cheaply (Rc internals)
- Supports repeated evaluation with different inputs
- Thread-safe when using `arc` feature

## Internal Evaluation Flow

When `eval_rule()` is called:

1. **Preparation** (if not `prepared`):
   - Gather all functions from modules → `FunctionTable`
   - Run scheduler on all queries → `Schedule`
   - Run loop hoister → `HoistedLoopsLookup`
   - Build `CompiledPolicyData`
   - Set `prepared = true`

2. **Interpreter setup**:
   - Set data and input on interpreter
   - Set current module context

3. **Evaluation**:
   - Find rule in `compiled_policy.rules`
   - Call `interpreter.eval_rule()`
   - Return result

## Multiple Module Management

- Modules stored as `Rc<Vec<Ref<Module>>>`
- Each module declares a package namespace (e.g., `package auth`)
- Rules qualified by package path: `data.auth.allow`
- Imports resolve cross-module references
- Functions tracked globally in `FunctionTable`

## Extensions API

Custom functions can be registered at runtime:

```rust
engine.add_extension(
    "custom.check".to_string(),
    2,  // arity
    Rc::new(Box::new(|args| -> Result<Value> {
        // implementation
    })),
)?;
```

Extensions are available to Rego policies as builtin functions.

## Metadata Access

```rust
pub fn get_packages(&self) -> Result<Vec<String>>      // Package names
pub fn get_policies(&self) -> Result<Vec<Source>>       // Policy sources
pub fn get_policies_as_json(&self) -> Result<String>    // JSON representation
pub fn get_coverage_report(&self) -> Result<Report>     // Code coverage
```

## Key Design Decisions

1. **Lazy compilation** — policies aren't compiled until first evaluation.
   `prepared` flag tracks whether compilation is needed.

2. **Data merging** — `add_data()` merges, doesn't replace. Multiple data
   sources accumulate into the data document.

3. **Input replacement** — `set_input()` replaces, doesn't merge. Each
   evaluation gets a fresh input.

4. **Clone semantics** — `Engine::clone()` clones all persistent state
   (policies, data, configuration) but resets runtime state (processed
   rules, caches). The clone is ready for independent evaluation.
