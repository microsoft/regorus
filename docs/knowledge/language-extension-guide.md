<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Language Extension Guide

How to add new policy languages to regorus. Read this when implementing
support for a new policy language or modifying the language extension
architecture.

## Current Architecture

Regorus supports multiple policy languages through `src/languages/`:

```
src/languages/
  azure_policy/     JSON-based declarative constraints → RVM bytecode
  azure_rbac/       Condition expression strings → direct interpretation
  rego/             Rego source → RVM bytecode (via core compiler)
```

Each language has its own:
- **Parser**: language-specific syntax → AST
- **AST types**: language-specific node types with Span tracking
- **Compilation or interpretation**: AST → RVM bytecode OR direct evaluation
- **Feature flag**: compile-time opt-in

### No Shared Trait (Yet)

There is **no common trait** defining language behavior. Each language
provides its own entry points:

- Azure Policy: `parser::parse_policy_rule()` → `compiler::compile_policy_rule()`
- Azure RBAC: `parser::parse_condition_expression()` → `ConditionInterpreter::evaluate_str()`
- Rego: integrated into the core `Engine` via `Lexer → Parser → Interpreter/RVM`

This is an adapter pattern — each language adapts to the shared infrastructure
in its own way. A formal trait may be introduced as more languages are added.

### Two Execution Strategies

**Strategy 1: Compile to RVM** (Azure Policy, Rego)
- Parse to language-specific AST
- Compile to shared `Program` (RVM bytecode)
- Execute on the shared VM
- Benefits: shared optimization, serialization, instruction budget enforcement

**Strategy 2: Direct interpretation** (Azure RBAC)
- Parse to language-specific AST
- Evaluate directly with a language-specific interpreter
- Benefits: simpler for expression-oriented languages, no compilation overhead

## Adding a New Language

### Step 1: Feature Flag

```toml
# Cargo.toml
[features]
my_language = ["dep:optional-dep-if-needed"]
```

### Step 2: Module Structure

```
src/languages/my_language/
  mod.rs            Module root, public exports
  ast/              Language-specific AST types
    mod.rs          Node types with Span tracking
  parser/           Language-specific parser
    mod.rs          Entry point: parse() → AST
  compiler/         If compiling to RVM (Strategy 1)
    mod.rs          compile() → Rc<Program>
  interpreter.rs    If direct interpretation (Strategy 2)
  builtins/         Language-specific builtin functions (if any)
```

### Step 3: Register in `src/lib.rs`

```rust
pub mod languages {
    #[cfg(feature = "my_language")]
    pub mod my_language;
    // ... existing languages
}
```

### Step 4: Integration Points

**If compiling to RVM:**
- Produce a `Program` struct (same as Rego/Azure Policy)
- Populate metadata with language identifier
- The shared VM executes the program
- Benefits from instruction budget, time limits, memory limits

**If direct interpretation:**
- Implement an interpreter that evaluates against provided context
- Must enforce resource limits manually (time, memory)
- Must handle errors consistently with other languages

### Step 5: Engine Integration

Add methods to `Engine` (feature-gated) for loading and evaluating the
new language:

```rust
#[cfg(feature = "my_language")]
pub fn add_my_language_policy(&mut self, source: String) -> Result<()> {
    let ast = languages::my_language::parser::parse(&source)?;
    let program = languages::my_language::compiler::compile(&ast)?;
    // ... integrate with engine
    Ok(())
}
```

## Shared Infrastructure

New languages can reuse:

| Component | Location | What it provides |
|-----------|----------|-----------------|
| **Value type** | `src/value.rs` | Shared data representation |
| **Number type** | `src/number.rs` | High-precision arithmetic |
| **RVM** | `src/rvm/` | Bytecode execution engine |
| **Builtins** | `src/builtins/` | Shared builtin functions |
| **Span** | `src/ast.rs` | Source location tracking |
| **Limits** | `src/utils/limits/` | Time, memory, execution limits |
| **Cache** | `src/cache.rs` | LRU caching for compiled patterns |
| **Engine** | `src/engine.rs` | Policy management, data/input handling |

## Design Considerations for New Languages

### AST Design

- Every node should carry a `Span` for error reporting
- Use `Ref<T>` (Rc-based) for shared ownership
- Keep AST types in a dedicated `ast/` module

### Parser Design

- Recursive descent is the standard pattern in regorus
- Enforce depth limits (default 32) to prevent stack overflow
- Check memory limits during parsing
- Track line/column for error messages

### Compilation Design

If targeting the RVM:
- Allocate registers for intermediate values
- Use the literal table for constants
- Define entry points for each evaluatable unit
- Populate metadata (language name, version, etc.)
- Run `validate_limits()` on the generated program

### Error Design

- Use `thiserror` for language-specific error types
- Include source location (Span) in all errors
- Don't leak sensitive information in error messages
- Consider error recovery for better diagnostics

### Testing

- Create YAML test cases in `tests/` or language-specific test directory
- Cover: normal operation, edge cases, error conditions, resource limits
- Verify against reference implementation if one exists

## Future Directions

### Language Server Protocol (LSP)

The AST and Span infrastructure supports building language servers:
- **Completion**: AST traversal for scope-aware suggestions
- **Diagnostics**: Parser/compiler errors with source locations
- **Go to definition**: Span tracking enables precise navigation
- **Hover**: AST node identification for type/documentation info

### Linters and Analyzers

The compilation pipeline enables static analysis:
- **Scheduler output**: dependency analysis for unused variables
- **Scope analysis**: detect shadowing, unused imports
- **Type inference**: Value type tracking through expressions
- **Complexity analysis**: rule depth, statement count, loop nesting

### Partial Evaluation

Not currently implemented but the architecture supports it:
- The RVM's register-based design could track symbolic values
- The scheduler's dependency analysis identifies independent subexpressions
- Compilation could produce partially-evaluated programs with "holes"
- Design principle: keep evaluation logic pure and side-effect-free

### Causality Tracking

Understanding WHY a policy decision was made:
- The RVM's instruction-level execution could log decision paths
- The interpreter's context stack tracks which rules contributed
- Frame-level tracing in suspendable mode provides execution history
- Coverage tracking (`coverage` feature) already records evaluated expressions
