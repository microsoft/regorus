<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Tooling Architecture

How regorus's current architecture supports building language servers, linters,
analyzers, and other developer tooling. Read this when planning or implementing
tooling features.

## Foundational Infrastructure

### Span Tracking

Every AST node carries source location information:

```rust
pub struct Span {
    pub source: Source,    // File reference (Rc<SourceInternal>)
    pub line: u32,         // Line number (1-based)
    pub col: u32,          // Column number (1-based)
    pub start: u32,        // Byte offset in source
    pub end: u32,          // End byte offset
}
```

This enables precise error reporting, go-to-definition, hover information,
and diagnostic placement. Every expression, statement, rule, and module
carries a Span.

### AST Node Types

The AST (`src/ast.rs`) represents the full syntactic structure:

- 25+ `Expr` variants covering all expression types
- `LiteralStmt` for statements within rule bodies
- `Rule` with `RuleHead` (Compr, Set, Func) and bodies
- `Module` with package, imports, and policies
- `Query` for ordered statement lists

### Expression Indexing

Each node carries indices for O(1) lookup:
- `Expr.eidx` — unique expression index within module
- `LiteralStmt.sidx` — statement index within query
- `Query.qidx` — query index within module

These indices enable efficient mapping between AST nodes and compilation
artifacts (schedules, hoisted loops, binding plans).

### NodeRef Pattern

AST nodes use `NodeRef<T>` (wraps `Rc<T>`) with pointer-identity comparison:
```rust
pub struct NodeRef<T> { inner: Rc<T> }
// PartialEq/Eq use Rc::ptr_eq (pointer identity, not value equality)
```
This enables cheap cloning and sharing of AST subtrees, which is important
for tooling that needs to maintain multiple views of the AST.

## Language Server Capabilities

### Diagnostics (Errors and Warnings)

**Already available:**
- Parser errors with Span → precise source location for red squiggles
- Lexer errors with line/column → tokenization failures
- Scheduler errors → dependency cycle detection
- Type errors from builtins → argument type mismatches

**Possible additions:**
- Unused variable detection (scheduler tracks variable definitions/uses)
- Unreachable rule detection (via dependency analysis)
- Shadowing warnings (scope context tracks bindings)
- Style warnings (naming conventions, rule complexity)

### Completion

**What the AST provides:**
- Package/import declarations → suggest available packages
- Variable scope information → suggest in-scope variables
- Builtin function registry → suggest available builtins
- Rule paths → suggest available rules from data document

**What the scheduler provides:**
- Variable dependency analysis → which variables are defined at cursor position
- Scope boundaries → what's visible in the current context

### Go-to-Definition

**What Span tracking enables:**
- Every variable reference carries a Span
- Every rule definition carries a Span
- Imports link to package declarations
- Function calls link to function definitions

**Resolution path:**
1. Find AST node at cursor position (binary search on Span ranges)
2. Determine node type (variable, function call, import, etc.)
3. Look up definition in scope (variables), FunctionTable (functions),
   or module list (imports)
4. Return definition's Span

### Hover Information

**What the AST provides:**
- Expression type (from Value type system)
- Rule documentation (doc comments if added)
- Builtin function signatures (from BUILTINS registry)
- Variable origin (which statement defined it)

### Rename/Refactoring

**What expression indexing enables:**
- Find all references to a variable (scope analysis)
- Find all call sites for a function (FunctionTable)
- Find all imports of a package (import analysis)

## Linter Capabilities

### Static Analysis from Scheduler

The scheduler's dependency analysis provides:
- **Unused variables**: defined but never used
- **Circular dependencies**: variable cycles within rule bodies
- **Dead statements**: statements that can never execute (after always-failing stmt)

### Static Analysis from Scope Context

The compiler's scope analysis provides:
- **Variable shadowing**: same name in nested scope
- **Unbound variable access**: using a variable before it's defined
- **Import shadowing**: import overriding a local definition

### Static Analysis from AST

Direct AST inspection can detect:
- **Rule complexity**: number of statements, nesting depth, comprehension count
- **Naming conventions**: package names, rule names, variable names
- **Pattern violations**: using `=` where `:=` is preferred
- **Deprecated syntax**: v0 patterns that should use v1 syntax

### Type Analysis

While Rego is dynamically typed, partial type inference is possible:
- Literal types are known at parse time
- Builtin return types are documented
- Input/data schema (if provided) constrains types
- Type conflicts in comparison operations can be detected

## Analyzer Capabilities

### Policy Analysis

- **Entrypoint discovery**: find all rules that can be queried
- **Data dependency mapping**: which rules depend on which data paths
- **Input dependency mapping**: which rules depend on which input fields
- **Cross-module analysis**: how packages interact

### Performance Analysis

- **Instruction count estimation**: from RVM compilation
- **Loop complexity**: from hoisted loop analysis
- **Comprehension nesting**: depth of nested comprehensions
- **Virtual document chains**: how deep rule-as-data chains go

### Security Analysis

- **Undefined propagation paths**: where undefined values could affect decisions
- **Missing default rules**: rules without fallback values
- **Unbounded iteration**: loops without explicit bounds
- **Resource limit coverage**: which evaluation paths enforce limits

## Partial Evaluation (Future)

Partial evaluation reduces a policy given known inputs while leaving unknown
parts symbolic. This enables:

- **Policy optimization**: pre-evaluate the known parts at compile time
- **Policy simplification**: show users what a policy "means" for their context
- **Incremental evaluation**: only re-evaluate changed parts

### Design Considerations

The current architecture supports partial evaluation through:
- **RVM's register model**: registers could hold symbolic values
- **Scheduler dependency analysis**: identifies independent subexpressions
- **Value type**: could be extended with a `Symbolic` variant
- **Compilation pipeline**: could produce residual programs with "holes"

### Requirements for Implementation

1. **Symbolic Value type**: extend `Value` with symbolic representation
2. **Partial evaluation pass**: walk AST, evaluate ground subexpressions,
   leave symbolic subexpressions
3. **Residual program**: output a simplified policy/program
4. **Correctness guarantee**: partial evaluation must preserve semantics

## Causality Tracking (Future)

Understanding why a policy produced its result:

### What Exists Today

- **Coverage tracking** (`coverage` feature): records which expressions
  were evaluated during a query
- **Tracing** (`eval_query(query, tracing=true)`): captures evaluation steps
- **RVM frame stack**: in suspendable mode, provides execution history
- **Active rules stack**: tracks rule evaluation chain

### What's Needed

1. **Decision tree**: which rules contributed to the final result
2. **Value provenance**: where each value came from (input, data, rule)
3. **Counterfactual analysis**: "what if this input were different?"
4. **Human-readable explanations**: translate decision path to English

### Architecture Implications

- Evaluation functions need optional "trace" parameters
- The Value type may need provenance metadata
- The RVM could log instruction-level execution traces
- The interpreter's context stack already tracks rule contributions
- Memory overhead must be opt-in (not in production fast path)
