<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Causality and Partial Evaluation

Design considerations for future causality tracking and partial evaluation
features. These are not yet implemented but the architecture is being
designed to support them. Read this when making architectural decisions
that may affect these future capabilities.

## Partial Evaluation

### What It Is

Partial evaluation reduces a policy given **known** inputs while leaving
**unknown** parts symbolic:

```
Full policy + known data + unknown input
    → Simplified policy (only depends on unknown input)
```

Example:
```rego
allow {
    input.role == "admin"       # Unknown (depends on input)
    data.feature_enabled        # Known: true
    input.department in {"eng", "security"}  # Unknown
}
```

Partial evaluation with `data.feature_enabled = true`:
```rego
allow {
    input.role == "admin"
    input.department in {"eng", "security"}
}
```

The `data.feature_enabled` check is eliminated because it's always true.

### Use Cases

1. **Policy optimization**: pre-evaluate known parts at compile/load time
2. **Policy simplification**: show users what a policy means for their context
3. **Incremental evaluation**: only re-evaluate changed parts
4. **Query planning**: push policy decisions closer to data sources
5. **Policy diffing**: compare simplified policies across configurations

### Current Architecture Support

**Scheduler dependency analysis**: The scheduler already identifies which
statements depend on which variables. Statements that only depend on known
variables can be evaluated. Statements with unknown dependencies remain
symbolic.

**RVM register model**: Registers could hold symbolic values alongside
concrete ones. Instructions that operate on symbolic values produce symbolic
results.

**Value type extensibility**: The `Value` enum could be extended:
```rust
pub enum Value {
    // ... existing variants ...
    Symbolic(SymbolicExpr),  // Future: represents an unknown value
}
```

**Compilation pipeline**: The hoister and scheduler already separate
ground-truth computations from data-dependent ones. This separation is
the foundation for partial evaluation.

### Design Principles

1. **Preserve semantics**: partially evaluated policy must produce identical
   results to the original when the remaining unknowns are bound.

2. **Undefined handling**: partial evaluation must correctly propagate
   Undefined through symbolic expressions. This is the hardest part —
   `not Undefined = true` means symbolic undefined propagation has
   non-obvious results.

3. **No information loss**: the residual policy must capture all constraints,
   including those that were partially evaluated.

4. **Composability**: partial evaluation results should be further partially
   evaluatable as more inputs become known.

### Implementation Considerations

**Phase 1: Ground-truth elimination**
- Identify statements where all variables are known
- Evaluate them and replace with results
- Remove always-true conditions, eliminate always-false rule bodies
- This is the easiest phase and provides immediate value

**Phase 2: Symbolic propagation**
- Track symbolic values through expressions
- Simplify expressions where possible (e.g., `true AND x` → `x`)
- Handle Undefined propagation symbolically
- Generate residual policy/program

**Phase 3: Cross-rule analysis**
- Partially evaluate virtual documents
- Propagate known rule results into dependent rules
- Handle default rules in partial context

### Challenges

- **Undefined propagation**: `not (Undefined)` = `true` makes symbolic
  analysis non-trivial. A symbolic expression that might be Undefined
  has different semantics under negation.

- **Set/Object construction**: if any element is symbolic, the entire
  collection construction may need to remain symbolic.

- **Comprehensions**: partial evaluation of comprehensions requires
  knowing which iterations are ground vs symbolic.

- **Builtins**: some builtins are pure (suitable for partial evaluation),
  others have side effects or depend on runtime state (`time.now_ns()`).

## Causality Tracking

### What It Is

Causality tracking answers **why** a policy produced its result:
- Which rules contributed to the decision?
- What input/data values were decisive?
- What would need to change to get a different result?

### Use Cases

1. **Audit**: prove why a request was allowed/denied
2. **Debugging**: understand unexpected policy decisions
3. **Compliance**: demonstrate that decisions follow documented logic
4. **Counterfactual**: "what if the user had role X instead of Y?"

### Current Infrastructure

**Coverage tracking** (`coverage` feature):
- Records which expressions were evaluated
- Binary: evaluated or not evaluated
- Doesn't track values or decision flow

**Tracing** (`eval_query(query, tracing=true)`):
- Captures evaluation steps
- Provides more detail than coverage
- Performance cost limits production use

**RVM frame stack** (suspendable mode):
- Frame-by-frame execution history
- Instruction-level granularity available via single-step mode
- Only in suspendable mode (not run-to-completion)

**Active rules stack** (interpreter):
- Tracks which rules are currently being evaluated
- Used for cycle detection
- Could be repurposed for causality

### Design Vision

#### Decision Tree

A tree structure recording the evaluation path:

```
allow = true
├── Rule: data.auth.allow (body 1 succeeded)
│   ├── Statement: input.role == "admin" → true
│   │   └── input.role = "admin" (from input)
│   └── Statement: input.active == true → true
│       └── input.active = true (from input)
└── Default: data.auth.deny = false (not triggered)
```

#### Value Provenance

Track where each value came from:
- `input.role` → from user input
- `data.allowed_roles` → from data document loaded at path X
- `count(data.items)` → computed by builtin from data

#### Counterfactual Analysis

"What would change if `input.role` were `"viewer"` instead?"
- Re-evaluate with modified input
- Compare decision trees
- Report which statements changed outcome

### Architecture Implications

1. **Opt-in overhead**: causality tracking adds memory and CPU cost.
   Must be behind a feature flag or runtime configuration. Never in
   the hot path for production evaluation.

2. **Value annotation**: Values may need optional metadata:
   ```rust
   struct AnnotatedValue {
       value: Value,
       provenance: Option<Provenance>,  // Where it came from
   }
   ```

3. **Evaluation hooks**: the interpreter/RVM need "observation points"
   where causality information is recorded. These should be no-ops
   when tracking is disabled.

4. **Serializable traces**: decision trees and provenance information
   need to be serializable (JSON) for audit logging and external
   tooling.

5. **Deterministic replay**: for counterfactual analysis, the evaluation
   must be deterministic. This means:
   - `time.now_ns()` must be mockable
   - Random builtins must be seedable
   - External data must be snapshotted

### Connection to Partial Evaluation

Causality and partial evaluation complement each other:
- Partial evaluation identifies the **relevant** parts of a policy
- Causality tracking explains the **decisions** within those parts
- Together they answer: "given what we know, what decisions were made and why?"

## Design Principles for Both Features

1. **Keep evaluation logic pure** — side-effect-free functions are easier
   to partially evaluate and track causally.

2. **Document invariants explicitly** — invariants that hold during
   evaluation are the foundation for symbolic reasoning.

3. **Prefer exhaustive pattern matching** — every case handled explicitly
   makes symbolic analysis tractable.

4. **Separate observation from computation** — tracking infrastructure
   should be orthogonal to evaluation logic.

5. **Correct today, analyzable tomorrow** — current code should be
   designed so these features can be added without fundamental restructuring.
