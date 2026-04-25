---
name: design-alternatives
description: >-
  Explore multiple design alternatives for a feature or change in regorus.
  Use this skill when asked to consider different approaches, evaluate
  tradeoffs, compare implementations, or when facing a non-trivial design
  decision. Generates and evaluates multiple candidates before recommending.
---

# Design Alternatives Skill

When facing a non-trivial design decision in regorus, don't commit to the
first approach that comes to mind. Generate multiple alternatives, evaluate
their tradeoffs against regorus's constraints, and recommend the best option.

## Strategy

### Phase 1: Understand the Problem

Before generating alternatives:

1. **Clarify the requirement** — what exactly must this achieve?
2. **Identify constraints** — which of regorus's constraints apply?
   - no_std compatibility
   - 9 FFI binding targets
   - Dual execution paths (interpreter + RVM)
   - Feature flag composition
   - Security-critical correctness
   - Performance at scale
3. **Read relevant knowledge files** from `docs/knowledge/`
4. **Study existing patterns** — how does the codebase solve similar problems?

### Phase 2: Generate Alternatives

Generate **at least 3 meaningfully different approaches**. Don't generate
trivial variations — each alternative should represent a genuinely different
design philosophy or tradeoff.

For each alternative, describe:
- **Approach**: what it does and how
- **Key design choice**: what makes this different from the others

Push yourself to consider:
- The obvious approach everyone would try first
- A simpler approach that sacrifices some capability
- A more sophisticated approach that handles more edge cases
- An approach that reuses existing infrastructure differently
- An approach from a different domain that could apply here

### Phase 3: Evaluate

Evaluate each alternative against these dimensions (weight by relevance
to the specific problem):

| Dimension | Description |
|-----------|-------------|
| **Correctness** | Can this be implemented correctly? How many edge cases? |
| **Security** | Attack surface? Resource bounds? Panic safety? |
| **Complexity** | How much code? How hard to understand and maintain? |
| **Performance** | Runtime cost? Memory cost? Scales with what? |
| **Compatibility** | Works with no_std? All FFI targets? All feature combos? |
| **Extensibility** | Easy to extend later? Blocks future plans? |
| **Testability** | Easy to test? Property-testable? |
| **Migration cost** | How much existing code must change? |
| **Risk** | What could go wrong? How bad is the failure mode? |

Be honest about tradeoffs. Every approach has weaknesses — name them
explicitly rather than advocating for a favorite.

### Phase 4: Recommend

1. **Rank** the alternatives
2. **Recommend** one with clear reasoning
3. **Identify risks** in the recommended approach
4. **Suggest mitigations** for those risks
5. **Note what to revisit** — decisions that should be reconsidered
   if assumptions change

If no alternative is clearly best, say so. Present the decision to the
user with the tradeoffs clearly laid out so they can make an informed choice.

## Example Decision Framework

For a decision like "how should we implement partial evaluation":

**Alternative A: AST-level transformation**
- Walk AST, evaluate ground subexpressions, leave symbolic ones
- Simple, reuses parser, but loses RVM optimizations

**Alternative B: RVM-level symbolic execution**
- Extend registers with symbolic values, execute normally
- Complex, but preserves all optimizations and is more precise

**Alternative C: Hybrid — compile then reduce**
- Compile to RVM, then do a simplification pass on bytecode
- Medium complexity, preserves compilation optimizations

Evaluate each against correctness (Undefined propagation!), complexity,
performance, and extensibility. The right answer depends on which
constraints matter most for this specific decision.

## Anti-Patterns

- **Don't generate strawmen** — every alternative should be genuinely viable
- **Don't evaluate only on your preferred dimension** — consider all
- **Don't hide tradeoffs** — if an approach is risky, say so clearly
- **Don't over-engineer** — sometimes the simplest approach is best
- **Don't ignore existing patterns** — the codebase has established idioms

## Reference

All knowledge files in `docs/knowledge/` are potentially relevant —
choose based on the subsystem being designed for. Key files:

- `docs/knowledge/rvm-architecture.md` — RVM design constraints
- `docs/knowledge/ffi-boundary.md` — FFI compatibility requirements
- `docs/knowledge/feature-composition.md` — Feature flag constraints
- `docs/knowledge/value-semantics.md` — Value type constraints
- `docs/knowledge/language-extension-guide.md` — Extensibility patterns
- `docs/knowledge/causality-and-partial-eval.md` — Future architecture vision
