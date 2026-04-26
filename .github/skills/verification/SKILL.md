---
name: verification
description: >-
  Formal verification and memory safety verification for regorus. Use this
  skill when asked about Miri, formal verification, Z3, Verus, property
  testing, or when verifying safety properties of regorus code.
allowed-tools: shell
---

# Verification Skill

regorus uses multiple verification approaches to ensure correctness and
memory safety. This skill guides verification efforts.

## Verification Tiers

### Tier 1: Miri (Active — in CI)

Miri detects undefined behavior in unsafe code, memory leaks, and
concurrency bugs. regorus runs Miri in CI.

```bash
# Run Miri on the test suite
cargo +nightly miri test

# Run Miri on specific tests
cargo +nightly miri test -- test_name

# Run with stricter checks
MIRIFLAGS="-Zmiri-strict-provenance" cargo +nightly miri test
```

**What Miri catches:**
- Use-after-free, double-free
- Out-of-bounds memory access
- Uninitialized memory reads
- Data races (with `-Zmiri-check-stacked-borrows`)
- Memory leaks

**regorus context:** The core crate is `#![forbid(unsafe_code)]`, so Miri
is most relevant for FFI binding crates (`bindings/ffi/`) where unsafe is
allowed. Also useful for verifying `Rc::make_mut()` patterns.

### Tier 2: Property Testing (Recommended)

Use `proptest` or `quickcheck` to test properties that must hold for all
inputs:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn value_roundtrip(v in arb_value()) {
        let json = v.to_json_str();
        let parsed = Value::from_json_str(&json)?;
        prop_assert_eq!(v, parsed);
    }

    #[test]
    fn eval_deterministic(policy in arb_policy(), input in arb_input()) {
        let r1 = engine.eval(&policy, &input)?;
        let r2 = engine.eval(&policy, &input)?;
        prop_assert_eq!(r1, r2);
    }
}
```

**Properties worth testing in regorus:**
- Value serialization round-trips
- Evaluation determinism (same input → same output)
- Interpreter/RVM equivalence (both paths produce same result)
- Undefined propagation consistency
- Resource limit enforcement (instruction budget halts execution)
- RVM program serialization round-trips

### Tier 3: Z3 / SMT Solving (Planned)

For verifying policy properties symbolically:

- **Policy satisfiability**: is there any input that satisfies this policy?
- **Policy equivalence**: do two policies produce the same result for all inputs?
- **Policy subsumption**: does policy A imply policy B?
- **Unreachable rules**: are there rules that can never fire?

This connects to the partial evaluation vision in
`docs/knowledge/causality-and-partial-eval.md`.

### Tier 4: Verus (Planned)

Verus enables verified Rust — proving properties about Rust code at
compile time. Potential targets in regorus:

- **Value type invariants**: prove that Value operations preserve type safety
- **RVM instruction safety**: prove that well-formed programs cannot cause
  register overflow or invalid memory access
- **Scheduler correctness**: prove that topological sort produces valid order
- **Resource limit enforcement**: prove that instruction budget is checked

## Verification Strategies by Subsystem

### Value Type (`src/value.rs`)
- Property test: all operations handle Undefined correctly
- Property test: comparison is total ordering
- Property test: serialization round-trips for all Value variants
- Miri: Rc::make_mut patterns don't alias

### RVM (`src/rvm/`)
- Property test: program serialization round-trips
- Property test: instruction budget halts execution within bounds
- Property test: register allocation stays within frame bounds
- Miri: frame stack operations are memory-safe

### FFI (`bindings/ffi/`)
- Miri: handle create/destroy cycles don't leak
- Miri: panic containment doesn't cause UB
- Property test: poisoned engine rejects all operations

### Builtins (`src/builtins/`)
- Property test: builtins return Undefined (not error) for type mismatches
- Property test: time parsing matches OPA reference for valid inputs
- Property test: string operations handle UTF-8 edge cases

## Running Verification

```bash
# Tier 1: Miri
cargo +nightly miri test

# Tier 2: Property tests (if added)
cargo test --test prop_tests

# Full verification suite
cargo +nightly miri test && cargo test && cargo test --test opa --features opa-testutil
```

## Reference

- `docs/knowledge/policy-evaluation-security.md` — Security properties to verify
- `docs/knowledge/value-semantics.md` — Value invariants
- `docs/knowledge/rvm-architecture.md` — RVM safety properties
- `docs/knowledge/ffi-boundary.md` — FFI safety requirements
- `docs/knowledge/causality-and-partial-eval.md` — Symbolic analysis vision
