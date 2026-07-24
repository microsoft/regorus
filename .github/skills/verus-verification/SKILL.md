---
name: verus-verification
description: >-
  Rigorous Verus specification and proof work for Regorus. Use when adding,
  strengthening, debugging, or reviewing Verus contracts, proofs, external-body
  boundaries, assume_specification declarations, BigInt or Number models, or
  minimal Verus bug reproducers. Preserves executable behavior while minimizing
  trusted assumptions and verifier workarounds.
---

# Regorus Verus Verification

Use this workflow for proof-oriented changes in Regorus, especially `Number`,
`BigInt`, arithmetic, conversions, and policy-critical value semantics.

The objective is not merely to make Verus pass. The objective is to establish an
exact, useful contract for the real executable implementation with the smallest
honest trusted boundary.

## Core Rules

1. **Specify executable semantics exactly.**
   - Model every meaningful result variant and error path.
   - Preserve distinctions such as integer versus float representation.
   - For floating-point operations, specify IEEE-754 behavior rather than ideal
     real arithmetic.
   - Do not weaken a contract just because the stronger proof is inconvenient.

2. **Prove bodies whenever Verus supports them.**
   - Prefer a verified implementation over `assume_specification`.
   - Remove a trusted assumption once the implementation carries a proved spec.
   - Never describe an `external_body` function as body-proved.

3. **Preserve executable behavior.**
   - Before editing, compare the function with `main` or the relevant base.
   - Keep executable statements unchanged unless the task explicitly requires a
     runtime fix.
   - Never use conditional compilation to give Verus and ordinary Rust different
     executable bodies or behavior. If Verus cannot verify the shared body,
     retain the narrowest `external_body` boundary and document the unsupported
     construct.
   - Put ghost reasoning in `proof!` blocks. Move proof work to the beginning of
     the function when it depends only on inputs.
   - Afterward, inspect the focused diff against the base and confirm that only
     contracts and erased proof code differ, unless a runtime change was intended.

4. **Do not use preconditions to hide valid edge cases.**
   - Check minimum signed values, maximum values, zero, and representation
     boundaries explicitly.
   - Negating `i32::MIN` as `i32` overflows, but its magnitude $2^31$ fits in
     `u32`. Widen before negation, for example `(-(e as i64)) as u32`.
   - If the API can compute a valid result, prove and compute it instead of
     excluding the input or returning an invented error.

5. **Reuse existing semantic models.**
   - Search `src/verify/` before adding an uninterpreted spec function.
   - Prefer established models such as `pow2`, `NumberView`,
     `spec_to_f64_lossy`, and BigInt view/spec traits.
   - If the same mathematical value can have representation-dependent runtime
     behavior, quantify over the concrete modeled value rather than pretending
     the view alone determines the result.

6. **Minimize and explain trust.**
   - Use `external_body` only at the smallest unsupported boundary.
   - Give an exact postcondition, not merely positivity or successful return,
     whenever downstream proofs depend on exact behavior.
   - Add a short comment naming the concrete verifier limitation, for example:
     overloaded `<<=`/`>>=` is unsupported, or overloaded `!` on external
     `BigInt` crashes this Verus version.
   - Avoid broad external wrappers around otherwise verifiable callers.

## Workflow

### 1. Establish the Runtime Baseline

Start with the function, its helper contracts, its callers, and any existing
trusted specification.

```bash
git show main:path/to/file.rs
rg -n 'function_name|assume_specification|relevant_helper' src tests
```

Record one falsifiable hypothesis:
- what the exact behavior should be;
- which helper contracts it depends on;
- the cheapest verification or runtime check that could disprove it.

Do not map the whole subsystem before making a small grounded edit.

### 2. Write the Contract Before the Proof

The contract should answer:
- Which inputs return `Ok`, `Err`, `Some`, or `None`?
- What exact mathematical value is represented?
- Is the result an integer or float variant?
- Which rounding, overflow, saturation, or lossy-conversion rule applies?
- Are multiple concrete representations possible for the same view?

For arithmetic returning `Result`, avoid vague contracts such as only
`result is Ok` when the exact value is knowable.

For BigInt operators, provide exact operator models and prove the caller against
them. For division producing a float, model the exact lossy conversions used by
the executable code.

### 3. Remove Redundant Trust

Search for existing assumptions:

```bash
rg -n 'assume_specification.*function_name|uninterp spec fn' src/verify src
```

When moving a spec onto a body-verified function:
- delete the old `assume_specification` in the same change;
- ensure no duplicate specification remains;
- strengthen helper contracts only as much as the body proof requires.

An external helper may remain trusted when Verus cannot translate its syntax,
but its contract must expose all facts needed by verified callers.

### 4. Keep Proofs Separate From Execution

Prefer this shape:

```rust
pub fn operation(input: i32) -> Result<Number> {
    proof! {
        // Input-only lemmas, cast equalities, and arithmetic facts.
    }

    // Original executable body.
}
```

Use local proof blocks later only when facts genuinely depend on an executable
value produced at that point.

Do not introduce executable temporaries solely to help a proof. If a temporary
is ghost-only, keep it inside `proof!`.

### 5. Handle Casts and Boundaries Explicitly

Verus often needs explicit facts connecting machine integers and mathematical
integers/naturals:

```rust
assert((e as u32) as nat == e as nat);
```

For negative signed values, widen before negating:

```rust
let magnitude = (-(e as i64)) as u32;
```

Then prove:
- the magnitude is positive;
- its cast equals the intended mathematical magnitude;
- required power/division lemmas apply;
- remainder is nonzero when the runtime should choose floating division.

Check memory implications separately. A mathematically valid BigInt may be very
large. Prove extreme paths, but do not execute resource-heavy regression tests
unless the cost is acceptable and intentional. Test the conversion and a smaller
representative behavior instead.

### 6. Use Verification Attributes Deliberately

- `#[verus_verify]` on an `impl` applies to all methods in that impl.
- Do not split adjacent inherent impls merely to change verification scope when
  one impl-level annotation plus narrow method overrides is clearer.
- Use `#[verus_verify(external)]` only when an item must remain entirely outside
  verification and has a separate specification.
- Use `#[verus_verify(external_body)]` when Verus should trust a stated contract
  but cannot verify the implementation body.
- Method-level attributes can override the impl-wide default.

Before diagnosing missing internal markers or macro bugs, inspect braces and
attributes. Confirm the method is actually inside the annotated impl.

## Diagnosing Verus Failures

### Translation or Compiler Failure

1. Reduce to the exact operator, type, attribute, and impl context.
2. Test a one-file reproducer with the same relevant structure.
3. Do not introduce macros, missing impl annotations, or different ownership
   patterns unless they exist in the failing code.
4. If a small candidate passes, it is not a reproducer. Keep reducing the real
   context or state that the failure was caused by local annotation structure.
5. Inspect `~/verus` only after the local code path is understood.

A valid verifier bug report must:
- fail on the stated Verus version;
- contain no unrelated repository dependencies when avoidable;
- reproduce the same failure mechanism;
- document any workaround retained in Regorus.

### Proof Failure

Treat the first focused failure as evidence:
- failed arithmetic safety means the implementation has an unhandled machine
  boundary or needs a justified precondition;
- failed postcondition may indicate a missing helper fact, a representation
  mismatch, or an incorrect contract;
- unsupported library internals should be isolated in the narrowest helper, not
  used to externalize the verified caller.

Do not respond to a failed proof by immediately weakening the postcondition.
First trace a concrete input through the runtime behavior.

## Validation

After the first substantive edit, immediately run the narrowest check:

```bash
cargo verus verify --features verus \
  --fwd-verus-args-to roots -- --verify-module number
```

Use a fresh target directory when checking for stale macro or compiler behavior.

After the focused proof passes:

```bash
cargo test focused_test_name
cargo fmt --all -- --check
git diff --check
```

For broader or final validation, use repository commands as appropriate:

```bash
cargo xtask fmt
cargo xtask clippy
cargo xtask ci-debug
```

Report verification counts accurately. Distinguish:
- body-verified functions;
- external-body contracts;
- trusted assumptions;
- runtime tests actually executed;
- extreme tests skipped due to resource cost.

## Completion Checklist

- [ ] Contract matches exact executable semantics.
- [ ] Integer/float and `Undefined` distinctions remain intact where relevant.
- [ ] Minimum/maximum signed values and casts were considered.
- [ ] Original executable body is preserved unless a runtime bug was fixed.
- [ ] Proof-only code is inside `proof!` and placed early when possible.
- [ ] No redundant uninterpreted helper or trusted assumption remains.
- [ ] Every `external_body` has the narrowest useful exact contract and a reason.
- [ ] Impl-level verification annotations cover the intended methods without
      unnecessary splits.
- [ ] Any claimed verifier reproducer is representative and independently fails.
- [ ] Focused Verus verification passes.
- [ ] Relevant runtime tests, formatting, and diff checks pass.
