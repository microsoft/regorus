---
name: opa-conformance
description: >-
  Check OPA conformance for regorus changes. Use this skill when modifying
  Rego evaluation, builtins, or anything that could affect OPA compatibility.
  Runs conformance tests and analyzes failures.
allowed-tools: shell
---

# OPA Conformance Skill

regorus aims for high conformance with the Open Policy Agent (OPA) reference
implementation. This skill helps verify that changes don't break conformance
and diagnose any failures.

## When to Use

- Modifying Rego evaluation (interpreter or RVM compiler)
- Adding or changing builtin functions
- Changing the Value type or its operations
- Modifying the parser or scheduler
- Any change where you're unsure if it affects Rego semantics

## Running Conformance Tests

```bash
# Full OPA conformance suite
cargo test --test opa --features opa-testutil

# Run with verbose output to see which tests pass/fail
cargo test --test opa --features opa-testutil -- --nocapture

# Run a specific conformance test category
cargo test --test opa --features opa-testutil -- test_name_pattern
```

## Analyzing Failures

When conformance tests fail:

1. **Read the test case** — OPA conformance tests are in `tests/opa/` and
   follow a standard structure: input, data, policy, expected result
2. **Identify the Rego feature** — which language feature does the failing
   test exercise? (comprehensions, `with`, negation, builtins, etc.)
3. **Check both execution paths** — run the failing test against both the
   interpreter and RVM to see if the failure is path-specific
4. **Compare with OPA spec** — the expected result comes from the OPA
   reference implementation. Understand why OPA produces that result.
5. **Check Undefined propagation** — the most common conformance failure
   is incorrect Undefined handling. Review `docs/knowledge/value-semantics.md`.

## Known Non-Conformance

Some OPA features are intentionally not supported or have known gaps.
Before investigating a failure, check if it's in a known category:

- Check `tests/` for any skip lists or known-failure annotations
- Check GitHub issues for tracked conformance gaps
- Some builtins may be feature-gated — ensure the right features are enabled

## After Fixing

After fixing a conformance issue:

1. Run the full conformance suite to ensure no regressions
2. Run `cargo test` for general test suite
3. Verify the fix works in both interpreter and RVM paths
4. Update `docs/knowledge/` if the fix reveals a subtle semantic rule

## Reference

- `docs/knowledge/rego-semantics.md` — Rego evaluation model
- `docs/knowledge/value-semantics.md` — Value type and Undefined
- `docs/knowledge/builtin-system.md` — Builtin registration and conformance
- `docs/knowledge/interpreter-architecture.md` — Interpreter details
- `docs/knowledge/rego-compiler.md` — RVM compiler details
