---
name: security-review
description: >-
  Security-focused review for regorus changes. Use this skill when asked to
  do a security review, threat analysis, or when reviewing changes to FFI
  boundaries, resource limits, policy evaluation, or dependency updates.
allowed-tools: shell
---

# Security Review Skill

regorus is a security-critical policy evaluation engine. Policy evaluation
bugs can lead to incorrect access control decisions at Azure scale. This skill
provides a security-focused review lens.

## Threat Model

regorus evaluates **untrusted policies and inputs** provided by external users.
The engine must:

1. **Produce correct results** — a wrong allow/deny is a security bug
2. **Not crash** — panics in FFI contexts poison the engine permanently
3. **Bound resource usage** — adversarial inputs must not cause DoS
4. **Maintain isolation** — evaluation of one policy must not affect another
5. **Protect the host** — no arbitrary code execution, file access, or network access

## Review Approach

Think adversarially. For each change, ask:

### Policy Evaluation Correctness

- Could this change cause a policy to evaluate to a different result?
- If the result changes, is that the correct behavior per specification?
- What happens with edge-case inputs: empty, null, very large, deeply nested?
- What happens when values are Undefined? (`not Undefined = true`)
- Are default rules affected?

### Resource Exhaustion

- Does this introduce unbounded iteration (no instruction budget check)?
- Does this allocate memory proportional to untrusted input size?
- Does this add recursion without depth bounds?
- Can an adversarial policy trigger O(n²) or worse behavior?
- RVM instruction budget is 25,000 — does this change affect instruction
  count significantly for common policies?

### Panic Safety

- Can this code path panic? (`.unwrap()`, `.expect()`, index `[i]`,
  integer overflow via `as` casts, slice out of bounds)
- Is this reachable from FFI? (If so, panic = permanent engine poisoning)
- Are all match arms exhaustive?
- Are arithmetic operations checked? (`checked_add`, `saturating_mul`, etc.)

### FFI Boundary

If the change touches public API or FFI:
- Does the handle pattern remain safe? (`Box::into_raw` / `Box::from_raw`)
- Is `with_unwind_guard()` used for panic containment?
- Do all 9 binding languages handle the change correctly?
- Are error codes and status values consistent?
- Could a binding language misuse the new API in a way that causes UB?

### Supply Chain

If dependencies change:
- Is the new dependency necessary?
- Does it have known vulnerabilities? (`cargo audit`)
- Does it use `unsafe`? How much?
- Is it maintained? How many maintainers?
- Does it support `no_std` with `default-features = false`?
- Could it be replaced with a smaller, more focused crate?

Run: `cargo audit` and `cargo deny check` after dependency changes.

### Feature Flag Safety

- Does this compile with `--all-features`?
- Does this compile with `--no-default-features`?
- Does the `arc` feature (Rc→Arc) work correctly with this change?
- Are `#[cfg(...)]` guards correct and complete?

## Automated Security Checks

```bash
# Dependency audit
cargo audit

# Dependency policy check
cargo deny check

# Clippy with all features (catches unsafe patterns)
cargo clippy --all-features -- -D warnings

# Clippy with no features (no_std safety)
cargo clippy --no-default-features -- -D warnings

# Miri for memory safety (if nightly available)
cargo +nightly miri test
```

## Severity Assessment

For each finding, assess:

- **Impact**: what's the worst case if exploited?
- **Exploitability**: can an external user trigger this?
- **Scope**: how many deployments are affected?

In regorus, most evaluation bugs are high-impact because they affect
policy decisions across all deployments using the engine.

## Reference

- `docs/knowledge/policy-evaluation-security.md` — DoS protection, limits
- `docs/knowledge/ffi-boundary.md` — Handle pattern, panic containment
- `docs/knowledge/feature-composition.md` — Feature flag interactions
- `docs/knowledge/value-semantics.md` — Undefined propagation (security-relevant)
