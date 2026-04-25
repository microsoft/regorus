---
name: add-builtin
description: >-
  Guide for adding new builtin functions to regorus. Use this skill when asked
  to add a new builtin, implement a missing OPA builtin, or extend the builtin
  system.
allowed-tools: shell
---

# Add Builtin Skill

Adding a builtin to regorus requires changes in multiple places and careful
attention to feature gating, type safety, and OPA conformance.

## Overview

Read `docs/knowledge/builtin-system.md` first for the full registration
architecture.

## Steps to Add a Builtin

### 1. Choose the Right Module

Builtins are organized by category in `src/builtins/`:

```
src/builtins/
  aggregates.rs    # count, sum, max, min, sort
  arrays.rs        # array.concat, array.slice, array.reverse
  bitwise.rs       # bits.and, bits.or, bits.negate, etc.
  casts.rs         # to_number
  comparison.rs    # opa.runtime
  conversions.rs   # units.parse, units.parse_bytes
  crypto.rs        # crypto.sha256, crypto.x509, etc.
  encoding.rs      # base64, json, yaml, hex, urlquery
  graphs.rs        # graph.reachable, graph.reachable_paths
  numbers.rs       # rand.intn, numbers.range, ceil, floor
  objects.rs       # object.get, object.union, object.filter
  regex.rs         # regex.match, regex.split, regex.find
  semver.rs        # semver.compare, semver.is_valid
  sets.rs          # intersection, union
  strings.rs       # concat, contains, sprintf, etc.
  time/            # time.now_ns, time.parse_ns, etc.
  types.rs         # is_string, is_number, type_name
  azure_policy/    # Azure Policy-specific builtins
```

Add your builtin to the appropriate existing module, or create a new module
if it represents a new category.

### 2. Implement the Function

```rust
fn my_builtin(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    // Validate argument count
    ensure_args_count(span, "my_builtin", params, args, expected_count)?;

    // Type-check arguments — return Undefined for type mismatches (not errors)
    let arg0 = match &args[0] {
        Value::String(s) => s,
        _ => return Ok(Value::Undefined),
    };

    // Implement the logic
    // ...

    Ok(result)
}
```

Key patterns:
- **Return `Value::Undefined`** for type mismatches (OPA semantics)
- **Return `Err`** only for genuine errors (wrong arg count, internal failure)
- **Use `strict` parameter** for strict mode behavior differences
- **Handle `Value::Undefined` inputs** — decide: propagate or treat as error

### 3. Register the Builtin

In the same module, add to the registration function:

```rust
pub fn register(m: &mut HashMap<&'static str, BuiltinFcn>) {
    m.insert("my_category.my_builtin", (my_builtin, 2));
    // ...
}
```

The tuple is `(function_pointer, expected_arg_count)`.

### 4. Feature Gate (if needed)

If the builtin depends on an optional crate or is language-specific:

```rust
#[cfg(feature = "my-feature")]
pub fn register(m: &mut HashMap<&'static str, BuiltinFcn>) {
    m.insert("my_category.my_builtin", (my_builtin, 2));
}
```

Update `Cargo.toml` if adding a new feature flag. Update
`docs/knowledge/feature-composition.md` with the new flag.

### 5. Add Tests

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_my_builtin_basic() { /* ... */ }

    #[test]
    fn test_my_builtin_undefined_input() {
        // Verify Undefined propagation behavior
    }

    #[test]
    fn test_my_builtin_type_mismatch() {
        // Verify returns Undefined, not error
    }

    #[test]
    fn test_my_builtin_edge_cases() {
        // Empty inputs, null, very large values, etc.
    }
}
```

### 6. Verify OPA Conformance

```bash
# Run conformance tests
cargo test --test opa --features opa-testutil

# If OPA test data exists for this builtin, verify it passes
cargo test --test opa --features opa-testutil -- my_builtin
```

### 7. Update Documentation

- Add the builtin to `docs/builtins.md`
- If it's complex, consider updating `docs/knowledge/builtin-system.md`

## Checklist

- [ ] Function implemented with correct signature
- [ ] Returns Undefined for type mismatches (not errors)
- [ ] Handles Undefined inputs correctly
- [ ] Registered with correct name and arg count
- [ ] Feature-gated if needed
- [ ] Unit tests cover: basic, undefined, type mismatch, edge cases
- [ ] OPA conformance tests pass
- [ ] Works in both interpreter and RVM
- [ ] Documentation updated
- [ ] Compiles with `--no-default-features` (if not feature-gated)

## Reference

- `docs/knowledge/builtin-system.md` — Full registration architecture
- `docs/knowledge/value-semantics.md` — Undefined propagation rules
- `docs/knowledge/feature-composition.md` — Feature flag guidance
- `src/builtins/` — Existing builtins as examples
