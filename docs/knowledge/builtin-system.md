<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Builtin System

Deep knowledge about regorus's builtin function infrastructure. Read this
before adding, modifying, or debugging builtin functions.

## Registration Pattern

Builtin functions live in `src/builtins/`. Each module exports a `register`
function that inserts entries into the `BUILTINS` lazy_static registry:

```rust
// In src/builtins/arrays.rs
pub fn register(m: &mut BuiltinsMap<&'static str, BuiltinFcn>) {
    m.insert("array.concat", (concat, 2));
    m.insert("array.reverse", (reverse, 1));
    m.insert("array.slice", (slice, 3));
}
```

The tuple is `(function_pointer, arity)`. The function signature is:

```rust
fn concat(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value>
```

Parameters:
- `span`: Source location for error messages
- `params`: AST expressions (for error reporting, not evaluation)
- `args`: Evaluated argument values
- `strict`: Whether strict builtin error mode is enabled

## Registration in BUILTINS

All builtin modules register in `src/builtins/mod.rs` via a `lazy_static!` block:

```rust
lazy_static::lazy_static! {
    pub static ref BUILTINS: BuiltinsMap<&'static str, BuiltinFcn> = {
        let mut m = BuiltinsMap::new();
        numbers::register(&mut m);
        strings::register(&mut m);
        // ...
        #[cfg(feature = "regex")]
        regex::register(&mut m);
        // ...
        m
    };
}
```

## Feature Gating

Optional builtins must be feature-gated at two levels:

**1. Cargo.toml** — declare the feature and optional dependency:
```toml
[features]
regex = ["dep:regex"]
```

**2. Registration** — gate the register call:
```rust
#[cfg(feature = "regex")]
regex::register(&mut m);
```

**3. Composite features** — add to `full-opa` and/or `opa-no-std` if the
builtin is part of the OPA specification:
```toml
full-opa = ["regex", ...]
opa-no-std = ["regex", ...]  # only if the dep supports no_std
```

## Argument Validation

Every builtin must validate argument count first:

```rust
fn concat(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "array.concat";
    ensure_args_count(span, name, params, args, 2)?;
    // ...
}
```

Then validate argument types. Use `ensure_*` helpers where available.

## OPA Conformance Requirements

**Error messages must match OPA exactly.** The OPA conformance test suite
(`tests/opa.rs`) compares error messages literally. This means:

- Function names in errors must match OPA's naming
- Error message format must match OPA's format
- Type error descriptions must match OPA's wording

If an error message doesn't match, the conformance test fails. When
implementing a builtin, compare against the OPA Go source for exact wording.

## Strict vs Non-Strict Mode

When `strict` is `true`:
- Type errors are hard errors (return `Err(...)`)
- Missing arguments are hard errors

When `strict` is `false`:
- Type errors return `Value::Undefined` (the OPA default)
- This matches OPA's behavior where type mismatches silently fail

## Undefined Argument Handling

Builtins receive `Value::Undefined` when an argument expression evaluates to
undefined. The interpreter checks this before calling:

```rust
if args.iter().any(|a| a == &Value::Undefined) {
    return Ok(Value::Undefined);
}
```

However, individual builtins may also need to handle Undefined for specific
semantic reasons.

## Both Execution Paths

Builtins are shared between the interpreter and the RVM. Both use the same
`BUILTINS` registry. When adding a builtin:

1. The interpreter calls builtins via `eval_builtin_call()`
2. The RVM resolves builtins by name from the same registry
3. No special RVM registration is needed — it's automatic

Test with both `cargo test` (interpreter) and RVM-specific tests.

## Adding a New Builtin: Checklist

1. Create the function in the appropriate `src/builtins/` module
2. Follow the `(span, params, args, strict) -> Result<Value>` signature
3. Call `ensure_args_count()` first
4. Feature-gate if it requires optional dependencies
5. Register in the module's `register()` function
6. Add the module's `register()` call in `src/builtins/mod.rs` (feature-gated)
7. Add to composite features (`full-opa`, `opa-no-std`) if OPA-standard
8. Write tests (YAML format, see `tests/interpreter/`)
9. Verify error messages match OPA exactly
10. Update `docs/builtins.md`
11. Run `cargo test --test opa` to verify OPA conformance
12. Run `cargo xtask ci-debug` for full suite

## Builtin Modules

The modules in `src/builtins/` cover:
- `aggregates` — count, sum, min, max, sort
- `arrays` — concat, reverse, slice
- `azure_policy` — Azure Policy-specific builtins (feature-gated)
- `bitwise` — bitwise operations (and, or, negate, shift)
- `comparison` — comparison operators (helper module, not separately registered)
- `conversions` — to_number
- `encoding` — base64, base64url, hex, json, yaml, urlquery
- `glob` — match (feature-gated)
- `graph` — walk, reachable (feature-gated)
- `http` — http.send stub (feature-gated)
- `net` — cidr_contains, cidr_intersects (feature-gated)
- `numbers` — arithmetic, rounding, abs, rem
- `objects` — get, keys, remove, union, filter
- `opa` — runtime info (feature-gated)
- `regex` — match, split, find (feature-gated)
- `semver` — is_valid, compare (feature-gated)
- `sets` — intersection, union, difference
- `strings` — concat, contains, replace, split, trim, format, sprintf
- `test` — internal test helpers (feature-gated: `opa-testutil`)
- `time` — now_ns, parse_ns, date, clock (feature-gated)
- `tracing` — trace, print
- `types` — type_name, is_number, is_string, etc.
- `units` — parse
- `uuid` — rfc4122 (feature-gated)
- `utils` — internal helpers

## LRU Caching

Some builtins use the LRU cache (`src/cache.rs`) for expensive compiled objects:
- **Regex patterns**: up to 256 cached compiled `regex::Regex` objects
- **Glob matchers**: up to 128 cached compiled `GlobMatcher` objects

The cache is global, thread-safe (mutex-protected), and configurable via
`cache::configure()`. The hard cap is 2^16 entries per cache type.
