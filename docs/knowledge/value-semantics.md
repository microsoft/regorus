<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Value Semantics

Deep knowledge about regorus's `Value` type, `Undefined` propagation, and
three-valued logic. Read this before modifying `src/value.rs`, `src/number.rs`,
or any evaluation code.

## The Value Enum

```rust
pub enum Value {
    Null,                              // JSON null
    Bool(bool),                        // JSON boolean
    Number(Number),                    // u64 | i64 | f64 | BigInt — at least 100-digit precision
    String(Rc<str>),                   // Shared, cheap to clone
    Array(Rc<Vec<Value>>),             // Ordered collection
    Set(Rc<BTreeSet<Value>>),          // Ordered set (no JSON equivalent)
    Object(Rc<BTreeMap<Value, Value>>),// Keys can be any Value, not just strings
    Undefined,                         // Absence of value — NOT the same as Null or false
}
```

All collection variants use `Rc` (or `Arc` with the `arc` feature). Cloning a
Value is a refcount bump. Use `Rc::make_mut()` for copy-on-write mutation.

**Implementation note:** Rego does NOT require ordered sets or objects. The
current use of `BTreeSet` and `BTreeMap` provides deterministic ordering but
this is an implementation detail, not a semantic requirement. The Value
representation may change in the future (e.g., to hash-based collections for
performance). Do not write code that depends on iteration order of Sets or
Objects — treat them as unordered collections.

## The Number Type

`src/number.rs` represents numbers as one of four internal representations:

| Variant | Range | Use case |
|---------|-------|----------|
| `UInt(u64)` | 0 to 2^64-1 | Non-negative integers |
| `Int(i64)` | -2^63 to 2^63-1 | Negative integers |
| `Float(f64)` | IEEE 754 | Fractional values |
| `BigInt(Rc<BigInt>)` | Arbitrary | Overflow from u64/i64 |

**Invariants:**
- `from_bigint_owned()` normalizes: if a BigInt fits in i64/u64, it stores the
  smaller representation.
- Float comparison uses the `Number` type's methods, never raw `==` on f64
  (denied by `clippy::float_cmp`).
- `F64_SAFE_INTEGER = 2^53` — beyond this, float loses integer precision.
- Arithmetic between variants promotes correctly (e.g., UInt + Int → Int or BigInt).

**Never do raw arithmetic on Number internals.** Use the type's methods — they
handle precision, overflow, and type promotion.

## Undefined: The Critical Concept

**`Undefined` is NOT `false`. `Undefined` is NOT `Null`.** Rego has three-valued
logic where expressions can be true, false, or undefined (absent).

This is the single richest source of subtle bugs in regorus.

### Propagation Rules

**Boolean and comparison operations** (`src/interpreter.rs:618-676`):
```
Undefined <op> anything  →  Undefined
anything <op> Undefined  →  Undefined
```
Both operands must be defined for the operation to produce a result.

**Negation** (`not`):
```
not true      →  false
not false     →  true
not Undefined →  true    ← THIS IS THE TRAP
```
`not Undefined` evaluates to `true` because negating "absence" means "the
condition wasn't met" which is truthy in Rego. This is correct OPA semantics
but extremely subtle.

**Reference chains** (`a.b.c`):
If any intermediate key is missing or Undefined, the entire chain returns
Undefined. The interpreter navigates the path and returns Undefined at the
first missing component.

**Collection construction** (Array, Set, Object literals):
```
[1, Undefined, 3]  →  Undefined    (entire collection is Undefined!)
```
If ANY element in a collection literal is Undefined, the entire collection
becomes Undefined. This is NOT intuitive — it doesn't skip the undefined
element, it poisons the whole result.

**Builtin function arguments**:
```
builtin(x, Undefined, z)  →  Undefined
```
If any argument to a builtin function is Undefined, the result is Undefined.
The function is never called.

**Rule bodies**:
When a statement in a rule body evaluates to Undefined, the rule body fails
(the rule doesn't produce a value for that input). This is Rego's core
evaluation model — rules are "queries" that succeed or fail.

### Default Rules and Undefined

Default rules only fire when:
1. No complete rule for the path produced a defined value, AND
2. The path is Undefined in the data

Precedence: `initial data > evaluated rules > default rules`

### Testing Undefined

Every code path that handles Values must consider:
1. What if this Value is Undefined?
2. What if an intermediate value in a chain is Undefined?
3. What does `not <this expression>` mean when the expression is Undefined?
4. Does collection construction with an Undefined element behave correctly?

## Value Ordering

Values implement `Ord` with a total order:
```
Null < Bool < Number < String < Array < Set < Object < Undefined
```

Within each variant, natural ordering applies (false < true, numeric order,
lexicographic for strings, element-wise for collections).

This ordering matters for `Set` and `Object` (which use `BTreeSet`/`BTreeMap`).

## Memory Limits

`Value` construction respects memory limits. The function
`enforce_limit_anyhow()` is called during deserialization and construction to
check the global memory limit (see `src/utils/limits/memory.rs`). This prevents
adversarial JSON payloads from exhausting memory.

## Serialization

- `Set` serializes as JSON array (no JSON equivalent for sets)
- `Object` keys that aren't strings are serialized as `{"__regorus_key": key, "__regorus_value": value}`
- `Undefined` should never appear in serialized output (it represents absence)
- `Number` serialization preserves precision (BigInt as string when needed)
