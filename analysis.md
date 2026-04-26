# Arena-Allocated Value for Evaluation — Deep Analysis

## Current `Value` Layout (24 bytes on 64-bit)

```rust
enum Value {
    Null,                                       // 0 bytes payload
    Bool(bool),                                 // 1 byte
    Number(Number),                             // 16 bytes (enum: u64 | i64 | f64 | Rc<BigInt>)
    String(Rc<str>),                            // 16 bytes (fat pointer)
    Array(Rc<Vec<Value>>),                      // 8 bytes (thin pointer)
    Set(Rc<BTreeSet<Value>>),                   // 8 bytes
    Object(Rc<BTreeMap<Value, Value>>),         // 8 bytes
    Undefined,                                  // 0 bytes
}
```

`Rc` is conditionally `Arc` (via `arc` feature) for multi-threaded use. Cloning a `Value`
with heap variants is cheap — just an atomic refcount bump. But two distinct costs are being
paid during evaluation.

---

## Cost #1: Rc/Arc Refcount Operations (~316 clone sites)

The interpreter has ~161 `.clone()` calls on `Value`, the RVM has ~155. Most are
`get_register(r)?.clone()` or `variable.clone()` from scope lookup. Each `Arc::clone` is an
atomic increment (`lock xadd` on x86), and each drop is an atomic decrement.

**Estimated impact**: Moderate. For a policy evaluating ~10K expressions, expect ~10K–50K
atomic ops. At ~5–20ns each (cache-dependent), that's 50–1000µs of pure refcount overhead
per evaluation.

### Hot clone sites in the interpreter

| Pattern | Location | Frequency |
|---------|----------|-----------|
| Scope save/restore in `eval_some_in` | `interpreter.rs:944–1070` | 2–3× per loop iteration |
| Variable lookup | `interpreter.rs:538` | Every variable reference |
| Collection indexing | `interpreter.rs:596,605` | Every `obj[idx]` expression |
| `get_value_chained` path lookup | `interpreter.rs:3376–3390` | Every dotted reference |
| Literal evaluation | `interpreter.rs:3157–3163` | Every literal in expressions |
| `with` modifier state save | `interpreter.rs:1232–1240` | Each `with` block |

### Hot clone sites in the RVM

| Pattern | Location | Frequency |
|---------|----------|-----------|
| `get_register` → `.clone()` | `dispatch.rs` (31 sites) | Nearly every opcode |
| Comprehension accumulation | `comprehension.rs:258–276` | Each comprehension iteration |
| Loop variable binding | `loops.rs:550–599` | Each loop iteration |
| Rule result caching | `rules.rs:91–180` | Each rule evaluation |
| Data/Input loading | `dispatch.rs:68–72` | Start of eval |

---

## Cost #2: Heap Allocation for Collection Intermediates

Every new `String`, `Array`, `Set`, or `Object` created during eval allocates:
- `Rc`/`Arc` control block (16 bytes: strong + weak count) + payload
- `BTreeMap`/`BTreeSet` nodes (40+ bytes each internal node)
- `Vec` backing buffer (for arrays)
- `Rc<str>` allocation per string

### The RVM comprehension O(n²) bug

`comprehension.rs:265–276` clones the **entire collection** each iteration:

```rust
// Current code — O(n²) for n iterations:
let current_result = self.get_register(result_reg)?.clone();
let mut new_set = set.as_ref().clone();   // deep clone of BTreeSet
new_set.insert(value_to_add);
Value::Set(crate::Rc::new(new_set))       // new Rc allocation
```

The interpreter does this correctly using `Rc::make_mut` (O(n) amortized).

---

## Can Bumpalo Help? — Feasibility Analysis

**What bumpalo gives**: A bump allocator where all allocations are O(1) (pointer bump) and
deallocation is free (entire arena freed at once). No individual `Drop`. Perfect when all
values share a common lifetime.

### Hypothetical arena-allocated `EvalValue`

```rust
enum EvalValue<'a> {
    Null,
    Bool(bool),
    Number(EvalNumber<'a>),        // BigInt variant needs &'a
    String(&'a str),               // borrowed, not Rc<str>
    Array(&'a [EvalValue<'a>]),    // slice into arena
    Set(???),                      // BTreeSet can't use bumpalo
    Object(???),                   // BTreeMap can't use bumpalo
    Undefined,
}
```

### Key Obstacles

| Issue | Severity | Details |
|-------|----------|---------|
| **BTreeMap/BTreeSet in arena** | **Blocker** | Standard `BTreeMap` allocates internal nodes via global allocator. You'd need a custom B-tree allocating from bumpalo, or replace with sorted `Vec<(K,V)>` in the arena. Massive undertaking. |
| **Mutability** | **Blocker** | Rego evaluation **mutates** collections: comprehensions push to arrays, insert into sets/objects. Bumpalo gives `&'a T` — immutable. `bumpalo::collections::Vec` exists but not BTreeMap. You'd need `bumpalo::collections::Vec` for arrays and a sorted-vec replacement for sets/objects. |
| **Lifetime infection** | **Major** | `EvalValue<'a>` infects everything: interpreter, RVM, all builtins, all extension functions. The `Extension` trait `fn(Vec<Value>) -> Result<Value>` becomes `fn(Vec<EvalValue<'a>>) -> Result<EvalValue<'a>>` — lifetime parameter everywhere. |
| **Result escapes arena** | **Major** | The eval result must outlive the arena. Requires a conversion `EvalValue<'a> → Value` at the boundary, deep-copying the result. Partially negates gains. |
| **`data`/`input` cross boundary** | **Major** | `data` and `input` are `Value` (Rc-based). They'd need conversion to `EvalValue<'a>` at eval start. `Rc<str>` → `&'a str` requires strings to live in the arena or be borrowed from the original `Value`. |
| **`Ord` for sets/objects** | **Moderate** | `EvalValue` needs `Ord` to be used as keys. The `&'a` lifetime complicates container implementations. |

---

## What Would Actually Help — Targeted Optimizations

### 1. Fix RVM comprehension O(n²) — HIGH impact, LOW effort

Use `std::mem::take` + `Rc::make_mut` instead of clone-everything:

```rust
// After — O(n) amortized:
let mut current_result = std::mem::replace(
    &mut self.registers[result_reg], Value::Undefined
);
current_result.as_set_mut()?.insert(value_to_add);  // Rc::make_mut inside
self.set_register(result_reg, current_result)?;
```

When refcount is 1 (which it will be after `take`), `Rc::make_mut` is a no-op. This turns
O(n²) into O(n) for comprehension accumulation. Expected **2–10× speedup** for
comprehension-heavy policies.

### 2. `mem::take` for dead registers in RVM — MODERATE impact, LOW effort

When a source register is dead after use (e.g., `Move`, `Return`, `Halt`, single-use temps),
swap with `Undefined` instead of cloning. Avoids Rc increment+decrement pairs entirely.

The RVM compiler could annotate "last use" of a register. Even without compiler support, 
specific opcodes like `Return` and `Halt` can always take rather than clone.

### 3. String interning — MODERATE impact, MODERATE effort

Path components like `"data"`, `"input"`, and field names from policies are created as
`Value::String(Rc::new(...))` repeatedly. An interning table (lookup existing `Rc<str>`
keyed by `&str`) would share the same allocation. The `SourceStr` type already carries `Rc`
references to source text, so policy-defined strings could reference those directly.

### 4. Use `Rc` (not `Arc`) for single-threaded eval — LOW-MODERATE impact, trivial

If eval is always single-threaded (which it is — the multi-threaded benchmark clones the
`Engine`), the `arc` feature should be off during eval. `Rc::clone` is a simple non-atomic
increment (~1ns vs ~5–20ns for `Arc`).

This is already supported via the feature flag. Ensure hot-path usage benefits.

### 5. Interpreter scope save/restore — MODERATE impact, MODERATE effort

`eval_some_in` clones the entire `Scope` (`BTreeMap<SourceStr, Value>`) 2–3× per iteration.
Options:

- **Scope-stack approach**: Push variable bindings, pop on unwind (like the RVM's register
  windows). Avoids BTreeMap cloning entirely.
- **Persistent map**: Use `im::HashMap` — O(log n) structural sharing clone.
- **Trail-based undo**: Record mutations, replay in reverse to restore. O(k) where k is the
  number of bindings changed.

### 6. Sorted Vec for small Object/Set — MODERATE impact, MODERATE effort

`BTreeMap`/`BTreeSet` have high constant factors (node allocations, pointer chasing). For
objects with <16 entries (common in policy evaluation), a sorted `Vec<(Value, Value)>` is:
- More cache-friendly (contiguous memory)
- Cheaper to allocate (single allocation vs many nodes)
- Comparable lookup cost at small sizes (binary search on 16 elements ≈ 4 comparisons)

Could use a hybrid: sorted Vec below threshold, BTreeMap above.

---

## Estimated Impact Summary

| Approach | Speedup Estimate | Effort | Recommendation |
|----------|-----------------|--------|----------------|
| Fix RVM comprehension O(n²) | 2–10× for comprehension-heavy policies | Small (< 50 LOC) | **Do this now** |
| `mem::take` for dead registers | 5–15% overall eval | Medium | **Worth doing** |
| String interning | 5–10% for string-heavy policies | Medium | **Worth exploring** |
| `Rc` not `Arc` for eval | 5–10% if using `arc` feature | Trivial (feature flag) | **Already available** |
| Interpreter scope optimization | 10–20% for loop-heavy policies | Medium | **Worth doing** |
| Sorted Vec for small Object/Set | 10–20% for object-heavy policies | Medium | **Worth exploring** |
| Full bumpalo `EvalValue<'a>` | 15–30% theoretical | **Massive** (full rewrite) | **Not recommended** |

---

## Bottom Line

**Bumpalo / full arena value is not feasible** without effectively replacing `BTreeMap` and
`BTreeSet` with arena-friendly alternatives and infecting the entire codebase with a lifetime
parameter. The effort (~5K+ LOC rewrite across interpreter, RVM, and builtins) is
disproportionate to the expected gain (~15–30%), because the real bottleneck is BTreeMap
operations (O(log n), cache-unfriendly), not allocation/refcounting.

**The highest-ROI optimizations** are:
1. Fix the RVM comprehension O(n²) bug (immediate, large gain)
2. Use `mem::take` semantics in the RVM to avoid unnecessary Rc clones
3. Improve scope management in the interpreter to avoid BTreeMap cloning in loops

These targeted changes can deliver comparable or better speedups to a full arena rewrite,
with a fraction of the effort and no API surface changes.

---

## What if hashbrown + bumpalo for Object and Set?

The biggest blocker to arena-allocated values is that `BTreeMap`/`BTreeSet` allocate internal
nodes from the global allocator. But `hashbrown` supports custom allocators on stable:

```rust
hashbrown::HashMap<K, V, DefaultHashBuilder, &'bump Bump>
hashbrown::HashSet<T, DefaultHashBuilder, &'bump Bump>
```

All internal hash table nodes allocate from the bump arena. This makes the full `EvalValue`
sketch viable:

```rust
enum EvalValue<'a> {
    Null,
    Bool(bool),
    Number(EvalNumber),                   // u64/i64/f64 inline, BigInt: &'a BigInt
    String(&'a str),                      // arena-allocated or borrowed
    Array(&'a [EvalValue<'a>]),           // frozen slice in arena
    Set(&'a HashSet<EvalValue<'a>, ..., &'a Bump>),
    Object(&'a HashMap<EvalValue<'a>, EvalValue<'a>, ..., &'a Bump>),
    Undefined,
}
```

**Size**: 24 bytes (same as current `Value`).

### New Problems That Surface

#### 1. `EvalValue` must implement `Hash`

To be a key in `HashSet<EvalValue>` / `HashMap<EvalValue, _>`, `EvalValue` needs `Hash + Eq`.
But `HashSet`/`HashMap` don't implement `Hash` — chicken-and-egg.

**Fix**: Implement `Hash` manually with order-independent hashing for Set/Object:

```rust
impl Hash for EvalValue<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        discriminant(self).hash(state);
        match self {
            Set(s) => {
                s.len().hash(state);
                // XOR element hashes (commutative → order-independent)
                let mut combined = 0u64;
                for v in s.iter() {
                    let mut h = DefaultHasher::new();
                    v.hash(&mut h);
                    combined ^= h.finish();
                }
                combined.hash(state);
            }
            Object(m) => { /* similar: XOR of hash(k, v) pairs */ }
            // scalars, string, array: straightforward
            ...
        }
    }
}
```

Hashing deeply-nested values is O(total size). In practice, sets/objects as hash keys are
rare in Rego policies.

#### 2. `Eq` works, `Ord` is lost

`HashSet`/`HashMap` implement `PartialEq`/`Eq`, so `EvalValue: Eq` works. But `Ord` is lost
since hash collections have no canonical order.

Rego defines a **total ordering** on values (used by `sort()`, comparison operators). `Ord`
must be implemented manually, sorting set/object elements on demand. Costs O(n log n) per
comparison of set/object values.

#### 3. Deterministic output ordering

OPA/Rego produces deterministic JSON output (objects sorted by key). With HashMap, iteration
order is not deterministic.

**Fix**: Sort at the boundary when converting `EvalValue → Value` for the final result. Or
use `indexmap` (insertion-ordered) instead of `hashbrown::HashMap`. `indexmap` also supports
custom allocators via hashbrown internally.

#### 4. Mutation during evaluation

Rego evaluation **mutates** collections: comprehensions push to arrays, insert to sets/objects.
The arena pattern gives `&'a T` (immutable references).

| Approach | Trade-off |
|----------|-----------|
| **`&'a RefCell<HashMap<...>>`** | Runtime borrow checking. 8 bytes overhead per collection. |
| **Build in mutable local, freeze into arena** | Comprehensions build locally, then `bump.alloc(set)` → `&'a HashSet`. Works for build-once-read-many. |
| **Copy-on-write via arena** | To "mutate", allocate a new collection in arena with change applied. Old one leaked (arena freed at end). Wasteful but simple. |

The **build-then-freeze** pattern fits Rego well: most collections are built in
comprehensions/rules and then read. The few mutations (like `with` modifier overriding data)
can re-allocate.

#### 5. Sharing becomes free

Current `Value` with Rc gives free sharing: multiple registers/variables point to the same
object. With arena values:

- **Scalars + String** (`&'a str`): `EvalValue` is `Copy`-like — just copy the pointer. **Zero cost.**
- **Array** (`&'a [EvalValue]`): Copy the fat pointer. **Zero cost.** All references share the same arena slice.
- **Set/Object** (`&'a HashSet/HashMap`): Copy the thin pointer. **Zero cost.**

This is **better than Rc** — no atomic refcount at all. Just pointer copies. The arena owns
everything.

#### 6. Lifetime infection — still present

`EvalValue<'a>` still infects everything. The extension API would need the bump allocator
threaded through.

**Mitigation**: Keep the public API using `Value`. Use `EvalValue` internally in the
interpreter/RVM only. Convert at boundaries:
- `Value → EvalValue`: at eval start (for data/input). O(n) deep conversion.
- `EvalValue → Value`: at eval end (for result). O(result size) — typically small.

Builtins are internal so they can use `EvalValue<'a>`. Extensions (user-provided) would need
`EvalValue → Value` conversion before the call and `Value → EvalValue` after. Extensions are
rare in hot paths, so the overhead is acceptable.

### Revised Feasibility with hashbrown

| Issue | Before (BTreeMap only) | After (hashbrown) |
|-------|------------------------|-------------------|
| Collections in arena | **Blocker** | **Solved** |
| Mutability | **Blocker** | **Manageable** (build-then-freeze) |
| `Hash` for EvalValue | N/A | **Solvable** (manual impl) |
| Lifetime infection | Major | **Major** (mitigated by boundary conversion) |
| Result escapes arena | Major | **Same** (conversion at boundary) |
| Deterministic ordering | Free (BTreeMap) | **Requires sort at output** |
| Lookup performance | O(log n) | **O(1) amortized** — faster |

### The Real Gain

With hashbrown + bumpalo `EvalValue`:

1. **Zero refcount cost**: `EvalValue` copies are just memcpy of 24 bytes. No atomic ops.
   The ~316 clone sites become trivial copies. Saves ~50–1000µs per evaluation.

2. **O(1) hash lookups**: Object key lookup goes from O(log n) BTreeMap to O(1) HashMap.
   For objects with 100+ keys (e.g., ACI policies), significant win.

3. **Bulk deallocation**: At end of eval, `bump.reset()` frees everything. No cascading
   `Drop` calls walking tree nodes.

4. **Cache-friendly**: hashbrown uses flat, open-addressing — more cache-friendly than
   B-tree nodes scattered across the heap.

5. **Comprehension cost**: Building a set/object in a comprehension becomes
   `HashSet::insert` in arena — O(1) amortized with no Rc overhead. The O(n²) bug
   disappears structurally.

### Estimated Impact with hashbrown

| Component | Estimated gain |
|-----------|---------------|
| Eliminating Rc/Arc refcounting | 5–15% |
| O(1) vs O(log n) lookups | 10–25% for object-heavy policies |
| Bulk deallocation | 5–10% |
| Cache friendliness | 5–10% |
| **Combined** | **20–40% realistic** |

### Effort Estimate

~3K–5K LOC:

1. Define `EvalValue<'a>` with `Hash`/`Eq`/`Ord` impls (~300 LOC)
2. Refactor interpreter to use `EvalValue` + arena (~1500 LOC)
3. Refactor RVM to use `EvalValue` + arena (~1500 LOC)
4. Adapt builtins (~500 LOC)
5. Boundary conversions `Value ↔ EvalValue` (~200 LOC)

### Recommendation

The targeted fixes (comprehension O(n²), `mem::take`, scope optimization) deliver **15–30%**
for **~200 LOC**. The hashbrown+bumpalo approach gets further (**20–40%**) but at 15–25× the
effort.

**Do the targeted fixes first, benchmark, then decide if the remaining gap justifies the
arena rewrite.** The hashbrown approach makes it *possible* — the question is whether the
marginal gain over targeted fixes is worth the complexity.
