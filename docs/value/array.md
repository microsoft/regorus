# Array

Opaque container for `Value::Array`'s ordered element storage, enabling
alternative backends without call-site changes. It follows the same
abstraction pattern as [`Object`](object.md) and [`Set`](set.md).

## Design

`Array` wraps a `Vec<Value>` today but exposes only a curated method surface
(`get`, `get_mut`, `first`, `last`, `contains`, `iter`, `iter_mut`, `push`,
`append`, `extend`, `extend_from_slice`, `retain`, `clear`, `reverse`, `sort`,
`cursor`, and serde). The inner vector is private, and `Array` does not
implement `Deref`, so callers cannot depend on the backing representation.

Indexing uses `Index<usize>` and returns `Value::Undefined` for an out-of-range
index, matching `Value` indexing semantics. Use `get` when distinguishing a
missing element from an element whose value is explicitly `Undefined`.

Iteration follows sequence order. The opaque cursor supports incremental
traversal needed by RVM iteration state without exposing iterator internals.
`Ord` is implemented against the sequence iterator so alternative backends can
preserve the current array comparison behavior.

## Scenarios enabled

- **Inline-small storage** — store short arrays inline and spill to the heap
  only for larger values.
- **Lazy/streaming storage** — materialize elements from JSON, CBOR, or a host
  provider on demand.
- **Arena allocation** — use bump allocation for evaluation-time temporaries
  and release them together at query end.
- **FFI-backed storage** — access host-language lists or arrays without
  copying at every binding boundary.
