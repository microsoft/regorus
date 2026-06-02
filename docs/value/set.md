# Set

Opaque container for `Value::Set`'s element storage, enabling alternative
backends without call-site changes. Pairs with [`Object`](object.md) under
a shared design philosophy.

## Design

`Set` wraps a `BTreeSet<Value>` today but exposes only a curated method
surface (`contains`, `insert`, `remove`, `iter`, `iter_sorted`, `cursor`,
`is_subset`, `intersection`, `union`, `difference`, serde). The inner set is
private — callers cannot pattern-match it or hand out references to the
backing store, so the backend can change without churn at the ~400 call
sites that name `Set`.

Two iteration methods reflect a real distinction: `iter()` makes no
ordering promise (lets future hash/lazy backends skip sorting work);
`iter_sorted()` guarantees deterministic order (used by serialization and
`Ord`). Cursor types support incremental traversal needed by the RVM
iteration state without exposing iterator internals.

`Ord` is hand-written against `iter_sorted` rather than derived, so two
backends that store elements differently still compare equal when their
sorted contents match.

## Scenarios enabled

- **Hash-backed storage** — `FxHashSet`-backed inner turns O(log n)
  membership checks into O(1); swap in for policies where elements aren't
  compared ordinally.
- **Lazy/streaming** — wrap a `LazySetProvider` (DB query, CBOR slice,
  REST endpoint) and materialize elements on demand.
- **Arena allocation** — bumpalo-backed inner for eval-time temporaries;
  drop the whole arena at query end with zero per-element free cost.
- **FFI-backed** — host-language collections (Python set, JS Set) without
  copying into Rust.
- **Bloom-filter pre-check** — front a large backing set with a Bloom
  filter for fast negative-membership tests on read-mostly allowlists.

## Known use cases

- **Azure Policy allowed-values lists** — large allowlists (allowed
  regions, allowed SKUs, allowed image publishers) compared against
  single resource values. Hash-backed Set turns O(log n) membership
  checks into O(1).
- **SARIF rule deduplication** — collapsing duplicate rule references
  across thousands of result records. Set-of-objects with structural
  hashing avoids the BTreeSet sort cost on every insert.
- **RBAC role membership** — checking whether a principal belongs to any
  of dozens of role groups. Hash-backed Set scales to thousands of
  members with constant-time membership.
- **Azure Policy denied-resource-type sets** — exclusion lists used by
  deny-effect policies; same hash-backed pattern as allowed-values.

## Precedents

- **`indexmap::IndexSet`** — opaque newtype that pairs hash lookup with
  insertion-order iteration; precedent for "Set with alternative
  ordering semantics behind a stable surface."
- **`hashbrown::HashSet`** — backs Rust's `std::collections::HashSet`
  and demonstrates a fully swappable backend behind a stable API.
- **`roaring::RoaringBitmap`** — bitmap-backed integer set. Not
  applicable to `Value` keys directly, but a precedent for the broader
  idea of "Set with alternative storage representations chosen by
  workload shape."
- **`serde_json`** — note that `serde_json` has no Set equivalent: its
  Value enum collapses sets into arrays. Regorus's first-class Set with
  storage abstraction is therefore unusually well-positioned among JSON
  value libraries.

## Notes

Cursor types are `pub` (referenced by public `IterationState`) but not
re-exported at the crate root. The crate-internal `Set`/`Map`/`MapEntry`
aliases for `BTreeSet`/`BTreeMap` in `lib.rs` were renamed to
`MapSet`/`Map`/`MapEntry` when this type landed, to free the `Set` name
for the new public type. Future Array and String abstractions follow the
same shape — see `docs/value/array.md` and `docs/value/string.md` when
they land.
