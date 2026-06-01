# Object

Opaque container for `Value::Object`'s key→value storage, enabling
alternative backends without call-site changes.

## Design

`Object` wraps the storage for a key→value collection of `Value`s and
provides a curated set of methods (`get`, `insert`, `remove`, `iter`,
`iter_sorted`, `cursor`, serde). The backing store is private; callers
never see or pattern-match on it, so the representation can change
without rippling through call sites.

Multiple backends can coexist at runtime. Because the backing store is
private, different `Object` instances in the same process can use
different implementations — e.g., a lazy DB-backed object for `input`,
inline small-map objects for SARIF location records, and a regular
sorted map elsewhere — all interoperating through the same opaque
type. This is stronger than the typical Cargo-feature-selected backend
seen in precedent crates.

Iteration is split intentionally. `iter()` makes no ordering promise,
which lets backends that don't keep entries sorted skip any sort work.
`iter_sorted()` returns entries in `Value` order and is what
serialization and `Ord` rely on for deterministic output. Cursor types
add resumable, incremental traversal for the RVM iteration state
without leaking iterator internals.

`Ord` and `PartialOrd` are defined against `iter_sorted()` rather than
derived from the storage. Two `Object`s built on different backends —
or with different insertion histories — compare equal whenever their
sorted entries match, so changing the backend never changes observable
comparison results.

## Precedents

Other crates that hide storage behind a stable API so the implementation
can change without breaking callers:

- **`serde_json::Map`** — opaque newtype allowing cargo-feature based
  swap between `BTreeMap` (canonical order) and `IndexMap` (insertion
  order).
- **`toml::Table`** — opaque newtype allowing cargo-feature based swap
  between `BTreeMap` and `IndexMap`.
- **`simdjson` DOM** — opaque tree that lazily materializes nodes on
  access instead of parsing the whole document up front.

## Use cases

- **SARIF small-object pressure** — SARIF reports contain millions of
  small objects (location records, rule references, message arguments),
  most with 2-5 keys. A small-map-optimized backend (inline storage
  for ≤N entries, heap above) eliminates per-object BTreeMap allocation
  for the common case.

- **Kubernetes admission policies** — large, deeply-nested resource
  objects (Pod specs, CRDs) where policies typically touch a handful
  of paths. A lazy-materializing backend (`LazyObjectProvider` over
  the incoming JSON) parses only the accessed subtrees.

- **Azure Policy aliases** — ARM exposes the same logical property
  under multiple aliases (e.g. paths like
  `Microsoft.Compute/virtualMachines/storageProfile.osDisk.managedDisk.id`).
  An alias-aware backend resolves lookups across canonical and alias
  forms without rewriting every policy.

- **Azure Policy case-insensitive compare** — ARM property names are
  case-preserving but case-insensitive on lookup (`tags.Environment`
  and `tags.environment` resolve identically). A case-insensitive
  backend centralizes this once at the storage layer instead of at
  every comparison site.

- **External data sources** — `input` or `data` backed by a database
  query, CBOR slice, REST endpoint, or other streaming source via a
  `LazyObjectProvider`. Entries materialize on demand; the policy
  only pays for what it touches.

- **Eval-time temporaries** — objects constructed during evaluation
  (comprehensions, intermediate rule results) on a bumpalo arena.
  The whole arena drops at query end with zero per-entry free cost.

- **Host-language interop** — Python dicts or JS objects accessed via
  FFI callbacks from the embedding application, without copying into
  Rust on every binding boundary.
