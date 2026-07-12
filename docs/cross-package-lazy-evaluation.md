# Cross-package lazy evaluation and recursion detection

This document describes the fix for
[microsoft/regorus#743](https://github.com/microsoft/regorus/issues/743)
("Behaviour differing from OPA on cyclic references between multiple
policies"), its root cause, and a known behavioral caveat of the fix.

## The bug

Policies whose *packages* reference each other cyclically — but whose
*rules* are acyclic — were rejected at evaluation time with
`recursion detected when evaluating rule`, while OPA evaluates them
successfully. Example (from the issue):

```rego
# registry.rego
package registry
import rego.v1

allow if allow_stage2

allow_stage1 if data.registry.packages[_].allow_stage1
allow_stage2 if data.registry.packages[_].allow_stage2
```

```rego
# package_a.rego
package registry.packages.package_a
import data.registry
import rego.v1

allow_stage2 if registry.allow_stage1
allow_stage1 := true
```

At rule granularity the dependencies are acyclic:

```
registry.allow          → registry.allow_stage2
registry.allow_stage2   → package_a.allow_stage2
package_a.allow_stage2  → registry.allow_stage1
registry.allow_stage1   → package_a.allow_stage1  (a constant)
```

OPA evaluates this and returns `allow: true`. Regorus reported a false
recursion error.

## Root cause

The interpreter evaluates rules lazily, but at a coarser granularity
than OPA in two situations. Both caused rules that were *not* actual
dependencies to be evaluated inside another rule's evaluation; if such
a swept-in rule was already on the evaluation stack, the runtime cycle
detector fired even though no rule-level cycle exists.

1. **Whole-module materialization.** A ref that cannot be resolved to a
   single rule path — e.g. `data.registry.packages[name].allow_stage1`,
   where `[name]` is a variable — causes `ensure_module_evaluated` to
   force **every** rule of every module under the prefix
   (`data.registry.packages`). Here that included
   `package_a.allow_stage2`, which was the rule currently being
   evaluated further up the stack, so the cycle detector reported
   recursion.

2. **Import aliases materialized the whole imported subtree.** With
   `import data.registry`, the expression `registry.allow_stage1`
   resolved the alias by evaluating the entire `data.registry` ref and
   only then selecting `.allow_stage1` from the result. Evaluating all
   of `data.registry` forced `registry.allow` and
   `registry.allow_stage2`, again dragging in-flight rules into the
   chain.

## The fix

Both changes are in `src/interpreter.rs`:

1. During wholesale module materialization
   (`ensure_module_evaluated`), rules that are currently being
   evaluated (present in `active_rules`) are **skipped** instead of
   re-entered. Their values are written into `data` when their own
   evaluation completes. When any rule was skipped, the module is not
   marked as fully processed, so later lookups will evaluate the
   remaining rules. A rule that is *directly* referenced by path while
   already active still triggers the genuine-recursion error.

2. Import resolution for `data.*` imports no longer evaluates the whole
   imported ref. Instead the accessed fields are appended to the import
   path and resolved through `lookup_data_path` (factored out of
   `lookup_var`), so only the rules needed for the accessed path — e.g.
   `data.registry.allow_stage1` — are evaluated.

Regression tests: `tests/interpreter/cases/rule/dependency.yaml`, cases
`cross-module-non-cyclic-rules` and
`cross-module-non-cyclic-rules-no-import`.

## Caveat: package-granularity cycles are no longer always rejected

OPA detects recursion **statically** over rule dependencies, where a
ref to a whole package depends on every rule in it. Regorus detects
recursion **dynamically**, while evaluating. Skipping in-flight rules
during module materialization means a policy that is genuinely cyclic
at package granularity may now evaluate to an order-dependent (and
internally inconsistent) result instead of producing an error.

Concrete example:

```rego
# p.rego
package p
import rego.v1

a if data.q.trigger >= 0
```

```rego
# q.rego
package q
import rego.v1

trigger := count(data.p)
```

`q.trigger` depends on *all* of `data.p`, including `p.a`, which in
turn depends on `q.trigger` — a real cycle. Behavior:

- **OPA** rejects the policy at compile time:
  `rule data.p.a is recursive: data.p.a -> data.q.trigger -> data.p.a`.
- **Regorus before the fix** failed at evaluation time with
  `recursion detected when evaluating rule`.
- **Regorus after the fix** evaluates successfully and returns
  `{"p": {"a": true}, "q": {"trigger": 0}}`.

The post-fix result is self-contradictory: `trigger` was computed as
`count(data.p)` while `p.a` was still in flight and skipped, so it saw
an empty package and produced `0`; afterwards `p.a` completed and was
written into `data.p`, where `count(data.p)` would now be `1`.

This trade-off was accepted because rejecting valid, OPA-accepted
policies (the issue #743 pattern is common for plugin/registry style
policy layouts) is worse than producing a value for policies OPA would
reject as recursive. Matching OPA exactly would require rule-level
virtual-document evaluation (per-rule lazy resolution of refs with
variable path segments) or static rule-level cycle detection, both of
which are larger changes to the interpreter's evaluation model.
