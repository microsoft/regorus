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

## Detecting genuine package-granularity cycles

OPA detects recursion **statically** over rule dependencies, where a
ref to a whole package depends on every rule in it. Regorus detects
recursion **dynamically**, while evaluating. Skipping in-flight rules
during module materialization on its own would mean that a policy that
is genuinely cyclic at package granularity could silently evaluate to
an order-dependent, internally inconsistent result. Example:

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
turn depends on `q.trigger` — a real cycle. OPA rejects this policy at
compile time (`rule data.p.a is recursive: data.p.a -> data.q.trigger
-> data.p.a`). With skipping alone, regorus would return
`{"p": {"a": true}, "q": {"trigger": 0}}` — self-contradictory, since
with `p.a` present `count(data.p)` is `1`, not `0`.

To close this hole, the interpreter performs a **partial-sweep
consistency check** (a one-round fixpoint verification):

1. Whenever a wholesale module sweep skips an in-flight rule, the rule
   that triggered the sweep (the innermost active rule, the "reader")
   is recorded in `partial_sweep_readers`. If the skipped in-flight
   rule *is* the reader itself — a rule reading the entire package that
   contains it — a recursion error is raised immediately.
2. Once evaluation settles (the active-rule stack becomes empty), each
   recorded reader is re-evaluated with prints suppressed. All rule
   values are final at this point, so the re-evaluation sees the fully
   materialized data.
3. A recursion error (`recursion detected when evaluating rule: rule
   reads a package that depends on this rule`) is reported if the
   re-evaluation:
   - produces a conflicting value (surfaces as a rule conflict), or
   - changes the value at the rule's path, or
   - produces **no** value even though the rule is the only one
     defining its path and a value exists there (the "vanishing value"
     case, e.g. `trigger if count(data.p) == 0`, which held while the
     package was partially materialized but no longer holds), or
   - triggers another partial sweep naming an already-verified reader.

With this check, both `trigger := count(data.p)` and
`trigger if count(data.p) == 0` are rejected with a recursion error,
matching OPA's verdict, while the valid issue #743 policies re-evaluate
to identical values and pass. The check only runs when a partial sweep
actually occurred, so well-behaved policies pay no cost.

### Deferred back-references through a sweep

A swept rule may itself directly reference the rule that initiated the
sweep. With only one rule in the registry package:

```rego
package registry
allow_stage1 if data.registry.packages[_].allow_stage1
```

`allow_stage1` is the outermost evaluation, its sweep evaluates
`package_a.allow_stage2`, and that rule's direct reference to
`data.registry.allow_stage1` hits a rule that is already on the
evaluation stack. This is not a genuine rule-level cycle either (OPA
accepts it), so when a direct reference reaches an in-flight rule *and*
the cycle passes through a sweep-initiated evaluation, the reference is
**deferred** instead of rejected: the referencing rule momentarily sees
`undefined`, is recorded as a *fixup* reader (tracked per entry in
`partial_sweep_readers`), and is re-evaluated once evaluation settles —
its value legitimately appears then. The sweeping rule is recorded for
the strict consistency check described above, so a genuine cycle hiding
behind this pattern still errors (typically as a rule conflict during
fixup). A cycle that does not pass through any sweep (e.g. `a = b`,
`b = c`, `c = a`) is still rejected immediately with the classic
recursion error.

### Interaction with `with` scopes and engine reuse

`with` modifiers save and restore evaluation state around a statement.
Readers recorded *inside* a `with` scope were computed under modified
input/data and are dropped when the scope's state is restored — except
when the reader is the still-active rule containing the `with`
statement itself, which is kept: re-verifying it re-applies its own
modifiers, so genuine cycles whose package read happens under a `with`
modifier are still detected. All partial-sweep bookkeeping is also
cleared in `clean_internal_evaluation_state`, so a reused `Engine`
cannot carry stale readers from one evaluation into the next.

### Regression tests

All scenarios live in `tests/interpreter/cases/rule/dependency.yaml`:

| case | kind |
|---|---|
| `cross-module-non-cyclic-rules` | valid (issue #743, import alias) |
| `cross-module-non-cyclic-rules-no-import` | valid (issue #743, direct refs) |
| `cross-module-non-cyclic-rules-swept-back-reference` | valid (deferred back-reference) |
| `cross-module-three-package-chain` | valid (three packages, acyclic rules) |
| `cross-module-non-cyclic-set-and-object-readers` | valid (partial set + dynamic-key object readers) |
| `cross-module-non-cyclic-read-under-with` | valid (package read under `with`) |
| `cross-module-package-cycle` | error (count over cyclic package) |
| `cross-module-package-cycle-vanishing` | error (vanishing value) |
| `cross-module-package-cycle-via-function` | error (cycle through a function) |
| `cross-module-package-cycle-partial-set` | error (cycle through a partial set) |
| `cross-module-package-cycle-inside-with` | error (cycle read inside `with`) |

### Remaining differences from OPA

- Detection happens at evaluation time, not compile time, and the error
  message and location differ from OPA's (regorus points at the reader
  rule; OPA lists the static cycle).
- The vanishing-value check is limited to rules that are the sole
  definition of their path. If several rules define the same path and
  the final merged value is unchanged, no error is raised — the result
  is still consistent, but OPA would have rejected the policy
  statically.
- A reader whose body calls a nondeterministic builtin could in theory
  produce a different value on re-evaluation and trigger a spurious
  recursion error; the interpreter's builtin cache makes this unlikely
  in practice.
- A reader that ran to completion entirely inside a `with` scope (i.e.
  a rule evaluated under modified input/data from another rule's body)
  is dropped when the scope's state is restored, so a cycle confined to
  such a scope goes undetected rather than erroring. Example:

  ```rego
  package p
  a if data.q.trigger with input as {}
  ```

  ```rego
  package q
  trigger if count(data.p) == 0
  ```

  OPA rejects this as recursive; regorus returns
  `{"p": {"a": true}, "q": {}}`. The reader `q.trigger` completes
  inside `p.a`'s `with` scope and its record is discarded on restore,
  because re-verifying it later against *unmodified* input would be a
  meaningless comparison and would produce spurious recursion errors
  for valid policies. (If the `with` statement is inside the reader's
  own body, the reader is still active at restore time, is kept, and
  the cycle is detected — see `cross-module-package-cycle-inside-with`.)
  A precise fix would require re-verifying the reader under the same
  scope at scope exit, but its ancestors are still mid-flight then and
  the partial-materialization problem recurses; closing this gap for
  good needs static rule-level cycle detection as in OPA.
