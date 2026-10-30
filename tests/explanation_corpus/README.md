# Explanation and partial-evaluation corpus

A shared set of Rego policies and inputs for explanation (causality) and
partial-evaluation tests. The expected values come from Rego semantics and are
checked against OPA, so a test that adds explanation or residual expectations
can trust the value it explains.

The harness is `mod.rs`. It runs with the `rvm` feature:

```bash
cargo test --test mod explanation_corpus
# Also check every expected value against OPA:
REGORUS_OPA=/path/to/opa cargo test --test mod explanation_corpus::corpus_matches_opa
```

## Tests

- `corpus_values`: runs every example on the interpreter and on the RVM in both
  run-to-completion and suspendable modes. The outcome must equal `want_*`, or
  `divergence.actual_*` for the engines the divergence lists.
- `corpus_is_well_formed`: checks the structural rules below and prints how
  many cases cover each construct.
- `corpus_matches_opa`: when `REGORUS_OPA` is set, runs `opa eval` for every
  example (except cases with `opa_skip`) and compares with `want_*`. Error
  messages differ between OPA and regorus, so any OPA evaluation error
  (`eval_*` code) satisfies `want_error`. A parse, compile or usage error from
  OPA fails the test. Without `REGORUS_OPA` this test does nothing.

## Format

Each `cases/*.yaml` file has a `cases` list. A case is one policy and query;
its examples are inputs to it.

```yaml
cases:
  - note: unique_snake_case_name
    description: What the case shows.
    constructs: [complete_rule, default]   # see `Construct` in mod.rs
    modules:
      - |
        package test
        default allow := false
        allow if input.role == "admin"
    query: data.test.allow
    data: {}                      # optional
    rego_v0: false                # optional; parse modules as Rego v0
    strict_builtin_errors: false  # optional; true makes builtin errors errors instead of Undefined
    unknowns: [input.role]        # required iff tagged unknown_input
    secrets: ["s3cr3t"]           # required iff tagged secret
    opa_skip: reason              # optional; OPA can't run this case
    examples:
      - note: admin
        input: {role: admin}      # absent means no input document
        want_result: true         # "#undefined" for Undefined, {"set!": [...]} for a set
      - note: guest
        input: {role: guest}
        want_result: false
```

An example sets exactly one of `want_result` or `want_error` (a substring of the
regorus error message). Error messages quote the failing source line, so the
substring must not occur in the policy itself.

### Rules checked by `corpus_is_well_formed`

- Notes, the query and every module are non-empty. Case notes are unique, and example notes
  are unique within a case.
- Each case has at least two distinct expected outcomes, so every matching
  example has a nonmatching twin.
- Every construct is covered by at least one case.
- `unknowns` is set exactly when the case is tagged `unknown_input`, and every
  path is under `input`.
- `secrets` is set exactly when the case is tagged `secret`, and every secret
  appears in the case's input or data.
- A divergence's actual outcome differs from the expected one.
- No expected or actual error text occurs in the policy source.
- `partial_eval` and `explanation` are rejected until a checker exists.

### Divergences

When regorus disagrees with OPA, `want_*` stays the correct value and the
example records what regorus does today:

```yaml
        divergence:
          reason: Why regorus differs, with an upstream issue link if one exists.
          engines: [rvm]          # interpreter, rvm, or both
          actual_result: "#undefined"   # or actual_error: "substring"
```

Fixing the bug makes the test fail on the listed engines; remove the
divergence then.

## Adding explanation or partial-evaluation expectations

`explanation` (per example) and `partial_eval` (per case) are reserved. A PR
that adds an explanation or partial-evaluation feature:

1. Replaces the reserved field's type in `mod.rs` with the feature's expected
   type, behind the feature's cargo flag.
2. Adds a check that compares it with the producer's output.
3. Fills the field in for the cases it supports.

Cases and inputs stay as they are; new constructs get new cases with a twin.
Test functions for `cases/*.yaml` are generated at compile time, so after adding
a new file, rebuild the tests (for example, `touch tests/explanation_corpus/mod.rs`).

`unknowns` gives the input paths partial evaluation treats as unknown, and each
example's input is one concrete assignment of them. `secrets` lists values that
must not appear unredacted in a report.
