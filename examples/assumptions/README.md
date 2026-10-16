# Assumptions Example

This example is designed to make `--assume-unknown-input` easy to see in action.

The policy models a release approval flow:

- a release admin can approve a rollout,
- but only if at least two required controls are satisfied,
- and each control depends on input fields that are intentionally missing from the sample input.

With assumptions disabled, the policy denies the rollout because the required fields are undefined.

With assumptions enabled, Regorus records the missing fields as assumptions and the rollout can become allowed. That makes this a good debugging example for understanding exactly which unknown inputs the engine treated as if they existed and held true.

## Files

- `rollout_assumptions.rego`: policy with a complete rule and a partial-set helper rule.
- `sparse_input.json`: intentionally incomplete input.

## Suggested Commands

Show the final decision without assumptions:

```bash
cargo run --example regorus --features explanations -- eval \
  -d examples/assumptions/rollout_assumptions.rego \
  -i examples/assumptions/sparse_input.json \
  'data.examples.assumptions.allow' \
  --engine rvm --why
```

Show the final decision with assumptions enabled:

```bash
cargo run --example regorus --features explanations -- eval \
  -d examples/assumptions/rollout_assumptions.rego \
  -i examples/assumptions/sparse_input.json \
  'data.examples.assumptions.allow' \
  --engine rvm --why --assume-unknown-input
```

Inspect the helper rule to see one emitted control per assumption-driven branch:

```bash
cargo run --example regorus --features explanations -- eval \
  -d examples/assumptions/rollout_assumptions.rego \
  -i examples/assumptions/sparse_input.json \
  'data.examples.assumptions.required_controls' \
  --engine rvm --why --assume-unknown-input
```

## What Makes This Interesting

- It uses nested fields like `input.change.security.approved` and `input.release.window.status`.
- It has both a final decision rule and a partial-set helper rule.
- The `assumptions` section should tell you exactly which missing inputs were assumed.
- The helper rule output is easier to inspect when debugging because each emitted control corresponds to a concrete missing fact.