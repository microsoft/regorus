# Causality Demo

This folder contains a static browser demo for the causality feature.

The demo now includes:

- a scenario tour that shows the policy and request first, then runs analysis on demand
- a playground page for custom policy, data, input, engine, and entry point selection
- a shared wasm runtime that executes Regorus in the browser
- scripts to build the wasm assets and launch the static site locally

## Build demo assets

From the repository root:

```sh
./causality-demo/build-demo.sh
```

This builds the browser-targeted wasm package into `causality-demo/pkg`.

## Run locally

From the repository root:

```sh
./causality-demo/run-local.sh
```

The script builds the wasm assets, starts a static file server rooted at `causality-demo`, and opens the browser on macOS.

You can override the port with:

```sh
REGORUS_DEMO_PORT=8123 ./causality-demo/run-local.sh
```

## GitHub Pages

The final site is static. After running `./causality-demo/build-demo.sh`, publish the contents of `causality-demo/`.

## What it shows

- complete-rule why chains
- helper-rule inlining
- loop and `every` witnesses
- comprehension summaries
- multiple contributing conditions
- redacted versus full-value bindings
- Kubernetes admission control with stacked container violations
- RBAC role resolution with passing/failing iteration witnesses
- data pipeline schema validation with type-check builtins
- Terraform/cloud resource compliance with `glob.match`
- SBOM supply chain license audit across transitive dependencies
- feature flag targeting with segment rules and percentage rollouts
- custom playground evaluations