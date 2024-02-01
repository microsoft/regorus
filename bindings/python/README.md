# regorus

**Regorus** is

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
   interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

Regorus can be used in Python via `regorus` package. (It is not yet available in PyPI, but can be manually built.)

See [Repository](https://github.com/microsoft/regorus).

To build this binding, see [building](https://github.com/microsoft/regorus/bindings/python/building.md)

## Usage
```Python
import regorus

# Create engine
engine = regorus.Engine()

# Load policies
engine.add_policy_from_file('../../tests/aci/framework.rego')
engine.add_policy_from_file('../../tests/aci/api.rego')
engine.add_policy_from_file('../../tests/aci/policy.rego')

# Add policy data
data = {
  "metadata": {
    "devices": {
      "/run/layers/p0-layer0": "1b80f120dbd88e4355d6241b519c3e25290215c469516b49dece9cf07175a766",
      "/run/layers/p0-layer1": "e769d7487cc314d3ee748a4440805317c19262c7acd2fdbdb0d47d2e4613a15c",
      "/run/layers/p0-layer2": "eb36921e1f82af46dfe248ef8f1b3afb6a5230a64181d960d10237a08cd73c79",
      "/run/layers/p0-layer3": "41d64cdeb347bf236b4c13b7403b633ff11f1cf94dbc7cf881a44d6da88c5156",
      "/run/layers/p0-layer4": "4dedae42847c704da891a28c25d32201a1ae440bce2aecccfa8e6f03b97a6a6c",
      "/run/layers/p0-layer5": "fe84c9d5bfddd07a2624d00333cf13c1a9c941f3a261f13ead44fc6a93bc0e7a"
    }
  }
}
engine.add_data(data)

# Set input
input = {
  "containerID": "container0",
  "layerPaths": [
    "/run/layers/p0-layer0",
    "/run/layers/p0-layer1",
    "/run/layers/p0-layer2",
    "/run/layers/p0-layer3",
    "/run/layers/p0-layer4",
    "/run/layers/p0-layer5"
  ],
  "target": "/run/gcs/c/container0/rootfs"
}
engine.set_input(input)

# Eval query
results = engine.eval_query('data.framework.mount_overlay=x')

# Print results
print(results['result'][0])

# Eval query as json
results_json = engine.eval_query_as_json('data.framework.mount_overlay=x')
print(results_json)
```

