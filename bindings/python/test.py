# Copyright (c) Microsoft Corporation.
# Licensed under the MIT License.

import regorus

# Create engine
engine = regorus.Engine()

engine.set_rego_v0(True)

# Load policies
pkg = engine.add_policy_from_file('../../tests/aci/framework.rego')
print(' Loaded package %s' % pkg)

pkg = engine.add_policy_from_file('../../tests/aci/api.rego')
print(' Loaded package %s' % pkg)

pkg = engine.add_policy_from_file('../../tests/aci/policy.rego')
print(' Loaded package %s' % pkg)

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

# Eval rule
v = engine.eval_rule('data.framework.mount_overlay')
print(v)

# Eval rule as json
v = engine.eval_rule_as_json('data.framework.mount_overlay')
print(v)

# Enable coverage
engine.set_enable_coverage(True)
engine.eval_rule('data.framework.mount_overlay')

# Print coverage
report_json = engine.get_coverage_report_as_json()
print(report_json)

# Pretty coverage report
report = engine.get_coverage_report_pretty()
print(report)

# Clone engine
engine1 = engine.clone()


# Clear coverage data
engine.clear_coverage_data();

print(engine1.get_coverage_report_pretty())

# Enable gathering prints
engine1.set_gather_prints(True)

# Gather prints
engine1.eval_query('print("Hello")')
ps = engine1.take_prints()
print(ps)
