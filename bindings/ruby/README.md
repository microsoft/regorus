# Regorusrb

**Regorus** is

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
   interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

Regorus can be used in Ruby by  Use the bundler CLI to add the gem from remote git source:
`
bundle add regorus --git 'https://github.com/microsoft/regorus/tree/main/bindings/ruby'
`

or manually edit your gemfile to include the following
`
gem "regorus", git: "https://github.com/microsoft/regorus/tree/main/bindings/ruby"
`

It is not yet available in rubygems.

See [Repository](https://github.com/microsoft/regorus).

To build this gem locally

`rake build`

then to install the gem and build the native extensions,

`gem install --local ./pkg/regorusrb-0.1.0.gem`

## Installation

TODO: Replace `UPDATE_WITH_YOUR_GEM_NAME_IMMEDIATELY_AFTER_RELEASE_TO_RUBYGEMS_ORG` with your gem name right after releasing it to RubyGems.org. Please do not do it earlier due to security reasons. Alternatively, replace this section with instructions to install your gem from git if you don't plan to release to RubyGems.org.

Install the gem and add to the application's Gemfile by executing:

    $ bundle add UPDATE_WITH_YOUR_GEM_NAME_IMMEDIATELY_AFTER_RELEASE_TO_RUBYGEMS_ORG

If bundler is not being used to manage dependencies, install the gem by executing:

    $ gem install UPDATE_WITH_YOUR_GEM_NAME_IMMEDIATELY_AFTER_RELEASE_TO_RUBYGEMS_ORG

## Usage

```ruby
require "regorus"

engine = Regorus::Engine.new

engine.add_policy_from_file('../../tests/aci/framework.rego')
engine.add_policy_from_file('../../tests/aci/api.rego')
engine.add_policy_from_file('../../tests/aci/policy.rego')


# can be strings or symbols
data = {
  metadata: {
    devices: {
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
puts results[:result][0]

# Eval query as json
results_json = engine.eval_query_as_json('data.framework.mount_overlay=x')
puts results_json
```

## Development

After checking out the repo, run `bin/setup` to install dependencies. Then, run `rake test` to run the tests. You can also run `bin/console` for an interactive prompt that will allow you to experiment.

To install this gem onto your local machine, run `bundle exec rake install`. To release a new version, update the version number in `version.rb`, and then run `bundle exec rake release`, which will create a git tag for the version, push git commits and the created tag, and push the `.gem` file to [rubygems.org](https://rubygems.org).

