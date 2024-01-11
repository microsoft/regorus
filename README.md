# Regorus

**Regorus** is 

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/) interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

Regorus is available as a library that can be easily integrated into your Rust projects.


Regorus passes the [OPA v0.60.0 test-suite](https://www.openpolicyagent.org/docs/latest/ir/#test-suite) barring a few builtins.
See [OPA Conformance][#opa-conformance] below.

## Getting Started

[examples/regorus](examples/regorus.rs) is an example program that shows how to integrate Regorus into your project and evaluate Rego policies.

To build and install it, do

    cargo install --example regorus --path .


Check that the regorus example program is working

    $ regorus
    Usage: regorus <COMMAND>
    
    Commands:
      eval   Evaluate a Rego Query
      lex    Tokenize a Rego policy
      parse  Parse a Rego policy
      help   Print this message or the help of the given subcommand(s)
    
    Options:
      -h, --help     Print help
      -V, --version  Print versionUsage: regorus <COMMAND>



First, let's evaluate a simple Rego expression `1*2+3`

    regorus eval "1*2+3"

This produces the following output

    {
      "result": [
        {
          "expressions": [
            {
               "value": 5,
               "text": "1*2+3",
               "location": {
                 "row": 1,
                 "col": 1
              }
            }
          ]
        }
      ]
    }

Next, evaluate a sample [policy](examples/example.rego) and [input](examples/input.json) (borrowed from [Rego tutorial](https://www.openpolicyagent.org/docs/latest/#2-try-opa-eval)):

    regorus eval -d examples/example.rego -i examples/input.json data.example

Finally, evaluate real-world [policies](tests/aci/) used in Azure Container Instances (ACI)

    regorus eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.policy.mount_overlay=x


## ACI Policies

Regorus successfully passes the ACI policy test-suite. It is fast and can run each of the tests in a few milliseconds.

    $ cargo test -r --test aci
        Finished release [optimized + debuginfo] target(s) in 0.05s
         Running tests/aci/main.rs (target/release/deps/aci-2cd8d21a893a2450)
    aci/mount_device                                  passed    3.863292ms
    aci/mount_overlay                                 passed    3.6905ms
    aci/scratch_mount                                 passed    3.643041ms
    aci/create_container                              passed    5.046333ms
    aci/shutdown_container                            passed    3.632ms
    aci/scratch_unmount                               passed    3.631333ms
    aci/unmount_overlay                               passed    3.609916ms
    aci/unmount_device                                passed    3.626875ms
    aci/load_fragment                                 passed    4.045167ms

Run the ACI policies in the `tests/aci` directory, using data `tests/aci/data.json` and input `tests/aci/input.json`:

    regorus eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.policy.mount_overlay=x


Verify that [OPA](https://github.com/open-policy-agent/opa/releases) produces the same output

    diff <(regorus eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x) \
         <(opa eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x)

## Performance

To check how fast Regorus runs on your system, first install a tool like [hyperfine](https://github.com/sharkdp/hyperfine).

    cargo install hyperfine

Then benchmark evaluation of the ACI policies,

    $ hyperfine "regorus eval -b tests/aci -d tests/aci/data.json -i   tests/aci/input.json data.framework.mount_overlay=x"
    Benchmark 1: regorus eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x
      Time (mean ± σ):       4.6 ms ±   0.2 ms    [User: 4.1 ms, System: 0.4 ms]
      Range (min … max):     4.4 ms …   6.0 ms    422 runs
 
Compare it with OPA

    $  hyperfine "opa eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x"
    Benchmark 1: opa eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x
      Time (mean ± σ):      45.2 ms ±   0.6 ms    [User: 68.8 ms, System: 5.1 ms]
      Range (min … max):    43.8 ms …  46.7 ms    62 runs


## OPA Conformance

Regorus has been verified to be compliant with [OPA v0.60.0](https://github.com/open-policy-agent/opa/releases/tag/v0.60.0) 
using a [test driver](tests/opa.rs) that loads and runs the OPA testsuite using Regorus, and verifies that expected outputs
are produced.

The test driver can be invoked by running:

```
cargo test -r --test opa
```

Currently, Regorus passes all the non-builtin specific tests. See [passing tests suites](tests/opa.passing).

The following test suites don't pass fully due to mising builtins:
- `cryptoparsersaprivatekeys`
- `cryptox509parseandverifycertificates`
- `cryptox509parsecertificaterequest`
- `cryptox509parsecertificates`
- `cryptox509parsekeypair`
- `cryptox509parsersaprivatekey`
- `globsmatch`
- `graphql`
- `invalidkeyerror`
- `jsonpatch`
- `jwtbuiltins`
- `jwtdecodeverify`
- `jwtencodesign`
- `jwtencodesignraw`
- `jwtverifyhs256`
- `jwtverifyhs384`
- `jwtverifyhs512`
- `jwtverifyrsa`
- `netcidrcontains`
- `netcidrcontainsmatches`
- `netcidrexpand`
- `netcidrintersects`
- `netcidrisvalid`
- `netcidrmerge`
- `netcidroverlap`
- `netlookupipaddr`
- `providers-aws`
- `regometadatachain`
- `regometadatarule`
- `regoparsemodule`
- `rendertemplate`
- `time`

They are captured in the following [github issues](https://github.com/microsoft/regorus/issues?q=is%3Aopen+is%3Aissue+label%3Alib).

### Grammar

The grammar used by Regorus to parse Rego policies is described in [grammar.md](docs/grammar.md) in both EBNF and RailRoad Diagram formats.

## Contributing

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit https://cla.opensource.microsoft.com.

When you submit a pull request, a CLA bot will automatically determine whether you need to provide
a CLA and decorate the PR appropriately (e.g., status check, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

## Trademarks

This project may contain trademarks or logos for projects, products, or services. Authorized use of Microsoft 
trademarks or logos is subject to and must follow 
[Microsoft's Trademark & Brand Guidelines](https://www.microsoft.com/en-us/legal/intellectualproperty/trademarks/usage/general).
Use of Microsoft trademarks or logos in modified versions of this project must not cause confusion or imply Microsoft sponsorship.
Any use of third-party trademarks or logos are subject to those third-party's policies.
