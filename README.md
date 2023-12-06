# Regorus

**Regorus** is 

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/) interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

Regorus is available as a library that can be easily integrated into your Rust projects.


> **Warning**
> While Regorus is highly performant and can interpret complex Rego policies, it does not yet pass the full [OPA test-suite](https://www.openpolicyagent.org/docs/latest/ir/#test-suite).
> We are actively working to achieve full OPA compliance. Meanwhile, Regorus should be considered
> **experimental and used with discretion**.

## Getting Started

[regorus](examples/regorus.rs) is an example program that shows how to integrate Regorus into your project and evaluate Rego policies.

To build it, do

    cargo build -r --example regorus


Check that the regorus example program is working

    $ target/release/examples/regorus
    Usage: regorus <COMMAND>
    
    Commands:
      eval   Evaluate a Rego Query
      lex    Tokenize a Rego policy
      parse  Parse q Rego policy
      help   Print this message or the help of the given subcommand(s)

    Options:
      -h, --help     Print help
      -V, --version  Print version


First, let's evaluate a simple Rego expression `1*2+3`

    target/release/examples/regorus eval "1*2+3"

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

    target/release/examples/regorus eval -d examples/example.rego -i examples/input.json data.example

Finally, evaluate real-world [policies](tests/aci/) used in Azure Container Instances (ACI)

    target/release/examples/regorus eval -d tests/aci/framework.rego \
        -d tests/aci/policy.rego \
        -d tests/aci/api.rego  \
        -d tests/aci/data.json  \
        -i tests/aci/input.json \
         data.policy.mount_overlay=x


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

    target/release/examples/regorus eval \
         -b tests/aci \
         -d tests/aci/data.json \
         -i tests/aci/input.json \
         data.framework.mount_overlay=x

Verify that [OPA](https://github.com/open-policy-agent/opa/releases) produces the same output

    diff <(target/release/examples/regorus eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x) <(opa eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x)

## Performance

To check how fast Regorus runs on your system, first install a tool like [hyperfine](https://github.com/sharkdp/hyperfine).

   cargo install hyperfine

Then benchmark evaluation of the ACI policies,

    $ hyperfine "target/release/examples/regorus eval -b tests/aci -d tests/aci/data.json -i   tests/aci/input.json data.framework.mount_overlay=x"
    Benchmark 1: target/release/examples/regorus eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x
      Time (mean ± σ):       4.6 ms ±   0.2 ms    [User: 4.1 ms, System: 0.4 ms]
      Range (min … max):     4.4 ms …   6.0 ms    422 runs
 
Compare it with OPA

    $  hyperfine "opa eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x"
    Benchmark 1: opa eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x
      Time (mean ± σ):      45.2 ms ±   0.6 ms    [User: 68.8 ms, System: 5.1 ms]
      Range (min … max):    43.8 ms …  46.7 ms    62 runs


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
