# Regorus

**Regorus** is

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
   interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

Regorus is also
  - *cross-platform* - Written in platform-agnostic Rust.
  - *current* - We strive to keep Regorus up to date with latest OPA release. Regorus supports `import rego.v1`.
  - *compliant* - Regorus is mostly compliant with the latest [OPA release v0.62.0](https://github.com/open-policy-agent/opa/releases/tag/v0.62.0). See [OPA Conformance](#opa-conformance) for details. Note that while we behaviorally produce the same results, we don't yet support all the builtins.
  - *extensible* - Extend the Rego language by implementing custom stateful builtins in Rust.
    See [add_extension](https://github.com/microsoft/regorus/blob/fc68bf9c8bea36427dae9401a7d1f6ada771f7ab/src/engine.rs#L352).
    Support for extensibility using other languages coming soon.
  - *polyglot* - In addition to Rust, Regorus can be used from *C*, *C++*, *C#*, *Golang*, *Java*, *Javascript*, *Python*, and *Ruby*.
    This is made possible by the excellent FFI tools available in the Rust ecosystem. See [bindings](#bindings) for information on how to use Regorus from different languages.

    To try out a *Javascript(WASM)* compiled version of Regorus from your browser, visit [Regorus Playground](https://anakrish.github.io/regorus-playground/).



Regorus is available as a library that can be easily integrated into your Rust projects.
Here is an example of evaluating a simple Rego policy:

```rust
use anyhow::Result;
use regorus::*;
use serde_json;

fn main() -> Result<()> {
  // Create an engine for evaluating Rego policies.
  let mut engine = Engine::new();

  // Add policy to the engine.
  engine.add_policy(
    // Filename to be associated with the policy.
    "hello.rego".to_string(),

    // Rego policy that just sets a message.
    r#"
       package test
       message = "Hello, World!"
    "#.to_string()
  )?;

  // Evaluate the policy, fetch the message and print it.
  let results = engine.eval_query("data.test.message".to_string(), false)?;
  println!("{}", serde_json::to_string_pretty(&results)?);

  Ok(())
}
```

Regorus is designed with [Confidential Computing](https://confidentialcomputing.io/about/) in mind. In Confidential Computing environments,
it is important to be able to control exactly what is being run. Regorus allows enabling and disabling various components using cargo
features. By default all features are enabled.

The default build of regorus example program is 6.4M:
```bash
$ cargo build -r --example regorus; strip target/release/examples/regorus; ls -lh target/release/examples/regorus
-rwxr-xr-x  1 anand  staff   6.4M Jan 19 11:23 target/release/examples/regorus*
```


When all features except for `yaml` are disabled, the binary size drops down to 2.9M.
```bash
$ cargo build -r --example regorus --features "yaml" --no-default-features; strip target/release/examples/regorus; ls -lh target/release/examples/regorus
-rwxr-xr-x  1 anand  staff   2.9M Jan 19 11:26 target/release/examples/regorus*
```

Regorus passes the [OPA v0.61.0 test-suite](https://www.openpolicyagent.org/docs/latest/ir/#test-suite) barring a few
builtins. See [OPA Conformance](#opa-conformance) below.

## Bindings

Regorus can be used from a variety of languages:

- *C*: C binding is generated using [cbindgen](https://github.com/mozilla/cbindgen).
  [corrosion-rs](https://github.com/corrosion-rs/corrosion) can be used to seamlessly use Regorous
   in your CMake based projects. See [bindings/c](https://github.com/microsoft/regorus/tree/main/bindings/c).
- *C++*: C++ binding is generated using [cbindgen](https://github.com/mozilla/cbindgen).
  [corrosion-rs](https://github.com/corrosion-rs/corrosion) can be used to seamlessly use Regorous
   in your CMake based projects. See [bindings/cpp](https://github.com/microsoft/regorus/tree/main/bindings/cpp).
- *C#*: C# binding is generated using [csbindgen](https://github.com/Cysharp/csbindgen). See [bindings/csharp](https://github.com/microsoft/regorus/tree/main/bindings/csharp) for an example of how to build and use Regorus in your C# projects.
- *Golang*: The C bindings are exposed to Golang via [CGo](https://pkg.go.dev/cmd/cgo). See [bindings/go](https://github.com/microsoft/regorus/tree/main/bindings/go) for an example of how to build and use Regorus in your Go projects.
- *Python*: Python bindings are generated using [pyo3](https://github.com/PyO3/pyo3). Wheels are created using [maturin](https://github.com/PyO3/maturin). See [bindings/python](https://github.com/microsoft/regorus/tree/main/bindings/python).
- *Java*: Java bindings are developed using [jni-rs](https://github.com/jni-rs/jni-rs).
  See [bindings/java](https://github.com/microsoft/regorus/tree/main/bindings/java).
- *Javascript*: Regorus is compiled to WASM using [wasmpack](https://github.com/rustwasm/wasm-pack).
  See [bindings/wasm](https://github.com/microsoft/regorus/tree/main/bindings/wasm) for an example of using Regorus from nodejs.
  To try out a *Javascript(WASM)* compiled version of Regorus from your browser, visit [Regorus Playground](https://anakrish.github.io/regorus-playground/).
- *Ruby*: Ruby bindings are developed using [magnus](https://github.com/matsadler/magnus).
  See [bindings/ruby](https://github.com/microsoft/regorus/tree/main/bindings/ruby).

To avoid operational overhead, we currently don't publish these bindings to various repositories.
It is straight-forward to build these bindings yourself.


## Getting Started

[examples/regorus](https://github.com/microsoft/regorus/blob/main/examples/regorus.rs) is an example program that
shows how to integrate Regorus into your project and evaluate Rego policies.

To build and install it, do

```bash
$ cargo install --example regorus --path .
```

Check that the regorus example program is working

```bash
$ regorus
Usage: regorus <COMMAND>

Commands:
  eval   Evaluate a Rego Query
  lex    Tokenize a Rego policy
  parse  Parse a Rego policy
  help   Print this message or the help of the given subcommand(s)

Options:
  -h, --help     Print help
  -V, --version  Print version
```


First, let's evaluate a simple Rego expression `1*2+3`

```bash
$ regorus eval "1*2+3"
```

This produces the following output

```json
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
```

Next, evaluate a sample [policy](https://github.com/microsoft/regorus/blob/main/examples/example.rego) and [input](https://github.com/microsoft/regorus/blob/main/examples/input.json)
(borrowed from [Rego tutorial](https://www.openpolicyagent.org/docs/latest/#2-try-opa-eval)):

```bash
$ regorus eval -d examples/example.rego -i examples/input.json data.example
```

Finally, evaluate real-world [policies](tests/aci/) used in Azure Container Instances (ACI)

```bash
$ regorus eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.policy.mount_overlay=x
```

## Policy coverage

Regorus allows determining which lines of a policy have been executed using the `coverage` feature (enabled by default).

We can try it out using the `regorus` example program by passing in the `--coverage` flag.

```shell
$ regorus eval -d examples/example.rego -i examples/input.json data.example --coverage
```

It produces the following coverage report which shows that all lines are executed except the line that sets `allow` to true.

![coverage.png](https://github.com/microsoft/regorus/blob/main/docs/coverage.png?raw=true)

See [Engine::get_coverage_report](https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_coverage_report) for details.
Policy coverage information is useful for debugging your policy as well as to write tests for your policy so that all 
lines of the policy are exercised by the tests.

## ACI Policies

Regorus successfully passes the ACI policy test-suite. It is fast and can run each of the tests in a few milliseconds.

```bash
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
```

Run the ACI policies in the `tests/aci` directory, using data `tests/aci/data.json` and input `tests/aci/input.json`:

```bash
$ regorus eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.policy.mount_overlay=x
```

Verify that [OPA](https://github.com/open-policy-agent/opa/releases) produces the same output

```bash
$ diff <(regorus eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x) \
       <(opa eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x)
```


## Performance

To check how fast Regorus runs on your system, first install a tool like [hyperfine](https://github.com/sharkdp/hyperfine).

```bash
$ cargo install hyperfine
```

Then benchmark evaluation of the ACI policies,

```bash
$ hyperfine "regorus eval -b tests/aci -d tests/aci/data.json -i   tests/aci/input.json data.framework.mount_overlay=x"
Benchmark 1: regorus eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x
  Time (mean ± σ):       4.6 ms ±   0.2 ms    [User: 4.1 ms, System: 0.4 ms]
  Range (min … max):     4.4 ms …   6.0 ms    422 runs
```

Compare it with OPA

```bash
$ hyperfine "opa eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x"
Benchmark 1: opa eval -b tests/aci -d tests/aci/data.json -i tests/aci/input.json data.framework.mount_overlay=x
  Time (mean ± σ):      45.2 ms ±   0.6 ms    [User: 68.8 ms, System: 5.1 ms]
  Range (min … max):    43.8 ms …  46.7 ms    62 runs

```
## OPA Conformance

Regorus has been verified to be compliant with [OPA v0.61.0](https://github.com/open-policy-agent/opa/releases/tag/v0.61.0)
using a [test driver](https://github.com/microsoft/regorus/blob/main/tests/opa.rs) that loads and runs the OPA testsuite using Regorus, and verifies that expected outputs
are produced.

The test driver can be invoked by running:

```bash
$ cargo test -r --test opa
```

Currently, Regorus passes all the non-builtin specific tests.
See [passing tests suites](https://github.com/microsoft/regorus/blob/main/tests/opa.passing).

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

They are captured in the following [github issues](https://github.com/microsoft/regorus/issues?q=is%3Aopen+is%3Aissue+label%3Alib).


### Grammar

The grammar used by Regorus to parse Rego policies is described in [grammar.md](https://github.com/microsoft/regorus/blob/main/docs/grammar.md)
in both [W3C EBNF](https://www.w3.org/Notation.html) and [RailRoad Diagram](https://en.wikipedia.org/wiki/Syntax_diagram) formats.


## Contributing

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit <https://cla.opensource.microsoft.com>.

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
