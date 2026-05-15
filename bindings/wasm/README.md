# regorusjs

**Regorus** is

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
   interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

`regorusjs` is Regorus compiled into WASM.

See [Repository](https://github.com/microsoft/regorus).

To build this binding, see [building.md](https://github.com/microsoft/regorus/blob/main/bindings/wasm/building.md)

## Automation

Run `cargo xtask build-wasm` to invoke wasm-pack with sensible defaults, or `cargo xtask test-wasm` to rebuild the package and execute `node test.js`.



## Usage

See [test.js](https://github.com/microsoft/regorus/blob/main/bindings/wasm/test.js) for example usage.

For best performance with large policies, call `engine.prepare()` after loading
policy/data, then use `engine.clone()` to create per-request engines. If
`prepare()` is skipped, the first `eval*` call performs the same one-time
setup. Adding/changing policy or data after `prepare()` invalidates the
prepared state.
