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

The standard `regorusjs` package excludes explanation APIs. Use
`cargo xtask build-wasm --experimental` or `cargo xtask test-wasm --experimental` to produce or
test the separate `regorusjs-experimental` package. Its APIs and report formats may change before
stabilization.



## Usage

See [test.js](https://github.com/microsoft/regorus/blob/main/bindings/wasm/test.js) for example usage.
