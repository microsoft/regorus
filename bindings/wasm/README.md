# regorus-wasm

**Regorus** is

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
   interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

See [Repository](https://github.com/microsoft/regorus).

`regorus-wasm` is Regorus compiled into WASM.

## Usage

In nodejs,

``javascript

var regorus = require('regorus-wasm')

// Create an engine.
var engine = new regorus.Engine();

// Add Rego policy.
engine.add_policy()


```
