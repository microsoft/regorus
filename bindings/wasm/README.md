# regorusjs

**Regorus** is

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
   interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

`regorusjs` is Regorus compiled into WASM.

See [Repository](https://github.com/microsoft/regorus).

To build this binding, see [building](https://github.com/microsoft/regorus/bindings/wasm/building.md)



## Usage

```javascript

var regorus = require('regorusjs')

// Create an engine.
var engine = new regorus.Engine();

// Add Rego policy.
engine.add_policy(
    // Associate this file name with policy
    'hello.rego',
    
    // Rego policy
`
  package test
  
  # Join messages
  message = concat(", ", [input.message, data.message])
`)

// Set policy data
engine.add_data_json(`
 {
    "message" : "World!"
 }
`)

// Set policy input
engine.set_input_json(`
 {
	"message" : "Hello"
 }
`)

// Eval query
results = engine.eval_query('data.test.message')

// Display
console.log(results)
// {
//   "result": [
//     {
//       "expressions": [
//         {
//           "value": "Hello, World!",
//           "text": "data.test.message",
//           "location": {
//             "row": 1,
//             "col": 1
//           }
//         }
//       ]
//     }
//   ]
// }

// Convert results to object
results = JSON.parse(results)

// Process result
console.log(results.result[0].expressions[0].value)
// Hello, World!
```
