// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

var regorus = require('./pkg/regorusjs');

// Create an engine.
var engine = new regorus.Engine();

// Enable code coverage
engine.setEnableCoverage(true);

// Add Rego policy.
var pkg = engine.addPolicy(
    // Associate this file name with policy
    'hello.rego',
    
    // Rego policy
`
  package test

  x = 10

  # Join messages
  message = concat(", ", [input.message, data.message])
`);

console.log(pkg);
// data.test

// Set policy data
engine.addDataJson(`
 {
    "message" : "World!"
 }
`);

// Set policy input
engine.setInputJson(`
 {
	"message" : "Hello"
 }
`);

// Eval rule as json
var value = engine.evalRule('data.test.message');
value = JSON.parse(value);

// Display value 
console.log(value);
// Hello, World!

// Eval query
results = engine.evalQuery('data.test.message');

// Display
console.log(results);
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
results = JSON.parse(results);

// Process result
console.log(results.result[0].expressions[0].value);
// Hello, World!

// Print coverage report
report = engine.getCoverageReport();
console.log(report);

// Print pretty report.
report = engine.getCoverageReportPretty();
console.log(report);

// RVM regular example
{
const policy = `
package demo
import rego.v1

default allow := false

allow if {
  input.user == "alice"
  input.active == true
}
`;

const modules = JSON.stringify([
  { id: "demo.rego", content: policy }
]);
const entryPoints = JSON.stringify(["data.demo.allow"]);

const program = regorus.Program.compileFromModules(
  "{}",
  modules,
  entryPoints
);

console.log(program.generateListing());

const binary = program.serializeBinary();
const deserialized = regorus.Program.deserializeBinary(binary);
if (deserialized.isPartial) {
  throw new Error("Deserialized program marked partial");
}
const rehydrated = deserialized.program();

const vm = new regorus.Rvm();
vm.loadProgram(rehydrated);
vm.setInputJson('{"user":"alice","active":true}');
console.log(vm.execute());
}

// RVM HostAwait example
{
const policy = `
package demo
import rego.v1

default allow := false

allow if {
  input.account.active == true
  details := __builtin_host_await(input.account.id, "account")
  details.tier == "gold"
}
`;

const modules = JSON.stringify([
  { id: "await.rego", content: policy }
]);
const entryPoints = JSON.stringify(["data.demo.allow"]);

const program = regorus.Program.compileFromModules(
  "{}",
  modules,
  entryPoints
);

const vm = new regorus.Rvm();
vm.setExecutionMode(1);
vm.loadProgram(program);
vm.setInputJson('{"account":{"id":"acct-1","active":true}}');
vm.execute();
console.log(vm.getExecutionState());
console.log(vm.resume('{"tier":"gold"}'));
}
