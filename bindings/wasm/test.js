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
