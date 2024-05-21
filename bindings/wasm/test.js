// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

var regorus = require('./pkg/regorusjs')

// Create an engine.
var engine = new regorus.Engine();

// Add Rego policy.
var pkg = engine.add_policy(
    // Associate this file name with policy
    'hello.rego',
    
    // Rego policy
`
  package test
  
  # Join messages
  message = concat(", ", [input.message, data.message])
`)
console.log("Loaded policy " + pkg)

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
var results = engine.eval_query('data.test.message')

// Display
console.log(results)

// Convert results to object
results = JSON.parse(results)

// Process result
console.log(results.result[0].expressions[0].value)

