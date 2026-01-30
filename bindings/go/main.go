package main

import (
	"fmt"
	"os"
	"regorus_test/pkg/regorus"
	"time"
)

func main() {
	var output string
	var err error

	t := time.Now();

	// Create new engine
	engine := regorus.NewEngine()
	defer engine.Close()

	engine.SetRegoV0(true)
	elapsed1 := time.Since(t)
	
	
	t = time.Now()
	// Add policies and data.
	policies := []string{
		"../../tests/aci/framework.rego",
		"../../tests/aci/api.rego",
		"../../tests/aci/policy.rego",
	}
	for _, policy := range policies {
		var pkg string
		if pkg, err = engine.AddPolicyFromFile(policy); err != nil {
			fmt.Fprintf(os.Stderr, "error: %v\n", err)
			os.Exit(1)
		}
		fmt.Printf("Loaded package %s\n", pkg);
	}
	if err = engine.AddDataFromJsonFile("../../tests/aci/data.json"); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	elapsed2 := time.Since(t)

	t = time.Now()
	// Set input.
	if err = engine.SetInputFromJsonFile("../../tests/aci/input.json"); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}

	// Eval Rule
	if output, err = engine.EvalRule("data.framework.mount_overlay"); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	elapsed3 := time.Since(t)

	fmt.Printf("%s\n", output)
	fmt.Printf("NewEngine took %v\n", elapsed1)
	fmt.Printf("Add policies and data took %v\n", elapsed2)
	fmt.Printf("Set input and eval query took %v\n", elapsed3)

	// Create new engine.
	engine1 := regorus.NewEngine()
	defer engine1.Close()

	// Enable coverage
	engine1.SetEnableCoverage(true)

	var pkg string
	pkg, err = engine1.AddPolicy("test.rego", "package test\nx = 1\nmessage = `Hello`")
	fmt.Printf("Loaded package %s\n", pkg)

	// Eval Rule
	if output, err = engine1.EvalRule("data.test.message"); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("%s\n", output)

	// Print pretty coverage report.
	if output, err = engine1.GetCoverageReportPretty(); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("%s\n", output)

	// Print packages
	if output, err = engine1.GetPackages(); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("%s\n", output)

	// Print policies
	if output, err = engine1.GetPolicies(); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("%s\n", output)

	// RVM regular example (compile, serialize, execute)
	const regularPolicy = `
package demo
import rego.v1

default allow := false

allow if {
  input.user == "alice"
  input.active == true
}
`
	const regularInput = `{"user":"alice","active":true}`

	regularModules := []regorus.PolicyModule{{Id: "demo.rego", Content: regularPolicy}}
	regularEntryPoints := []string{"data.demo.allow"}
	regularProgram, err := regorus.CompileProgramFromModules("{}", regularModules, regularEntryPoints)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	defer regularProgram.Close()

	listing, err := regularProgram.GenerateListing()
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("RVM listing:\n%s\n", listing)

	binary, err := regularProgram.SerializeBinary()
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	regularProgram.Close()

	rehydrated, isPartial, err := regorus.DeserializeProgram(binary)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	if isPartial {
		fmt.Fprintf(os.Stderr, "error: program marked partial\n")
		os.Exit(1)
	}
	defer rehydrated.Close()

	regularVm, err := regorus.NewRvm()
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	defer regularVm.Close()

	if err := regularVm.LoadProgram(rehydrated); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	if err := regularVm.SetInputJson(regularInput); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}

	regularResult, err := regularVm.Execute()
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("RVM regular result: %s\n", regularResult)

	// RVM HostAwait example
	const rvmPolicy = `
package demo
import rego.v1

default allow := false

allow if {
  input.account.active == true
  details := __builtin_host_await(input.account.id, "account")
  details.tier == "gold"
}
`
	const rvmInput = `{"account":{"id":"acct-1","active":true}}`

	modules := []regorus.PolicyModule{{Id: "demo.rego", Content: rvmPolicy}}
	entryPoints := []string{"data.demo.allow"}
	program, err := regorus.CompileProgramFromModules("{}", modules, entryPoints)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	defer program.Close()

	vm, err := regorus.NewRvm()
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	defer vm.Close()

	if err := vm.SetExecutionMode(1); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	if err := vm.LoadProgram(program); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	if err := vm.SetInputJson(rvmInput); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}

	if _, err := vm.Execute(); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}

	state, err := vm.GetExecutionState()
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("HostAwait state: %s\n", state)

	result, err := vm.Resume(`{"tier":"gold"}`, true)
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("HostAwait result: %s\n", result)
}
