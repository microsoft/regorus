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
}
