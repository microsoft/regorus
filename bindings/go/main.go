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
		if err := engine.AddPolicyFromFile(policy); err != nil {
			fmt.Fprintf(os.Stderr, "error: %v\n", err)
			os.Exit(1)
		}
	}
	if err = engine.AddDataFromJsonFile("../../tests/aci/data.json"); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	elapsed2 := time.Since(t)

	t = time.Now()
	// Set input and eval query.
	if err = engine.SetInputFromJsonFile("../../tests/aci/input.json"); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}


	if output, err = engine.EvalQuery("data.framework.mount_overlay = x"); err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
	elapsed3 := time.Since(t)

	fmt.Println("{%s}", output)
	fmt.Printf("NewEngine took %v\n", elapsed1)
	fmt.Printf("Add policies and data took %v\n", elapsed2)
	fmt.Printf("Set input and eval query took %v\n", elapsed3)
}
