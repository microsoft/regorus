package regorus

import "testing"

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

const rvmRegularPolicy = `
package demo
import rego.v1

default allow := false

allow if {
	input.user == "alice"
	input.active == true
}
`

const rvmRegularInput = `{"user":"alice","active":true}`

func TestRvmProgramCompileAndExecute(t *testing.T) {
	modules := []PolicyModule{{Id: "demo.rego", Content: rvmRegularPolicy}}
	entryPoints := []string{"data.demo.allow"}
	program, err := CompileProgramFromModules("{}", modules, entryPoints)
	if err != nil {
		t.Fatalf("compile program: %v", err)
	}
	defer program.Close()

	listing, err := program.GenerateListing()
	if err != nil || listing == "" {
		t.Fatalf("listing failed: %v", err)
	}

	binary, err := program.SerializeBinary()
	if err != nil {
		t.Fatalf("serialize program: %v", err)
	}

	rehydrated, isPartial, err := DeserializeProgram(binary)
	if err != nil {
		t.Fatalf("deserialize program: %v", err)
	}
	if isPartial {
		t.Fatalf("deserialized program marked partial")
	}
	defer rehydrated.Close()

	vm, err := NewRvm()
	if err != nil {
		t.Fatalf("new vm: %v", err)
	}
	defer vm.Close()

	if err := vm.LoadProgram(rehydrated); err != nil {
		t.Fatalf("load program: %v", err)
	}
	if err := vm.SetInputJson(rvmRegularInput); err != nil {
		t.Fatalf("set input: %v", err)
	}

	result, err := vm.Execute()
	if err != nil {
		t.Fatalf("execute: %v", err)
	}
	if result != "true" {
		t.Fatalf("expected allow=true, got %s", result)
	}
}

func TestRvmHostAwaitSuspendResume(t *testing.T) {
	modules := []PolicyModule{{Id: "host_await.rego", Content: rvmPolicy}}
	entryPoints := []string{"data.demo.allow"}
	program, err := CompileProgramFromModules("{}", modules, entryPoints)
	if err != nil {
		t.Fatalf("compile program: %v", err)
	}
	defer program.Close()

	vm, err := NewRvm()
	if err != nil {
		t.Fatalf("new vm: %v", err)
	}
	defer vm.Close()

	if err := vm.SetExecutionMode(1); err != nil {
		t.Fatalf("set execution mode: %v", err)
	}
	if err := vm.LoadProgram(program); err != nil {
		t.Fatalf("load program: %v", err)
	}
	if err := vm.SetInputJson(rvmInput); err != nil {
		t.Fatalf("set input: %v", err)
	}

	if _, err := vm.Execute(); err != nil {
		t.Fatalf("execute in suspendable mode failed: %v", err)
	}

	state, err := vm.GetExecutionState()
	if err != nil {
		t.Fatalf("get execution state: %v", err)
	}
	if state == "" {
		t.Fatalf("expected non-empty execution state")
	}

	result, err := vm.Resume(`{"tier":"gold"}`, true)
	if err != nil {
		t.Fatalf("resume: %v", err)
	}
	if result != "true" {
		t.Fatalf("expected allow=true, got %s", result)
	}
}
