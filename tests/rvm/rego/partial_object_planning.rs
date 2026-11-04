// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, RegoVM};
use regorus::{Engine, Rc, Value};

const ENTRYPOINT: &str = "data.t.main";

fn check_policy(body: &str, expected: Value) -> Result<()> {
    let policy = format!("package t\n{body}");
    check_policies(&[&policy], expected)
}

fn check_policies(policies: &[&str], expected: Value) -> Result<()> {
    let mut engine = Engine::new();
    for (index, policy) in policies.iter().enumerate() {
        engine.add_policy(format!("{index}.rego"), (*policy).into())?;
    }
    let policy = policies.join("\n\n");
    let input = Value::from_json_str(
        r#"{"keys":["a","b"],"values":[10,20],
            "groups":[["x","y"],["z"]],"nested_values":[[1,2],[3]]}"#,
    )?;
    engine.set_input(input.clone());
    assert_eq!(
        engine.eval_rule(ENTRYPOINT.into())?,
        expected,
        "interpreter:\n{policy}"
    );

    let compiled = engine.compile_with_entrypoint(&ENTRYPOINT.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[ENTRYPOINT])?;
    let json = program.serialize_json().map_err(anyhow::Error::msg)?;
    let json_program = Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;
    let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
    let binary_program = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => program,
        DeserializationResult::Partial(_) => {
            anyhow::bail!("head-planning program needs recompilation")
        }
    };
    for program in [program, Rc::new(json_program), Rc::new(binary_program)] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_data(engine.get_data())?;
            vm.set_input(input.clone());
            vm.set_execution_mode(mode);
            assert_eq!(
                vm.execute_entry_point_by_name(ENTRYPOINT)?,
                expected,
                "{mode:?}:\n{policy}"
            );
        }
    }
    Ok(())
}

#[test]
fn shared_head_indices_match_in_all_execution_modes() -> Result<()> {
    for body in [
        r#"p[input.keys[i]] contains input.values[i] if { true }
           main := p == {"a": {10}, "b": {20}}"#,
        r#"p[input.keys[i]] contains input.values[i]
           main := p == {"a": {10}, "b": {20}}"#,
        r#"p[input.keys[i]] := input.values[i] if { true }
           main := p == {"a": 10, "b": 20}"#,
        r#"p[input.keys[i]][input.groups[i][j]] contains input.nested_values[i][j] if { true }
           main := p == {"a": {"x": {1}, "y": {2}}, "b": {"z": {3}}}"#,
        r#"p[input.keys[i]][input.groups[i][j]] := input.nested_values[i][j] if { true }
           main := p == {"a": {"x": 1, "y": 2}, "b": {"z": 3}}"#,
        r#"p[input.keys[i]] contains {
             input.groups[i][j]: input.nested_values[i][j] | true
           } if { true }
           main := p == {"a": {{"x": 1, "y": 2}}, "b": {{"z": 3}}}"#,
        r#"p[input.keys[i]].fixed contains input.values[i] if { true }
           main := p == {"a": {"fixed": {10}}, "b": {"fixed": {20}}}"#,
        r#"p[input.keys[_]] contains input.values[_] if { true }
           main := p == {"a": {10, 20}, "b": {10, 20}}"#,
        r#"p[ks[i]] contains i if { ks := {"a": 10, "b": 20} }
           main := p == {10: {"a"}, 20: {"b"}}"#,
        r#"p[ks[i]] contains i if { ks := {1, 2} }
           main := p == {1: {1}, 2: {2}}"#,
        r#"p[input.keys[i]] contains [input.values[i], v] if { some v in [false, null] }
           main := p == {"a": {[10, false], [10, null]}, "b": {[20, false], [20, null]}}"#,
        r#"p[input.keys[i]] contains vs[i] if { vs := [10] }
           main := p == {"a": {10}}"#,
    ] {
        check_policy(body, Value::Bool(true))?;
    }
    Ok(())
}

#[test]
fn head_plans_are_specific_to_each_independent_body() -> Result<()> {
    for body in [
        r#"p[input.keys[i]] := input.values[i] if { i := 0 } { true }
           main := p == {"a": 10, "b": 20}"#,
        r#"p[input.keys[i]] := input.values[i] if { true } { i := 0 }
           main := p == {"a": 10, "b": 20}"#,
        r#"p[input.keys[i]] := input.values[i] if { true } { i := 99 }
           main := p == {"a": 10, "b": 20}"#,
        r#"p[input.keys[i]] := input.values[i] if { false } { true }
           main := p == {"a": 10, "b": 20}"#,
        r#"p[ks[i]] := vs[i] if { ks := ["a"]; vs := [10] } {
             ks := ["b"]; vs := [20]; i := 0
           }
           main := p == {"a": 10, "b": 20}"#,
        r#"p[ks[i]].fixed := vs[i] if { ks := ["a"]; vs := [10] } {
             ks := ["b"]; vs := [20]; i := 0
           }
           main := p == {"a": {"fixed": 10}, "b": {"fixed": 20}}"#,
        r#"p[input.keys[i]] contains {k: v[i] |
             some k, v in {"value": input.values}
           } if { true }
           main := p == {"a": {{"value": 10}}, "b": {{"value": 20}}}"#,
        r#"p := input.missing[i] if { false } else := 20 if { true }
           main := p == 20"#,
        r#"p[k] := {input.keys[i]: input.values[i] | true} if {
             k := "a"; i := 0
           } { k := "b" }
           main := p == {"a": {"a": 10}, "b": {"a": 10, "b": 20}}"#,
        r#"p[k] := {input.keys[i]: value |
             some value in input.values
             value == input.values[i]
           } if { k := "a"; i := 0 } { k := "b" }
           main := p == {"a": {"a": 10}, "b": {"a": 10, "b": 20}}"#,
        r#"p[k] := [i | input.values[i] > 0] if {
             k := "a"; i := 0
           } { k := "b" }
           main := p == {"a": [0], "b": [0, 1]}"#,
        r#"p[k] := [i | every x in [input.values[i]] { x > 0 }] if {
             k := "a"; i := 0
           } { k := "b" }
           main := p == {"a": [0], "b": [0, 1]}"#,
    ] {
        check_policy(body, Value::Bool(true))?;
    }
    Ok(())
}

#[test]
fn head_plans_and_function_bindings_are_module_specific() -> Result<()> {
    check_policies(
        &[
            r#"package t
               p[ks[i]] contains vs[i] if { ks := ["a"]; vs := [10] }
               main := p == {"a": {10}, "b": {20}}"#,
            r#"package t
               p[ks[i]] contains vs[i] if { ks := ["b"]; vs := [20]; i := 0 }"#,
        ],
        Value::Bool(true),
    )?;
    check_policies(
        &[
            "package helper\nf([x]) := x",
            r#"package t
               import data.helper.f
               p[input.keys[i]] contains f([input.values[i]]) if { true }
               main := p == {"a": {10}, "b": {20}}"#,
        ],
        Value::Bool(true),
    )
}

#[test]
fn independent_partial_bodies_accumulate_in_both_vm_modes() -> Result<()> {
    for body in [
        r#"p[k] := 1 if { k := "a" } { k := "b" }
           main := p == {"a": 1, "b": 1}"#,
        r#"p[k] contains 1 if { k := "a" }
           p[k] contains 1 if { k := "b" }
           main := p == {"a": {1}, "b": {1}}"#,
        r#"p[k].fixed := 1 if { k := "a" } { k := "b" }
           main := p == {"a": {"fixed": 1}, "b": {"fixed": 1}}"#,
    ] {
        check_policy(body, Value::Bool(true))?;
    }
    Ok(())
}

#[test]
fn missing_scalar_and_empty_head_collections_make_no_contribution() -> Result<()> {
    for (head, expected) in [
        ("p[k] contains 1", Value::Undefined),
        ("p[k] := 1", Value::new_object()),
    ] {
        check_policy(
            &format!("{head} if {{ false; k := \"a\" }}\nmain := p"),
            expected,
        )?;
    }
    check_policy(
        "p[input.missing[i]] contains input.values[i] if { true }\nmain := p",
        Value::Undefined,
    )?;
    for collection in ["false", "null", "7", r#""scalar""#, "[]", "{}"] {
        check_policy(
            &format!("p[xs[i]] contains input.values[i] if {{ xs := {collection} }}\nmain := p"),
            Value::Undefined,
        )?;
    }
    Ok(())
}
