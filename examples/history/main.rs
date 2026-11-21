// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Decide requests against a committed event history with `history.require` and
//! `history.forbid`. Run with `cargo run --example history --features history`.

use regorus::languages::history_table::{HistoryStore, ACTION, PRINCIPAL, RESOURCE};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::RegoVM;
use regorus::Engine;
use std::sync::Arc;

const POLICY: &str = r#"
package example
import rego.v1

# A principal may release a resource only after editing it ...
edited := history.require(
    {"action": "release", "principal": p, "resource": r},
    [any, {principal == p, action == "edit", resource == r}, any],
)

# ... and nobody may release a resource once it has been removed.
not_removed := history.forbid(
    {"action": "release", "principal": p, "resource": r},
    [any, {action == "remove", resource == r}, any],
)

default allow := false

allow if {
    edited
    not_removed
}
"#;

fn main() -> anyhow::Result<()> {
    let mut engine = Engine::new();
    engine.add_policy("example.rego".into(), POLICY.into())?;
    let policy = engine.compile_with_entrypoint(&"data.example.allow".into())?;
    let program = Compiler::compile_from_policy(&policy, &["data.example.allow"])?;

    // Paths are interned once per coordinate; events are triples of their IDs.
    let store = Arc::new(HistoryStore::new());
    let event = |principal: &str, action: &str, resource: &str| -> anyhow::Result<_> {
        Ok(store.event(&[
            store.intern(PRINCIPAL, principal)?,
            store.intern(ACTION, action)?,
            store.intern(RESOURCE, resource)?,
        ])?)
    };

    let history = store.new_history()?;
    store.append(&history, &[event("alice", "edit", "doc")?])?;

    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.attach_history(store.clone())?;

    let mut decide = |label: &str, request| -> anyhow::Result<()> {
        // Deciding never appends the request to the history.
        vm.set_history_input(history.clone(), request)?;
        let allow = vm.execute_entry_point_by_name("data.example.allow")?;
        println!("{label}: allow = {allow}");
        Ok(())
    };
    decide(
        "alice releases doc after editing it",
        event("alice", "release", "doc")?,
    )?;
    decide(
        "bob releases doc without editing it",
        event("bob", "release", "doc")?,
    )?;

    store.append(&history, &[event("carol", "remove", "doc")?])?;
    decide(
        "alice releases doc after it was removed",
        event("alice", "release", "doc")?,
    )?;
    Ok(())
}
