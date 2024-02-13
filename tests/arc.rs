// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use lazy_static::lazy_static;
use std::sync::Mutex;

use regorus::*;

// Ensure that types can be s
lazy_static! {
    static ref VALUE: Value = Value::Null;
    static ref ENGINE: Mutex<Engine> = Mutex::new(Engine::new());
//    static ref ENGINE: Engine = Engine::new();
}

#[test]
fn shared_engine() -> anyhow::Result<()> {
    let e_guard = ENGINE.lock();
    let mut engine = e_guard.expect("failed to lock engine");

    engine.add_policy(
        "hello.rego".to_string(),
        r#"
package test
allow = true
"#
        .to_string(),
    )?;

    let results = engine.eval_query("data.test.allow".to_string(), false)?;
    assert_eq!(results.result[0].expressions[0].value, Value::from(true));
    Ok(())
}
