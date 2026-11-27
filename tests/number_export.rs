// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// `Number` is the payload of `Value::Number`; it must be nameable from the crate root.
use regorus::{Number, Value};

#[test]
fn number_is_exported() -> anyhow::Result<()> {
    let value = Value::from(42_u64);
    let number: &Number = value.as_number()?;
    assert_eq!(number.as_u64(), Some(42));
    Ok(())
}
