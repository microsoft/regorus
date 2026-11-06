// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::cmp::Ordering;

use crate::value::compare_checked;
use crate::Value;

use super::errors::{Result, VmError};
use super::machine::RegoVM;

fn operands(registers: &[Value], pc: usize, left: u8, right: u8) -> Result<(&Value, &Value)> {
    let get = |index: u8| {
        registers
            .get(usize::from(index))
            .ok_or(VmError::RegisterIndexOutOfBounds {
                index,
                pc,
                register_count: registers.len(),
            })
    };
    Ok((get(left)?, get(right)?))
}

impl RegoVM {
    pub(super) fn compare_registers(
        &mut self,
        left: u8,
        right: u8,
        equality: bool,
    ) -> Result<Ordering> {
        if self.execution_timer.config().is_none() {
            return Ok(self.get_register(left)?.cmp(self.get_register(right)?));
        }

        let pc = self.pc;
        let (left, right) = operands(&self.registers, pc, left, right)?;
        compare_checked(left, right, equality, &mut || {
            Self::tick_execution_timer(&mut self.execution_timer, pc, 1)?;
            crate::utils::limits::check_memory_limit_if_needed()
                .map_err(|error| VmError::from(anyhow::Error::new(error)))
        })
    }

    pub(super) fn contains_registers(&mut self, collection: u8, value: u8) -> Result<bool> {
        let pc = self.pc;
        let (value, collection) = operands(&self.registers, pc, value, collection)?;
        if self.execution_timer.config().is_none() {
            return Ok(match *collection {
                Value::Set(ref items) => items.contains(value),
                Value::Array(ref items) => items.contains(value),
                Value::Object(ref items) => items.values().any(|item| item == value),
                _ => false,
            });
        }

        let mut equals = |item: &Value| {
            compare_checked(item, value, true, &mut || {
                Self::tick_execution_timer(&mut self.execution_timer, pc, 1)?;
                crate::utils::limits::check_memory_limit_if_needed()
                    .map_err(|error| VmError::from(anyhow::Error::new(error)))
            })
            .map(Ordering::is_eq)
        };
        match *collection {
            Value::Array(ref items) => {
                for item in items.iter() {
                    if equals(item)? {
                        return Ok(true);
                    }
                }
            }
            Value::Object(ref items) => {
                for item in items.values() {
                    if equals(item)? {
                        return Ok(true);
                    }
                }
            }
            // B-tree lookup cannot interrupt its comparator. A timed scan can.
            Value::Set(ref items) => {
                for item in items.iter_sorted() {
                    if equals(item)? {
                        return Ok(true);
                    }
                }
            }
            _ => {}
        }
        Ok(false)
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    #![allow(clippy::panic_in_result_fn)]

    use super::*;
    use alloc::collections::{BTreeMap, BTreeSet};
    use alloc::vec;
    use core::convert::Infallible;

    #[test]
    fn checked_comparison_preserves_native_semantics() -> anyhow::Result<()> {
        let mut values = vec![
            Value::Null,
            Value::Undefined,
            Value::Bool(false),
            Value::Bool(true),
            Value::from(-1),
            Value::from(0),
            Value::from(1.0_f64),
            Value::from(f64::NAN),
            Value::from(f64::INFINITY),
            Value::from_json_str("1234567890123456789012345678901234567890")?,
            Value::from(""),
            Value::from("alpha"),
            Value::new_array(),
            Value::from(vec![Value::Null]),
            Value::from(vec![Value::Null, Value::Bool(true)]),
            Value::new_set(),
            Value::from(BTreeSet::from([Value::Null])),
            Value::new_object(),
            Value::from(BTreeMap::from([(
                Value::from(vec![Value::Null]),
                Value::Undefined,
            )])),
        ];
        for prefix in [255, 256, 257, 513] {
            for suffix in ["", "a", "z", "\u{100}"] {
                values.push(Value::from(alloc::format!(
                    "{}{suffix}",
                    "x".repeat(prefix)
                )));
            }
        }
        let leaves = values.clone();
        for value in leaves {
            values.push(Value::from(vec![value.clone(), value.clone()]));
            values.push(Value::from(BTreeSet::from([value.clone()])));
            values.push(Value::from(BTreeMap::from([(value.clone(), value)])));
        }
        for a in &values {
            for b in &values {
                for equality in [false, true] {
                    let checked =
                        compare_checked(a, b, equality, &mut || Ok::<(), Infallible>(()))?;
                    if equality {
                        assert_eq!(checked.is_eq(), a == b);
                    } else {
                        assert_eq!(checked, a.cmp(b));
                    }
                }
            }
        }
        Ok(())
    }

    #[test]
    fn checked_comparison_interrupts_and_shortcuts() {
        for equality in [false, true] {
            for (a, b) in [
                (
                    Value::from(vec![Value::Null; 128]),
                    Value::from(vec![Value::Null; 128]),
                ),
                (Value::from("x".repeat(4096)), Value::from("x".repeat(4096))),
            ] {
                let mut count = 0;
                let result = compare_checked(&a, &b, equality, &mut || {
                    count += 1;
                    if count == 4 {
                        Err("deadline")
                    } else {
                        Ok(())
                    }
                });
                assert_eq!(result, Err("deadline"));
                assert_eq!(count, 4);
            }
        }
        for a in [
            Value::from(vec![Value::Null; 128]),
            Value::from(BTreeSet::from([Value::Null])),
            Value::from(BTreeMap::from([(Value::Null, Value::Null)])),
            Value::from("x".repeat(4096)),
        ] {
            let alias = a.clone();
            let mut count = 0;
            assert_eq!(
                compare_checked(&a, &alias, true, &mut || {
                    count += 1;
                    Ok::<(), Infallible>(())
                }),
                Ok(Ordering::Equal)
            );
            assert_eq!(count, 1);
        }
    }
}
