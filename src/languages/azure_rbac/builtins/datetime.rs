// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;
use alloc::string::ToString as _;

use super::common;
use super::evaluator::RbacBuiltinError;

#[cfg(feature = "time")]
use chrono::DateTime;

// Compare RFC3339 timestamps using the requested operator.
//
// Interesting examples:
// - left: @Request[date] = "2023-05-01T12:00:00Z",
//   right: @Environment[utcNow] = "2023-05-01T11:59:59Z",
//   op: ">" => true
// - left: @Resource[expiry] = "2024-01-01T00:00:00Z",
//   right: @Environment[utcNow] = "2024-01-01T00:00:00Z",
//   op: "==" => true
// - left: @Request[scheduled] = "2023-12-31T23:59:59-08:00",
//   right: @Environment[utcNow] = "2024-01-01T07:59:59Z",
//   op: "==" => true (same instant, different offsets)
pub(super) fn datetime_compare(
    left: &Value,
    right: &Value,
    op: &str,
    name: &'static str,
) -> Result<bool, RbacBuiltinError> {
    // Parse both operands as RFC3339 strings.
    let lhs = common::value_as_string(left, name)?;
    let rhs = common::value_as_string(right, name)?;

    #[cfg(feature = "time")]
    {
        // Compare instants using chrono's RFC3339 parsing.
        let left_dt = DateTime::parse_from_rfc3339(&lhs)
            .map_err(|err| RbacBuiltinError::new(err.to_string()))?;
        let right_dt = DateTime::parse_from_rfc3339(&rhs)
            .map_err(|err| RbacBuiltinError::new(err.to_string()))?;
        Ok(match op {
            "==" => left_dt == right_dt,
            "<" => left_dt < right_dt,
            "<=" => left_dt <= right_dt,
            ">" => left_dt > right_dt,
            ">=" => left_dt >= right_dt,
            _ => false,
        })
    }

    #[cfg(not(feature = "time"))]
    {
        // Without the time feature, compare lexicographically as strings.
        Ok(match op {
            "==" => lhs == rhs,
            "<" => lhs < rhs,
            "<=" => lhs <= rhs,
            ">" => lhs > rhs,
            ">=" => lhs >= rhs,
            _ => false,
        })
    }
}
