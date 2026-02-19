// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;
use alloc::string::ToString as _;

use super::common;
use super::evaluator::RbacBuiltinError;

#[cfg(feature = "net")]
use core::net::IpAddr;
#[cfg(feature = "net")]
use ipnet::IpNet;

// Match an IP address against a CIDR range.
// Examples:
// - IpMatch("10.0.0.5", "10.0.0.0/24") => true
// - IpMatch("10.0.1.5", "10.0.0.0/24") => false
// - IpMatch("2001:db8::1", "2001:db8::/32") => true
pub(super) fn ip_match(
    left: &Value,
    right: &Value,
    name: &'static str,
) -> Result<bool, RbacBuiltinError> {
    // Parse inputs as strings before network matching.
    let ip_str = common::value_as_string(left, name)?;
    let cidr_str = common::value_as_string(right, name)?;

    #[cfg(feature = "net")]
    {
        // Parse CIDR and IP and check containment.
        let net = cidr_str
            .parse::<IpNet>()
            .map_err(|err| RbacBuiltinError::new(err.to_string()))?;
        let ip = ip_str
            .parse::<IpAddr>()
            .map_err(|err| RbacBuiltinError::new(err.to_string()))?;
        Ok(net.contains(&ip))
    }

    #[cfg(not(feature = "net"))]
    {
        Err(RbacBuiltinError::new("IP builtins have not been enabled"))
    }
}

// Match an IP against a range or a CIDR block.
// - If the right operand is a 2-element list, it is treated as [start, end].
// - Otherwise, it is treated as a CIDR string.
// Examples:
// - IpInRange("10.0.0.5", ["10.0.0.1", "10.0.0.10"]) => true
// - IpInRange("10.0.0.5", ["10.0.0.6", "10.0.0.10"]) => false
// - IpInRange("10.0.0.5", "10.0.0.0/24") => true
pub(super) fn ip_in_range(
    left: &Value,
    right: &Value,
    name: &'static str,
) -> Result<bool, RbacBuiltinError> {
    match *right {
        Value::Array(ref list) if list.len() == 2 => {
            // Treat list as inclusive [start, end] bounds.
            let start = list
                .first()
                .ok_or_else(|| RbacBuiltinError::new("IpInRange expects 2 values"))?;
            let end = list
                .get(1)
                .ok_or_else(|| RbacBuiltinError::new("IpInRange expects 2 values"))?;
            let start = common::value_as_string(start, name)?;
            let end = common::value_as_string(end, name)?;
            ip_between(left, &start, &end, name)
        }
        _ => ip_match(left, right, name),
    }
}

// Check inclusive range membership: start <= ip <= end.
// Example: IpInRange("10.0.0.5", ["10.0.0.1", "10.0.0.10"]) => true
fn ip_between(
    left: &Value,
    start: &str,
    end: &str,
    name: &'static str,
) -> Result<bool, RbacBuiltinError> {
    // Parse the target IP once for range checks.
    let ip_str = common::value_as_string(left, name)?;

    #[cfg(feature = "net")]
    {
        // Compare parsed IP values with inclusive bounds.
        let ip = ip_str
            .parse::<IpAddr>()
            .map_err(|err| RbacBuiltinError::new(err.to_string()))?;
        let start_ip = start
            .parse::<IpAddr>()
            .map_err(|err| RbacBuiltinError::new(err.to_string()))?;
        let end_ip = end
            .parse::<IpAddr>()
            .map_err(|err| RbacBuiltinError::new(err.to_string()))?;
        Ok(start_ip <= ip && ip <= end_ip)
    }

    #[cfg(not(feature = "net"))]
    {
        Err(RbacBuiltinError::new("IP builtins have not been enabled"))
    }
}
