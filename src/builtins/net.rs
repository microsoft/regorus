#![allow(
    clippy::panic,
    clippy::expect_used,
    clippy::needless_continue,
    clippy::unused_trait_names
)] // net builtins panic/expect in invariant checks

use core::net::IpAddr;
use ipnet::IpNet;
use std::format;
use std::string::ToString;
use std::sync::Arc;
use std::vec::Vec;

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{enforce_limit, ensure_args_count};
use crate::lexer::Span;
use crate::value::Value;

use anyhow::{anyhow, bail, Result};

use super::utils::ensure_string;

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("net.cidr_is_valid", (cidr_is_valid, 1));
    m.insert("net.cidr_contains", (cidr_contains, 2));
    m.insert("net.cidr_expand", (cidr_expand, 1));
}

/// Checks if a CIDR string is valid or invalid. Uses the
/// `net::IpAddr` type to determine if the string is a valid IP,
/// and checks to ensure that the mask is in bounds for the parsed
/// IP address type (v4 or v6).
pub fn cidr_is_valid(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    ensure_args_count(span, "cidr_is_valid", params, args, 1)?;
    let cidr = ensure_string("cidr_is_valid", &params[0], &args[0])?;

    Ok(Value::from(is_valid_cidr(cidr)))
}

fn is_valid_cidr(cidr: Arc<str>) -> bool {
    let Some((ip_addr, prefix_len)) = cidr.split_once("/") else {
        return false;
    };
    match ip_addr.parse::<IpAddr>() {
        Ok(addr) => {
            let Ok(mask) = prefix_len.parse::<i16>() else {
                return false;
            };

            match addr {
                IpAddr::V4(_) => {
                    if !(0..=32).contains(&mask) {
                        return false;
                    }
                }
                IpAddr::V6(_) => {
                    if !(0..=128).contains(&mask) {
                        return false;
                    }
                }
            }
            true
        }
        Err(_) => false,
    }
}

/// Checks if a CIDR string contains a given CIDR or individual network address.
pub fn cidr_contains(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    strict: bool,
) -> Result<Value> {
    ensure_args_count(span, "cidr_contains", params, args, 2)?;
    let cidr = ensure_string("cidr_contains", &params[0], &args[0])?;
    let cidr_or_ip = ensure_string("cidr_contains", &params[1], &args[1])?;
    let contains = _cidr_contains(cidr, cidr_or_ip);

    match contains {
        Ok(r) => Ok(Value::from(r)),
        // The rego implementation will retur an error in strict mode, see
        // https://github.com/open-policy-agent/opa/blob/main/v1/test/cases/testdata/v1/netcidrcontains/test-netcidrcontains-0100.yaml
        // as an example, so we will propagate the error if the builtin is
        // run in strict mode.
        Err(e) if strict => bail!(span.error(&format!("{e}"))),
        // If not in strict mode, an error will result in Undefined.
        _ => Ok(Value::Undefined),
    }
}

fn _cidr_contains(cidr: Arc<str>, cidr_or_ip: Arc<str>) -> Result<bool> {
    let net = cidr
        .parse::<IpNet>()
        .map_err(|e| anyhow!("Error parsing {cidr}: {e}"))?;

    if cidr_or_ip.contains("/") {
        let subnet = cidr_or_ip
            .parse::<IpNet>()
            .map_err(|e| anyhow!("Error parsing {cidr_or_ip} as CIDR: {e}"))?;

        return Ok(net.contains(&subnet));
    }

    // if the caller did not provide a CIDR string, try to parse
    // the input as an IP address.
    let subnet = cidr_or_ip
        .parse::<IpAddr>()
        .map_err(|e| anyhow!("Error parsing {cidr_or_ip} as IP address: {e}"))?;
    Ok(net.contains(&subnet))
}

pub fn cidr_expand(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    ensure_args_count(span, "cidr_expand", params, args, 1)?;
    let cidr = ensure_string("cidr_expand", &params[0], &args[0])?;

    _cidr_expand(cidr)
}

fn _cidr_expand(cidr: Arc<str>) -> Result<Value> {
    let net = cidr
        .parse::<IpNet>()
        .map_err(|e| anyhow!("Error parsing {cidr}: {e}"))?;

    let mut hosts: Vec<Value> = Vec::new();
    for host in net.hosts() {
        hosts.push(Value::String(host.to_string().into()));
        // Guard expanded host list growth while iterating over CIDR addresses.
        enforce_limit()?;
    }

    // the IpNet library has some different behavior regarding CIDR expansion from the go implementation
    // that OPA uses; it will exclude the IPv4 CIDR network address and broadcast address when the netmask < 31.
    // Adjust accordingly for parity.
    if matches!(net, IpNet::V4(_) if net.prefix_len() < 31) {
        hosts.push(Value::String(net.broadcast().to_string().into()));
        // Guard expanded host list growth when adding the broadcast address.
        enforce_limit()?;
        hosts.insert(0, Value::String(net.network().to_string().into()));
        // Guard expanded host list growth when reintroducing the network address.
        enforce_limit()?;
    }

    Ok(Value::Array(Arc::from(hosts)))
}

#[cfg(test)]
mod net_tests {
    use super::*;

    #[test]
    fn test_cidr_is_valid() {
        let valids = Vec::from(["127.0.0.1/32", "10.0.0.0/8", "0.1.2.3/32", "::1/128"]);
        let invalids = Vec::from(["256.0.0.0/8", "127.0.0.1/33", "::1/129"]);

        for cidr in valids {
            assert!(
                is_valid_cidr(Arc::from(cidr)),
                "Valid CIDR {cidr} deemed invalid"
            );
        }

        for cidr in invalids {
            assert!(
                !is_valid_cidr(Arc::from(cidr)),
                "Invalid CIDR {cidr} deemed valid"
            );
        }
    }

    #[test]
    fn test_cidr_contains() {
        let test_cases: std::vec::IntoIter<(Arc<str>, Arc<str>, bool, bool)> = Vec::from([
            // Each case is a tuple of (cidr, cidr_or_ip, expected Ok(result), and expected error)
            (
                Arc::from("127.0.0.1/32"),
                Arc::from("127.0.0.1"),
                true,
                false,
            ),
            (
                Arc::from("10.0.0.0/8"),
                Arc::from("10.10.10.10"),
                true,
                false,
            ),
            (
                Arc::from("10.0.0.0/8"),
                Arc::from("10.10.10.0/24"),
                true,
                false,
            ),
            (Arc::from("fd00::/16"), Arc::from("fd00::/17"), true, false),
            (
                Arc::from("127.0.0.1/32"),
                Arc::from("127.0.0.2"),
                false,
                false,
            ),
            (Arc::from("10.0.0.0/8"), Arc::from("11.0.0.1"), false, false),
            (Arc::from("fd00::/16"), Arc::from("fd00::/15"), false, false),
            (
                Arc::from("127.0.0.0/8"),
                Arc::from("not a cidr"),
                false,
                true,
            ),
        ])
        .into_iter();

        for (cidr, sub, result, should_err) in test_cases {
            let got = _cidr_contains(cidr.clone(), sub.clone());
            match got {
                Err(_) if should_err => continue,
                Ok(res) if res == result => continue,
                _ => {
                    panic!(
                        "Expected `cidr_contains` for cidr {cidr} and subnet {sub} to be {result}"
                    )
                }
            }
        }
    }

    #[test]
    fn test_cidr_expand() {
        let cases = Vec::from([
            ("127.0.0.1/32", Vec::from(["127.0.0.1"])),
            (
                "10.0.0.0/29",
                Vec::from([
                    "10.0.0.0", "10.0.0.1", "10.0.0.2", "10.0.0.3", "10.0.0.4", "10.0.0.5",
                    "10.0.0.6", "10.0.0.7",
                ]),
            ),
        ]);

        for (cidr, exp) in cases {
            let cidrs = _cidr_expand(cidr.into()).expect("CIDRs should be returned");
            let expv = Value::from(exp.iter().map(|s| Value::from(*s)).collect::<Vec<Value>>());
            assert_eq!(cidrs, expv);
        }
    }
}
