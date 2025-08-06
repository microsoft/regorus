use core::net::IpAddr;
use std::sync::Arc;

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::ensure_args_count;
use crate::lexer::Span;
use crate::value::Value;

use anyhow::Result;

use super::utils::ensure_string;

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("net.cidr_is_valid", (cidr_is_valid, 1));
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

#[cfg(test)]
mod net_tests {
    use super::*;
    use std::vec::Vec;

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
}
