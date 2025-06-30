use std::sync::Arc;

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::ensure_args_count;
use crate::lexer::Span;
use crate::value::Value;

use anyhow::{bail, Ok, Result};

use super::utils::ensure_string;

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("net.cidr_is_valid", (cidr_is_valid, 1));
}

/// Checks if a CIDR string is valid or invalid. Based on the
/// golang standard library implementation, as that is how the
/// built-in is implemented in the Open Policy Agent rego standardt
/// lib.
/// https://github.com/golang/go/blob/master/src/net/ip.go#L550
pub fn cidr_is_valid(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    ensure_args_count(span, "cidr_is_valid", params, args, 1)?;
    let cidr = ensure_string("cidr_is_valid", &params[0], &args[0])?;
    _cidr_is_valid(cidr)
}

fn _cidr_is_valid(cidr: Arc<str>) -> Result<Value> {
    let mut pieces = cidr.split("/");
    let addr_piece = pieces.next();
    let mask_piece = pieces.next();
    // TODO(tjons): check if there are more segments here...
    let mut v4: bool = false;
    let mut v6: bool = false;
    match addr_piece {
        None => bail!("cidr not valid"),
        Some(addr) => {
            for c in addr.chars() {
                match c {
                    '.' => {
                        v4 = true;
                        break;
                    }
                    ':' => {
                        v6 = true;
                        break;
                    }
                    _ => continue,
                }
            }
        }
    };

    if v4 {
        let _retval = parse_ipv4_or_err(addr_piece.unwrap())?;
    } else if v6 {
        let _retval = parse_ipv6(addr_piece.unwrap());
    }

    let mask = mask_piece
        .expect("CIDR mask invalid")
        .parse::<i16>()
        .unwrap();
    if mask < 0 {
        bail!("subnet mask cannot be less than 0");
    }
    if v4 && mask > 32 {
        bail!("ipv4 CIDR cannot have a mask greater than 32");
    }

    if v6 && mask > 128 {
        bail!("ipv6 CIDR cannot have a mask greater than 128");
    }

    Ok(Value::Bool(true))
}

fn parse_ipv4_or_err(addr: &str) -> Result<[u32; 4]> {
    // store each octet in the array
    let mut fields: [u32; 4] = [0; 4];
    let mut cur_octet: u32 = 0;
    let mut octet_digits = 0;
    let mut pos = 0;
    let mut prev: char = '\0';

    for c in addr.chars() {
        if c.is_ascii_digit() {
            // safe to unwrap this value because we check above that it is indeed a digit
            cur_octet = cur_octet * 10 + c.to_digit(10).unwrap();
            // if this is the second character of octets 2, 3, or 4; and the
            // octet == 0, like `1.00.x.x`, the CIDR cannot be valid.
            // if this is the first character of octet 1 and it is 0,
            // this is an invalid CIDR.
            if (octet_digits == 1 || pos == 0) && cur_octet == 0 {
                bail!("IPv4 field has octet with leading zero");
            }
            octet_digits += 1;

            if cur_octet > 255 {
                bail!("IPv4 field has value >255");
            }
        } else if c == '.' {
            // the CIDR may not start with a `.`, and there may not
            // be two consecutive `.` characters.
            if octet_digits == 0 || prev == '.' {
                bail!("IPv4 field must have at least one digit");
            }

            if pos == 3 {
                bail!("IPv4 address too long");
            }
            fields[pos] = cur_octet;
            pos += 1;
            cur_octet = 0;
            octet_digits = 0;
        } else {
            bail!("unexpected character");
        }
        prev = c;
    }

    Ok(fields)
}

fn parse_ipv6(_addr: &str) -> Result<(&str, i64)> {
    bail!("not implemented yet")
}

#[cfg(test)]
mod net_tests {
    use super::*;
    use std::format;
    use std::vec::Vec;

    #[test]
    fn test_cidr_is_valid() {
        let valids = Vec::from(["127.0.0.1/32", "10.0.0.0/8"]);

        let invalids = Vec::from(["0.1.2.3/32", "256.0.0.0/8"]);

        for cidr in valids {
            assert_eq!(
                _cidr_is_valid(Arc::from(cidr)).unwrap(),
                Value::Bool(true),
                "Valid CIDR {} deemed invalid",
                cidr
            );
        }

        for cidr in invalids {
            _cidr_is_valid(Arc::from(cidr))
                .expect_err(format!("Invalid CIDR {} deemed valid", cidr).as_str());
        }
    }
}
