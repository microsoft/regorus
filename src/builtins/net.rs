use std::sync::Arc;

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::lexer::Span;
use crate::builtins::utils::ensure_args_count;
use crate::value::Value;

use anyhow::{bail, Ok, Result};

use super::utils::ensure_string;

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("net.cidr_is_valid", (cidr_is_valid, 1));
}

pub fn cidr_is_valid(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    ensure_args_count(span, "cidr_is_valid", params, args, 1)?;
    let cidr = ensure_string("cidr_is_valid", &params[0], &args[0])?;
    _cidr_is_valid(cidr)
}

fn _cidr_is_valid(cidr: Arc<str>) -> Result<Value> {
    let mut pieces= cidr.split("/");
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
                    },
                    ':' => {
                        v6 = true;
                        break;
                    },
                    _ => continue,
                }
            }
        }
    };

    if v4 {
        let retval = parse_ipv4(addr_piece.unwrap())?;
    } else if v6 {
       let retval = parse_ipv6(addr_piece.unwrap());
    }

    match mask_piece {
        None => bail!("cidr not valid"),
        _ => (),
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
        if c >= '0' && c <= '9' {
            if octet_digits == 1 && cur_octet == 0 {
                bail!("IPv4 field has octet with leading zero");
            }
            // safe to unwrap this value because we check above that it is indeed a digit
            cur_octet = cur_octet * 10 + c.to_digit(10).unwrap();
            octet_digits += 1;

            if cur_octet > 255 {
                bail!("IPv4 field has value >255");
            }
        } else if c == '.' {
            if pos == 0 || prev == '.' {
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

fn parse_ipv6(addr: &str) -> Result<(&str, i64)> {
    bail!("not implemented yet")
}

#[cfg(test)]
mod net_tests {
    use super::*;

    #[test]
    fn test_cidr_is_valid() {
        let valids = Vec::from([
            "127.0.0.1/32",
            "10.0.0.0/8",
        ]);

        let invalids = Vec::from([
            "0.1.2.3/32",
            "256.0.0.0/8",
        ]);

        for cidr in valids {
            _cidr_is_valid(Arc::from(cidr)).expect("Valid CIDR returned invalid");
        }

        for cidr in invalids {
            _cidr_is_valid(Arc::from(cidr)).expect_err("Invalid CIDR returned valid");
        }
    }
}
