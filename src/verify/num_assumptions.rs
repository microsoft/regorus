// This file contains assumptions about Rust's primitive numeric types,
// encoded in Verus.
//
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use vstd::prelude::*;

verus! {

use vstd::arithmetic::power::pow;

pub assume_specification[ i128::abs ](value: i128) -> (res: i128)
    requires
        value != i128::MIN,
    ensures
        res as int == if value < 0 { -(value as int) } else { value as int },
;

pub assume_specification[ i64::checked_abs ](value: i64) -> (res: Option<i64>)
    ensures
        if value == i64::MIN {
            res is None
        } else {
            res matches Some(abs) && abs as int == if value < 0 { -(value as int) } else { value as int }
        },
;

pub assume_specification[ u64::checked_pow ](x: u64, exp: u32) -> (res: Option<u64>)
    ensures
        match res {
            Some(value) => value == pow(x as int, exp as nat),
            None => pow(x as int, exp as nat) > u64::MAX,
        },
;

} // end verus!
