use anyhow::{bail, Result};
use std::format;
use std::string::String;

use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
#[verifier::external_body]
pub fn verus_format_helper() -> String
{
    format!("who cares")
}

macro_rules! verus_format {
    ( $( $tt0:tt )* ) => {
        {
            #[cfg(not(verus_keep_ghost))]
            { format!($($tt0)*) }
            #[cfg(verus_keep_ghost)]
            { verus_format_helper() }
        }
    }
}

#[allow(dead_code)]
fn my_test_verus_format(fcn: &'static str, x: u32) -> String
{
    verus_format!("The parameters are `{fcn}` and `{x}`")
}

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAnyhowError(anyhow::Error);

#[cfg(verus_keep_ghost)]
#[verifier::external_body]
pub fn verus_bail_helper<T>() -> Result<T>
{
    bail!("who cares")
}

macro_rules! verus_bail {
    ( $( $tt0:tt )* ) => {
        {
            #[cfg(not(verus_keep_ghost))]
            { bail!($($tt0)*) }
            #[cfg(verus_keep_ghost)]
            { return verus_bail_helper(); }
        }
    }
}

#[allow(dead_code)]
fn my_test_verus_bail(fcn: &'static str, x: u32) -> Result<()>
{
    if x > 0 {
        verus_bail!("Invalid parameters `{}` and `{}`", fcn, x)
    }
    Ok(())
}

} // end verus!
