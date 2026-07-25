use std::format;
use std::string::String;

use vstd::prelude::*;

verus! {

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

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExAnyhowError(anyhow::Error);

pub assume_specification<M: core::fmt::Display + core::fmt::Debug + Send + Sync + 'static>[
    anyhow::Error::msg::<M>
](message: M) -> (error: anyhow::Error);

// The `anyhow!` macro expands to `must_use(format_err(format_args!(..)))`, so
// each of those pieces needs a specification. None of them promises anything
// about the resulting error, which is all the callers rely on.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFormatArguments<'a>(core::fmt::Arguments<'a>);

pub assume_specification<'a>[
    core::fmt::Arguments::<'a>::from_str
](message: &'static str) -> (args: core::fmt::Arguments<'a>);

pub assume_specification<'a>[
    anyhow::__private::format_err
](args: core::fmt::Arguments<'a>) -> (error: anyhow::Error);

pub assume_specification[
    anyhow::__private::must_use
](error: anyhow::Error) -> (result: anyhow::Error);

} // end verus!
