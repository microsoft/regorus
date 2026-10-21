// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.
#![no_std]
#![forbid(unsafe_code)]
#![allow(dead_code)]
extern crate alloc;

#[path = "../../../../../src/builtins/history/error.rs"]
mod error;
#[path = "../../../../../src/builtins/history/kernel.rs"]
mod kernel;
#[path = "../../../../../src/utils/limits/error.rs"]
mod limit_error;
#[path = "../../../../../src/builtins/history/normalize.rs"]
mod normalize;
#[path = "../../../../../src/builtins/history/symbolic.rs"]
mod symbolic;
mod utils {
    pub(crate) mod limits {
        pub(crate) use crate::limit_error::LimitError;
    }
}
mod work {
    pub(crate) type WorkVec<T> = alloc::vec::Vec<T>;
}
mod smoke;
mod store;

#[cfg(test)]
mod tests {
    #[test]
    fn production_kernel_smoke() {
        assert!(matches!(crate::smoke::extraction_smoke(), Ok(true)));
    }
}
