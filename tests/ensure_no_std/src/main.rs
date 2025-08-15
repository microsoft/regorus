// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![no_std]
#![no_main]

#[cfg(not(test))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    loop {}
}
