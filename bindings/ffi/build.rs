extern crate cbindgen;

use std::env;

fn main() {
    let crate_dir = env::var("CARGO_MANIFEST_DIR").unwrap();

    cbindgen::Builder::new()
        .with_crate(&crate_dir)
        .with_language(cbindgen::Language::C)
        .with_include_guard("REGORUS_H")
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file("regorus.h");

    cbindgen::Builder::new()
        .with_crate(crate_dir)
        .with_language(cbindgen::Language::Cxx)
        .with_include_guard("REGORUS_FFI_HPP")
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file("regorus.ffi.hpp");
}
