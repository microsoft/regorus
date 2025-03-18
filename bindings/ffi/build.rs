extern crate cbindgen;
extern crate csbindgen;

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

    csbindgen::Builder::default()
        .input_extern_file("src/lib.rs")
        .csharp_dll_name("regorus_ffi")
        .csharp_class_name("API")
        .csharp_namespace("Regorus.Internal")
        .generate_csharp_file("./RegorusFFI.g.cs")
        .unwrap();
}
