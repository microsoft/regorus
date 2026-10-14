extern crate cbindgen;

use std::env;

fn main() {
    let crate_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let experimental = env::var_os("CARGO_FEATURE_EXPLANATIONS").is_some();
    let (c_header, cpp_header, c_guard, cpp_guard) = if experimental {
        (
            "regorus.experimental.h",
            "regorus.experimental.ffi.hpp",
            "REGORUS_EXPERIMENTAL_H",
            "REGORUS_EXPERIMENTAL_FFI_HPP",
        )
    } else {
        (
            "regorus.h",
            "regorus.ffi.hpp",
            "REGORUS_H",
            "REGORUS_FFI_HPP",
        )
    };

    configure_builder(cbindgen::Builder::new(), experimental)
        .with_crate(&crate_dir)
        .with_language(cbindgen::Language::C)
        .with_include_guard(c_guard)
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file(c_header);

    configure_builder(cbindgen::Builder::new(), experimental)
        .with_crate(crate_dir)
        .with_language(cbindgen::Language::Cxx)
        .with_include_guard(cpp_guard)
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file(cpp_header);
}

fn configure_builder(builder: cbindgen::Builder, experimental: bool) -> cbindgen::Builder {
    let builder = builder.with_define("feature", "explanations", "REGORUS_EXPERIMENTAL");
    if experimental {
        builder.with_header("#define REGORUS_EXPERIMENTAL")
    } else {
        builder
    }
}
