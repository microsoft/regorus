# Steps to run invoke example

1. Install dotnet-script
1. `dotnet build` in `bindings/csharp/Regorus`
1. `cargo build --release` in `bindings/ffi`
1. Copy `bindings/ffi/target/debug/regorus_ffi.dll` to `bindings/csharp/scripts`
1. `cd` to `bindings/csharp/scripts`
1. Run `dotnet script invoke.csx`

All at once as a single command:
```
cd bindings/csharp/Regorus && dotnet build && cd ../../.. && cd bindings/ffi && cargo build --release --features rego-extensions,rego-builtin-extensions && cd ../.. && cp bindings/ffi/target/release/regorus_ffi.dll bindings/csharp/scripts && cd bindings/csharp/scripts && dotnet script invoke.csx && cd ../../..
```