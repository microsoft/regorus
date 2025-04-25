# Steps to run invoke example

1. Install dotnet-script
1. `dotnet build` in `bindings/csharp/Regorus`
1. `cargo build` in `bindings/ffi`
1. Copy `bindings/ffi/target/debug/regorus_ffi.dll` to `bindings/csharp/scripts`
1. `cd` to `bindings/csharp/scripts`
1. Run `dotnet script invoke.csx`
