# Building

## Build Regorus nuget package
```bash
cd bindings/csharp/Regorus
dotnet restore
dotnet build /p:Configuration=Release
dotnet pack
```

**Note** that the `build` and `pack` commands above **MUST** be run separately to ensure
that the regorus ffi shared library (libregorus.so, libregorus.dylib, regorus.dll) is included
in the nuget package.

Ensure the runtime folder has the regorus ffi shared library using `tar tf`, `unzip -l`  etc.
```
$ tar tf bin/Release/Regorus*.nupkg

_rels/.rels
Regorus.nuspec
lib/netstandard2.0/Regorus.dll
lib/netstandard2.1/Regorus.dll
README.md
runtimes/osx-arm64/native/libregorus_ffi.dylib   <-- Regorus FFI shared library.
[Content_Types].xml
package/services/metadata/core-properties/c04537f5acfc4bb98cfb43a8092d3521.psmdcp
``

# Test Regorus nuget package
```
cd bindings/csharp/TestApp
dotnet restore /p:RestoreSources=./../Regorus/bin/Release
dotnet run --framework net8.0
```