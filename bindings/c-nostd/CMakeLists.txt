# Copyright (c) Microsoft
# Licensed under the MIT License.

cmake_minimum_required(VERSION 3.12 FATAL_ERROR)
include(FetchContent)

FetchContent_Declare(
    Corrosion
    GIT_REPOSITORY https://github.com/corrosion-rs/corrosion.git
    GIT_TAG v0.4 # Optionally specify a commit hash, version tag or branch here
)
FetchContent_MakeAvailable(Corrosion)

project("regorus-test")

corrosion_import_crate(
  # Path to <regorus-source-folder>/bindings/ffi/Cargo.toml
  MANIFEST_PATH "../ffi/Cargo.toml"
  # Always build regorus in Release mode.
  PROFILE "release"
  # Only build the "regorus-ffi" crate.
  CRATES "regorus-ffi"
  
  # Turn off std support in regorus-ffi.
  NO_DEFAULT_FEATURES
  NO_STD

  # custom_allocator allows using a custom memory allocator.
  # To use malloc/free remove custom_allocator below.
  # Additionally, select specific features in regorus.
  # See regorus/opa_no_std
  FEATURES "custom_allocator,regorus/semver"

  # Link statically
  CRATE_TYPES staticlib FLAGS --crate-type=staticlib
  )

add_executable(regorus_test main.c)
# Add path to <regorus-source-folder>/bindings/ffi
target_include_directories(regorus_test PRIVATE "../ffi")
target_link_libraries(regorus_test regorus-ffi)
