# Copyright (c) Microsoft
# Licensed under the MIT License.

cmake_minimum_required(VERSION 3.12 FATAL_ERROR)
include(FetchContent)

FetchContent_Declare(
    Corrosion
    GIT_REPOSITORY https://github.com/corrosion-rs/corrosion.git
    # Use a tag that has a fix for https://github.com/corrosion-rs/corrosion/issues/590
    GIT_TAG 6be991bb34c348dfb8344be22f3606288ea5c7fd
)
FetchContent_MakeAvailable(Corrosion)

project("regorus-test")
enable_testing()

corrosion_import_crate(
  # Path to <regorus-source-folder>/bindings/ffi/Cargo.toml
  MANIFEST_PATH "../ffi/Cargo.toml"
  # Always build regorus in Release mode.
  PROFILE "release"
  # Only build the "regorus-ffi" crate.
  CRATES "regorus-ffi"

  # Select specific features in regorus.
  FEATURES "regorus/semver"

  LOCKED
  
  # Link statically
  CRATE_TYPES "cdylib"
  )

add_executable(regorus_test main.c)
# Add path to <regorus-source-folder>/bindings/ffi
target_include_directories(regorus_test PRIVATE "../ffi")
target_link_libraries(regorus_test regorus_ffi)

add_executable(regorus_rvm_test rvm_tests.c)
target_include_directories(regorus_rvm_test PRIVATE "../ffi")
target_link_libraries(regorus_rvm_test regorus_ffi)

add_test(NAME regorus_c_engine COMMAND regorus_test)
add_test(NAME regorus_c_rvm COMMAND regorus_rvm_test)
