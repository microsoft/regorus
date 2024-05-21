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
set(CMAKE_CXX_STANDARD 17)

corrosion_import_crate(
  # Path to <regorus-source-folder>/bindings/ffi/Cargo.toml
  MANIFEST_PATH "../ffi/Cargo.toml"
  # Always build regorus in Release mode.
  PROFILE "release"
  # Only build the "regorus-ffi" crate.
  CRATES "regorus-ffi"

  # Select specific features in regorus.
  FEATURES "regorus/semver"

  # Link statically
  CRATE_TYPES "staticlib")

add_executable(regorus_test main.cpp)
# Add path to <regorus-source-folder>/bindings/ffi
target_include_directories(regorus_test PRIVATE "../ffi")
target_link_libraries(regorus_test regorus-ffi)
