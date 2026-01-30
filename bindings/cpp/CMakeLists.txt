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
set(CMAKE_CXX_STANDARD 17)
enable_testing()

# installable ffi target

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
  CRATE_TYPES "cdylib")

include(GNUInstallDirs)

set(regorus_ffi_INCLUDEDIR ${CMAKE_INSTALL_INCLUDEDIR}/regorus_ffi)
set(regorus_ffi_CONFIGDIR ${CMAKE_INSTALL_LIBDIR}/cmake/regorus_ffi)
set(regorus_ffi_LIBDIR ${CMAKE_INSTALL_LIBDIR})
set(regorus_ffi_BINDIR ${CMAKE_INSTALL_BINDIR})

add_library(regorus_ffi::regorus_ffi ALIAS regorus_ffi)
corrosion_install(TARGETS regorus_ffi EXPORT regorus_ffi_targets LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR})

target_include_directories(regorus_ffi
INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../ffi>
    $<INSTALL_INTERFACE:${regorus_ffi_INCLUDEDIR}>
)

set(regorus_ffi_HEADER_FILES
  regorus.hpp
  ../ffi/regorus.ffi.hpp
)

install(FILES ${regorus_ffi_HEADER_FILES}
  DESTINATION ${regorus_ffi_INCLUDEDIR}
  COMPONENT Devel
)

install(EXPORT regorus_ffi_targets
  FILE regorus_ffi_targets.cmake
  NAMESPACE regorus_ffi::
  DESTINATION ${regorus_ffi_CONFIGDIR}
)

include(CMakePackageConfigHelpers)

configure_package_config_file(${CMAKE_CURRENT_LIST_DIR}/regorus_ffiConfig.cmake.in
  ${CMAKE_CURRENT_BINARY_DIR}/regorus_ffiConfig.cmake
  INSTALL_DESTINATION ${regorus_ffi_CONFIGDIR}
)

install(FILES
  ${CMAKE_CURRENT_BINARY_DIR}/regorus_ffiConfig.cmake
  ${CMAKE_CURRENT_BINARY_DIR}/corrosion/regorus_ffi_targetsCorrosion.cmake
  DESTINATION ${regorus_ffi_CONFIGDIR}
)

# test binary

add_executable(regorus_test main.cpp)
target_link_libraries(regorus_test regorus_ffi::regorus_ffi)

add_executable(regorus_rvm_test rvm_tests.cpp)
target_link_libraries(regorus_rvm_test regorus_ffi::regorus_ffi)

add_test(NAME regorus_cpp_engine COMMAND regorus_test)
add_test(NAME regorus_cpp_rvm COMMAND regorus_rvm_test)
