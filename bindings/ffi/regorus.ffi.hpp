#ifndef REGORUS_FFI_HPP
#define REGORUS_FFI_HPP

#include <cstdarg>
#include <cstdint>
#include <cstdlib>
#include <ostream>
#include <new>

/// Status of a call on `RegorusEngine`.
enum class RegorusStatus {
  /// The operation was successful.
  RegorusStatusOk,
  /// The operation was unsuccessful.
  RegorusStatusError,
};

/// Wrapper for `regorus::Engine`.
struct RegorusEngine;

/// Result of a call on `RegorusEngine`.
///
/// Must be freed using `regorus_result_drop`.
struct RegorusResult {
  /// Status
  RegorusStatus status;
  /// Output produced by the call.
  /// Owned by Rust.
  char *output;
  /// Errors produced by the call.
  /// Owned by Rust.
  char *error_message;
};

extern "C" {

/// Drop a `RegorusResult`.
///
/// `output` and `error_message` strings are not valid after drop.
void regorus_result_drop(RegorusResult r);

/// Construct a new Engine
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html
RegorusEngine *regorus_engine_new();

/// Clone a [`RegorusEngine`]
///
/// To avoid having to parse same policy again, the engine can be cloned
/// after policies and data have been added.
RegorusEngine *regorus_engine_clone(RegorusEngine *engine);

void regorus_engine_drop(RegorusEngine *engine);

/// Add a policy
///
/// The policy is parsed into AST.
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_policy
///
/// * `path`: A filename to be associated with the policy.
/// * `rego`: Rego policy.
RegorusResult regorus_engine_add_policy(RegorusEngine *engine, const char *path, const char *rego);

RegorusResult regorus_engine_add_policy_from_file(RegorusEngine *engine, const char *path);

/// Add policy data.
///
/// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_data
/// * `data`: JSON encoded value to be used as policy data.
RegorusResult regorus_engine_add_data_json(RegorusEngine *engine, const char *data);

RegorusResult regorus_engine_add_data_from_json_file(RegorusEngine *engine, const char *path);

/// Clear policy data.
///
/// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.clear_data
RegorusResult regorus_engine_clear_data(RegorusEngine *engine);

/// Set input.
///
/// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.set_input
/// * `input`: JSON encoded value to be used as input to query.
RegorusResult regorus_engine_set_input_json(RegorusEngine *engine, const char *input);

RegorusResult regorus_engine_set_input_from_json_file(RegorusEngine *engine, const char *path);

/// Evaluate query.
///
/// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.eval_query
/// * `query`: Rego expression to be evaluate.
RegorusResult regorus_engine_eval_query(RegorusEngine *engine, const char *query);

extern uint8_t *regorus_aligned_alloc(uintptr_t alignment, uintptr_t size);

extern void regorus_free(uint8_t *ptr);

} // extern "C"

#endif // REGORUS_FFI_HPP
