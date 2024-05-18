#ifndef REGORUS_H
#define REGORUS_H

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

/**
 * Status of a call on `RegorusEngine`.
 */
typedef enum RegorusStatus {
  /**
   * The operation was successful.
   */
  RegorusStatusOk,
  /**
   * The operation was unsuccessful.
   */
  RegorusStatusError,
} RegorusStatus;

/**
 * Wrapper for `regorus::Engine`.
 */
typedef struct RegorusEngine RegorusEngine;

/**
 * Result of a call on `RegorusEngine`.
 *
 * Must be freed using `regorus_result_drop`.
 */
typedef struct RegorusResult {
  /**
   * Status
   */
  enum RegorusStatus status;
  /**
   * Output produced by the call.
   * Owned by Rust.
   */
  char *output;
  /**
   * Errors produced by the call.
   * Owned by Rust.
   */
  char *error_message;
} RegorusResult;

/**
 * Drop a `RegorusResult`.
 *
 * `output` and `error_message` strings are not valid after drop.
 */
void regorus_result_drop(struct RegorusResult r);

/**
 * Construct a new Engine
 *
 * See https://docs.rs/regorus/latest/regorus/struct.Engine.html
 */
struct RegorusEngine *regorus_engine_new(void);

/**
 * Clone a [`RegorusEngine`]
 *
 * To avoid having to parse same policy again, the engine can be cloned
 * after policies and data have been added.
 */
struct RegorusEngine *regorus_engine_clone(struct RegorusEngine *engine);

void regorus_engine_drop(struct RegorusEngine *engine);

/**
 * Add a policy
 *
 * The policy is parsed into AST.
 * See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_policy
 *
 * * `path`: A filename to be associated with the policy.
 * * `rego`: Rego policy.
 */
struct RegorusResult regorus_engine_add_policy(struct RegorusEngine *engine,
                                               const char *path,
                                               const char *rego);

struct RegorusResult regorus_engine_add_policy_from_file(struct RegorusEngine *engine,
                                                         const char *path);

/**
 * Add policy data.
 *
 * See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_data
 * * `data`: JSON encoded value to be used as policy data.
 */
struct RegorusResult regorus_engine_add_data_json(struct RegorusEngine *engine, const char *data);

struct RegorusResult regorus_engine_add_data_from_json_file(struct RegorusEngine *engine,
                                                            const char *path);

/**
 * Clear policy data.
 *
 * See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.clear_data
 */
struct RegorusResult regorus_engine_clear_data(struct RegorusEngine *engine);

/**
 * Set input.
 *
 * See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.set_input
 * * `input`: JSON encoded value to be used as input to query.
 */
struct RegorusResult regorus_engine_set_input_json(struct RegorusEngine *engine, const char *input);

struct RegorusResult regorus_engine_set_input_from_json_file(struct RegorusEngine *engine,
                                                             const char *path);

/**
 * Evaluate query.
 *
 * See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.eval_query
 * * `query`: Rego expression to be evaluate.
 */
struct RegorusResult regorus_engine_eval_query(struct RegorusEngine *engine, const char *query);

extern uint8_t *regorus_aligned_alloc(uintptr_t alignment, uintptr_t size);

extern void regorus_free(uint8_t *ptr);

#endif /* REGORUS_H */
