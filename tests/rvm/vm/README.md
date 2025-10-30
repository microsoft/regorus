# Regorus VM Test Suites

This directory hosts YAML-driven regression suites for the Regorus virtual machine. Each YAML file is converted into parameterised Rust tests by `src/rvm/tests/vm.rs`, so the contents here define the end-to-end VM coverage.

## Prerequisites

- Enable the `rvm` feature (it pulls in `std` and the VM runtime) whenever you run these tests:
  - `cargo test --features rvm run_vm_test_file`
  - `cargo test --features rvm run_loop_test_file`
- Append `-- --nocapture` to surface per-test diagnostics when a failure occurs.
- Individual generated tests follow the pattern `run_vm_test_file_tests_rvm_vm_suites_<suite>_yaml`, so you can use that fragment with `cargo test` to run a single suite.

## Layout

- `suites/*.yaml` — primary instruction, control-flow, and integration suites.
- `suites/loops/*.yaml` — dedicated loop/comprehension suites.
- Mirror the comment headers inside each suite when adding new files; the descriptions are surfaced in this README for quick reference.

## Main Suites (`suites/*.yaml`)

| Suite | Focus |
| --- | --- |
| `arithmetic_operations.yaml` | Arithmetic opcodes (`Add`, `Sub`, `Mul`, `Div`, `Mod`) and simple expressions. |
| `assertions.yaml` | `AssertCondition` semantics, including success/failure and loop control interactions. |
| `basic_instructions.yaml` | Core load/move/return instructions that underpin every program. |
| `boolean_literals.yaml` | `LoadBool`, `LoadTrue`, `LoadFalse`, and their interaction with logical operators. |
| `builtin_functions.yaml` | Builtin dispatch covering argument marshalling, return handling, and error cases. |
| `call_rule.yaml` | `CallRule` execution, rule caches, defaults, and fallbacks. |
| `comparison_operations.yaml` | Relational operators plus logical combining (`Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`, `And`, `Or`, `Not`). |
| `complex.yaml` | Deeply nested hybrid loops, comprehensions, and rule calls that stress the scheduler. |
| `constructed_collections.yaml` | `ArrayCreate`/`SetCreate` success paths, undefined propagation, and deduplication. |
| `control_flow.yaml` | Conditional branching patterns, nested assertions, and selection logic. |
| `core_semantics.yaml` | Broad regression coverage for arithmetic, comparisons, loops, assertions, and collection helpers. |
| `data_structures.yaml` | Array/object/set creation, access, and mutation instructions. |
| `deep_nesting.yaml` | Three-plus levels of mixed loop modes validating register pressure and control flow correctness. |
| `default_rules.yaml` | Complete rule execution with default literals and failure fallbacks. |
| `destructuring_rules.yaml` | Destructuring metadata handling, success/early-exit semantics. |
| `function_calls.yaml` | User function invocation plumbing, argument passing, and returns. |
| `halt.yaml` | `Halt` instruction returning register `0` and stopping execution. |
| `host_await.yaml` | Successful `HostAwait` responses across execution modes and run-to-completion flows. |
| `host_await_failures.yaml` | Error signalling and ignore-flag behaviour for `HostAwait`. |
| `indexed_access.yaml` | Literal/register indexing, chained accesses, and undefined propagation. |
| `integration_scenarios.yaml` | Real-world policy shapes (RBAC, filtering, transforms, workflows). |
| `interpreter_operator_compatibility.yaml` | Ensures VM operators match interpreter behaviour on edge cases. |
| `invalid_collection_ops.yaml` | Error paths for object/set/array mutations with incorrect types. |
| `load_data_input.yaml` | `LoadData` and `LoadInput` instructions across nested/empty/undefined sources. |
| `loop_invalid_iteration.yaml` | Loop errors for non-iterables plus instruction-limit enforcement. |
| `null_undefined_handling.yaml` | Null/undefined behaviour across arithmetic, comparisons, indexing, loops, and comprehensions. |
| `object_operations.yaml` | Advanced object templates, dynamic keys, collisions, and validation. |
| `predefined.yaml` | Global `data` and `input` bindings, including nested access patterns. |
| `resource_limits.yaml` | Instruction counts, recursion depth, and other resource exhaustion scenarios. |
| `serialization.yaml` | Round-trip binary serialization for compiled programs covering all instruction families. |
| `set_operations.yaml` | Set creation, deduplication, membership checks, and nested values. |
| `type_errors.yaml` | Graceful error reporting for cross-family type mismatches. |
| `virtual_data_lookup.yaml` | `VirtualDataDocumentLookup` with base data, rule overrides, and invalid indices. |

## Loop Suites (`suites/loops/*.yaml`)

| Suite | Focus |
| --- | --- |
| `array_comprehensions.yaml` | Mapping, filtering, and edge cases for array comprehensions. |
| `empty.yaml` | Behaviour of every loop mode over empty collections (vacuous truth/falsehood). |
| `existential.yaml` | `some`-style (`Any`) quantification including early exits and complex predicates. |
| `loop_comprehension_interactions.yaml` | Interplay between nested loops and comprehensions emitting structured data. |
| `nested.yaml` | Mixed nesting patterns for loops and comprehensions with varying depth. |
| `nested_fixed.yaml` | Placeholder for future fixed-nesting scenarios (no cases yet). |
| `object_comprehensions.yaml` | Key/value emission, collision handling, and filtering in object comprehensions. |
| `set_comprehensions.yaml` | Deduplication and uniqueness guarantees in set comprehensions. |
| `universal.yaml` | `every`-style (`Every`) quantification, early failure, and vacuous truth cases. |

## Adding or Updating Suites

1. Place the new YAML file under `suites/` (or the relevant `suites/loops/` subdirectory).
2. Add a concise comment block at the top describing the intent and scenarios.
3. Update the tables above so the catalog stays accurate.
4. Run `cargo test --features rvm run_vm_test_file` to ensure the suite loads and all cases pass.

Keeping this README current makes it easier to discover coverage gaps and reason about the generated tests.
