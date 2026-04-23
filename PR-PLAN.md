# Azure Policy Compiler — PR Submission Plan

Main is the source of truth for RVM, aliases, parser, builtins, RBAC, bindings,
engine, etc. Only compiler/ code and its tests remain to be submitted.

## Completed

- **PR #686** (`azure-policy-compiler-eval` → `microsoft:main`): 2 commits
  - Commit 1 (`68d935f`): Compiler skeleton with core types and stubs
  - Commit 2 (`c17a438`): Condition, expression, field, and template dispatch compilation
  - Status: Draft, Copilot review clean (0 new comments on latest push)
  - Files: 14 new files in compiler/, +2,557 lines vs main

- **PR #688** (Count support): 1 squashed commit on `azure-policy-compiler-count`
  - Full count loop compilation replacing stubs
  - Status: In review, Copilot comments addressed

## Total remaining (compiler only): 7 files, +4,330 lines vs main

After PR #686: +2,984/-1,211 lines across 14 compiler files (restructuring)

Final state on `azure-policy-compiler`:
- mod.rs (1,681 LOC) — main pipeline, effects, metadata, emit helpers, aliases
- count.rs (912 LOC) — count loops, count-as-any, bindings
- conditions.rs — condition compilation + wildcard allOf
- fields.rs (385 LOC) — field path compilation
- template_dispatch.rs (369 LOC) — ARM function dispatch
- expressions.rs (337 LOC) — expression & JSON value compilation
- utils.rs (143 LOC) — shared helpers
- (stubs from PR #686 deleted: core.rs, conditions_wildcard.rs, metadata.rs,
  effects.rs, effects_modify_append.rs, count_any.rs, count_bindings.rs)

---

## PR 4: Effects + Metadata + File Restructure

### Goal
Complete the compiler by implementing effects, metadata, and consolidating files
(core.rs → mod.rs, conditions_wildcard.rs → conditions.rs, etc.).

### Phase A: Implement effects (in effects.rs or mod.rs)

#### Step 1: Implement compile_effect()
Replace the bail stub with full effect dispatch:
- Resolve effect kind via `resolve_effect_kind()` (handles parameterized `[parameters('effect')]`)
- Match on EffectKind: Deny, Audit, Disabled, Append, Modify, AuditIfNotExists, DeployIfNotExists, DenyAction, AddToNetworkGroup
- Simple effects (Deny, Audit, Disabled): load effect name literal, wrap via `wrap_effect_result()`
- Detail effects (Modify, Append): call `compile_effect_with_details()` → routes to `compile_modify_details()` or `compile_append_details()`
- Cross-resource effects (AINE, DINE): call `compile_cross_resource_effect()` which emits `HostAwait` instruction

#### Step 2: Implement wrap_effect_result()
Replace bail stub:
- Build structured result object `{ "effect": <name_reg>, "details": <details_reg> }`
- Uses `Instruction::ObjectNew`, `Instruction::ObjectInsert` sequences
- When details_reg is None, omit the details field

#### Step 3: Implement Modify/Append details
In effects_modify_append.rs (or same file depending on restructure):
- `compile_modify_details()` — iterates `details.operations` array, compiles each modify operation
- `compile_modify_operation()` — handles addOrReplace/Add/Remove operations with field/value pairs
- `compile_append_details()` — iterates `details` array items
- `compile_append_item()` — compiles individual append { field, value } items

#### Step 4: Implement cross-resource effects (AINE/DINE)
- `compile_cross_resource_effect()` — emits HostAwait instruction to request related resource lookup
- Sets `resource_override_reg` to the host response register for existenceCondition compilation
- Compiles `details.existenceCondition` constraint against the related resource
- Builds structured result with effect name + details (including type, resourceGroupName, etc.)

#### Step 5: Implement effect resolution helpers
- `resolve_effect_kind()` — if effect node is parameter reference, resolves via `parameter_defaults`
- `resolve_effect_kind_from_parameter_default()` — extracts effect value from `parameters('effectParam')` expression
- `resolve_effect_name_from_parameter_default()` — string version
- `effect_kind_from_string()` — maps lowercase string → EffectKind enum
- `compile_effect_name_expression()` — compiles runtime effect name from parameter expression

### Phase B: Implement metadata

#### Step 6: Implement metadata recording functions
Replace no-op stubs in metadata.rs:
- `record_field_kind()` — `self.observed_field_kinds.insert(name.to_string())`
- `record_alias()` — `self.observed_aliases.insert(path.to_string())`
- `record_tag_name()` — `self.observed_tag_names.insert(tag.to_string())`
- `record_operator()` — maps OperatorKind to string, `self.observed_operators.insert()`
- `record_resource_type_from_condition()` — if condition is `{ field: "type", equals: X }`, insert X into `observed_resource_types`

#### Step 7: Implement resolve_effect_annotation()
Replace raw-clone stub:
- When effect is parameterized, resolve from `parameter_defaults` to get the actual effect name
- Fall back to `effect.raw` if resolution fails

#### Step 8: Implement populate_compiled_annotations()
Replace no-op stub:
- Insert into `program.metadata.annotations`: field_kinds, aliases, tag_names, operators, resource_types (as Value sets)
- Insert boolean flags: uses_count, has_dynamic_fields, has_wildcard_aliases, has_host_await
- Set `program.metadata.annotations["effect"]` (already done in init_effect_annotation)

#### Step 9: Implement populate_definition_metadata()
Replace no-op stub:
- Extract from PolicyDefinition: display_name, description, mode, category, version, preview flag
- Insert into `program.metadata.annotations`: parameter_names list, policy_type, policy_id, policy_name

### Phase C: File restructure

#### Step 10: Merge core.rs into mod.rs
Move all content from core.rs into mod.rs:
- `Compiler` struct definition
- `CountBinding` struct definition
- `compile()` pipeline
- All register/span/emit helpers
- All literal/builtin/chained-index helpers
- All alias resolution functions (`resolve_alias_path`, `strip_fq_prefix`)
- `patch_end_pc`, `current_pc`, `emit_coalesce_undefined_to_null`, `load_input`, `load_context`

Update all `use super::core::Compiler;` → `use super::Compiler;` in:
- conditions.rs
- expressions.rs
- fields.rs
- template_dispatch.rs

Delete `core.rs` and remove `mod core;` from mod.rs.

#### Step 11: Merge conditions_wildcard.rs into conditions.rs
Move 4 functions into conditions.rs:
- `has_unbound_wildcard_field()`
- `has_inner_unbound_wildcard_field()`
- `compile_condition_wildcard_allof()`
- `compile_allof_loop_inner()`

Delete `conditions_wildcard.rs` and remove `mod conditions_wildcard;` from mod.rs.

#### Step 12: Merge effects/metadata stubs into mod.rs
If effects.rs and metadata.rs have been implemented as separate files, merge them into mod.rs.
Alternatively, implement directly in mod.rs.

Delete: effects.rs, effects_modify_append.rs, metadata.rs
Remove their `mod` declarations from mod.rs.

#### Step 13: Simplify utils.rs
On the final branch, utils.rs is 143 LOC (current eval has ~429 LOC extensions that were trimmed).
- Verify `split_count_wildcard_path` matches final version
- Verify `split_path_without_wildcards` matches
- Ensure `json_value_to_runtime` has `pub(crate)` visibility

#### Step 14: Apply comment/doc and minor code differences
Based on comparison, apply these adjustments to match final branch:
- **expressions.rs**: Import path changes, comment enhancements, minor code tweaks
- **fields.rs**: Import path changes, documentation expansion
- **template_dispatch.rs**: Import path change, section header formatting
- **conditions.rs**: Import changes, `patch_end_pc` return type, documentation additions

### Relevant files
- `src/languages/azure_policy/compiler/mod.rs` — absorbs core.rs + effects + metadata → grows to ~1,681 LOC
- `src/languages/azure_policy/compiler/core.rs` — DELETE (merged into mod.rs)
- `src/languages/azure_policy/compiler/conditions.rs` — absorbs conditions_wildcard.rs content
- `src/languages/azure_policy/compiler/conditions_wildcard.rs` — DELETE (merged into conditions.rs)
- `src/languages/azure_policy/compiler/effects.rs` — DELETE (merged into mod.rs)
- `src/languages/azure_policy/compiler/effects_modify_append.rs` — DELETE (merged into mod.rs)
- `src/languages/azure_policy/compiler/metadata.rs` — DELETE (merged into mod.rs)
- `src/languages/azure_policy/compiler/expressions.rs` — import path + minor adjustments
- `src/languages/azure_policy/compiler/fields.rs` — import path + documentation
- `src/languages/azure_policy/compiler/template_dispatch.rs` — import path + formatting
- `src/languages/azure_policy/compiler/utils.rs` — streamline to 143 LOC final version

### Line counts
- mod.rs: +1,614 (absorbs core.rs, adds effects, metadata, emit helpers, aliases)
- Delete: core.rs (-367), conditions_wildcard.rs (-199), metadata.rs (-52 stub),
  effects.rs (-30 stub), effects_modify_append.rs (-6 stub)
- utils.rs: -320 (functions moved into mod.rs)
- template_dispatch.rs: +75 (new function dispatches)
- Effects: Deny, Audit, Modify, Append, DenyAction, AINE, DINE
- Cross-resource evaluation (host_await)
- Modify/Append details, effect resolution from parameters
- Metadata: field kinds, aliases, operators, resource types

### Verification
1. `cargo build` — all effects/metadata compiled, no stubs remain
2. `cargo clippy` — remove all `#![allow(dead_code)]` from deleted stubs
3. `cargo test --features azure_policy` — existing tests still pass
4. `TEST_CASE_FILTER="effect" cargo test --features azure_policy -- --nocapture`
5. Verify final file list matches: mod.rs, conditions.rs, count.rs, expressions.rs, fields.rs, template_dispatch.rs, utils.rs (7 files)

---

## PR 5: Test Suite

### Goal
Add the full YAML-driven test suite: 58 high-level cases + 8 parser cases + alias test data.

### Step 1: Update tests/azure_policy/mod.rs
Replace the 5-line eval version with the full 700+ line test runner that includes:
- `TestCase` struct with all fields (host_await, want_details, api_version, request_context, context, etc.)
- `HostAwaitEntry` struct
- `YamlTest` struct with aliases/global policy_rule/policy_definition support
- `yaml_test_impl()` — full evaluation pipeline (parse → compile → normalize → VM execute → assert)
- Helper functions: `make_input()`, `make_context()`, `yaml_to_regorus_value()`, `lowercase_value_keys()`, `lowercase_json_keys()`, `extract_effect_name()`, `extract_details()`, `extract_details_resource_type()`, `inject_type_field()`
- `#[test_resources("tests/azure_policy/cases/*.yaml")]` auto-discovery
- `test_specific_case()` with `TEST_CASE_FILTER` support
- `DEBUG_LISTING` and `DEBUG_RESOURCE` environment variable support
- Remove `mod normalization;` (normalization tests already on main)

### Step 2: Add test_aliases.json (if not already present)
- Verify `tests/azure_policy/aliases/test_aliases.json` exists (it does on eval branch)
- Add `tests/azure_policy/aliases/versioned_aliases.json` if needed

### Step 3: Create tests/azure_policy/cases/ directory with 74 YAML files
Add all YAML test case files. Categories:

**Foundation tests (13 files):**
- aliases.yaml, casing.yaml, effects.yaml, effect_details.yaml, exists.yaml
- expressions.yaml, fields.yaml, field_wildcard_collect.yaml
- implicit_allof.yaml, logical_combinators.yaml, modifiable_check.yaml
- operators.yaml, value_conditions.yaml

**Count tests (1 file):**
- count.yaml (field count, value count, where clauses, nested, count-as-any)

**Template function tests (3 files):**
- template_functions.yaml, template_functions_datetime_ip.yaml, template_functions_extra.yaml

**Advanced tests (4 files):**
- deep_nesting.yaml, type_coercion.yaml, parse_errors.yaml, policy_definition.yaml

**Infrastructure tests (2 files):**
- azure_policies.yaml, complex_policies.yaml, versioned_normalization.yaml

**E2E real-world policies (51 files):**
- e2e_aci_*.yaml, e2e_aks_*.yaml, e2e_approved_*.yaml, e2e_asc_*.yaml
- e2e_automanage_*.yaml, e2e_azupdate_*.yaml, e2e_cmk_*.yaml
- e2e_container_*.yaml, e2e_cosmos_*.yaml, e2e_custom_*.yaml
- e2e_datafactory_*.yaml, e2e_dcra_*.yaml, e2e_double_*.yaml
- e2e_fic_*.yaml, e2e_functionapp_*.yaml, e2e_guest_*.yaml
- e2e_keyvault_*.yaml, e2e_managed_*.yaml, e2e_monitoring_*.yaml
- e2e_nic_*.yaml, e2e_nsg_*.yaml, e2e_pg_*.yaml, e2e_portal_*.yaml
- e2e_servicebus_*.yaml, e2e_shared_*.yaml, e2e_signalr_*.yaml
- e2e_sql_*.yaml, e2e_ssh_*.yaml, e2e_storage_*.yaml
- e2e_stream_*.yaml, e2e_tags_*.yaml, e2e_vm_*.yaml, e2e_vnet_*.yaml

### Step 4: Update parser tests if needed
- Verify `tests/azure_policy/parser_tests/` cases are up to date
- Check if any new parser test YAML files need to be added (8 files on final branch)

### Step 5: Handle normalization test directory
- The eval branch has `tests/azure_policy/normalization/` with 13 YAML cases
- The final branch does NOT have this directory (these tests are already on main)
- Ensure `mod normalization;` is removed from the test mod.rs if normalization tests shipped in an earlier PR

### Relevant files
- `tests/azure_policy/mod.rs` — replace with full 700+ line test runner
- `tests/azure_policy/cases/*.yaml` — 74 new YAML test case files
- `tests/azure_policy/aliases/test_aliases.json` — verify present
- `tests/azure_policy/aliases/versioned_aliases.json` — verify present
- `tests/azure_policy/parser_tests/` — verify/update

### Line counts
- ~84 azure_policy test files (+32,806/-6,051 across 156 test files total)
- E2e YAML test suites (74+ cases)
- External test runner with known-failure tracking
- Lockdown test policies (9 real-world policies)
- RVM VM suite updates for changed instruction semantics

### Verification
1. `cargo test --features azure_policy` — all 74 YAML cases + 8 parser cases pass
2. `TEST_CASE_FILTER="count" cargo test --features azure_policy -- --nocapture` — count cases pass
3. `TEST_CASE_FILTER="effect" cargo test --features azure_policy -- --nocapture` — effect cases pass
4. `TEST_CASE_FILTER="e2e" cargo test --features azure_policy -- --nocapture` — all E2E policies pass
5. `cargo clippy --features azure_policy --all-targets` — no warnings in test code
6. `cargo xtask pre-push` — full CI check passes

---

## Execution Order & Dependencies

```
PR #686 (Skeleton + Conditions) ← merged/in review
    ↓
PR #688 (Count) ← in review, builds on PR #686
    ↓
PR 4 (Effects + Restructure) ← depends on PR #688 (count bindings used in effects)
    ↓
PR 5 (Tests) ← depends on PR 4 (tests exercise full compiler including effects)
```

PRs #688 and 4 could potentially be combined into one PR if review size is acceptable (~2,000 lines).
PR 5 is large (~33k lines) but is purely test data — can be reviewed for structure rather than line-by-line.

## Key Decisions
- All implementation should match the final `azure-policy-compiler` branch state
- `to_lowercase()` vs `to_ascii_lowercase()`: eval branch already fixed to `to_ascii_lowercase()`; keep that fix (it's better)
- `patch_end_pc` return type: eval has `Result<()>`, final has `()` — reconcile during restructure
- Strict path validation in utils.rs: eval has more guard rails; reconcile to match simpler final version
- `pub(super)` visibility on `emit_policy_operator`: eval has it; final makes it `fn` private — reconcile during merge

## Key Context

### Source branches
- **`azure-policy-compiler`** — final branch with completed compiler (source of truth for target state)
- **`azure-policy-compiler-eval`** — worktree at `/tmp/azure-policy-compiler-eval` where PRs are built incrementally

### Build & test commands
- `cargo fmt` — format
- `cargo clippy --all-features` — lint
- `cargo test --all-features -- count` — run count-related tests
- `cargo xtask pre-commit` — pre-commit hook (build + fmt + clippy)
- `cargo xtask pre-push` — full CI (pre-commit + doc tests + no_std + full test suite + 2861 OPA tests)

### Git workflow
- Edit files → `cargo fmt` → `git add -A && git commit --amend --no-edit` → `git push origin <branch> --force`
- All from `/tmp/azure-policy-compiler-eval` worktree

### Crate constraints
- `#![deny(clippy::indexing_slicing, clippy::expect_used)]` — cannot use `.expect()` or `[]` indexing
- `no_std` compatible: use `alloc::{format, string, vec}` imports
