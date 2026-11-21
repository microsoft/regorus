# History branch loose ends and remaining validation

## Context
The user asks what loose ends remain after the history ownership cleanup and Verus workaround investigation. The inventory below separates remaining delivery evidence from optional maintenance and accepted limitations; no concrete unfinished history implementation or production-proof blocker was found in this inspection. The proposed follow-through is diagnostic binding validation only, using existing runners without source changes, staging, committing, pushing or changing verifier pins.

## Current loose ends and completed evidence
- Read-only `git status --short --branch` reports `feature/junco` tracking `origin/feature/junco`, with 0 staged entries, 60 unstaged tracked entries and 4 untracked entries. The untracked entries include `benches/history_table.rs`, `src/languages/history_table/store.rs`, `src/rvm/program/history.rs` and the `src/rvm/vm/history_tables/` directory. Shipping only tracked modifications would omit required additions.
- `/tmp/history-structural-results.t1pkl5d_/summary.json:242-303` records successful runtime/proof/debug-CI and selected push-preparation commands, zero surviving cleanup-review findings, and an unrun staging-sensitive aggregate hook. It explicitly excludes all nine binding smoke suites. **Correction:** this is not evidence that every hook constituent passed: `xtask/src/tasks/dev/precommit.rs:29-37` also runs format checking and full workspace/binding Clippy, whereas only the narrower targeted lint check is recorded. Those remain unrecorded delivery checks, not observed failures.
- `/tmp/deep-review-report.md:3-10,33-39` covers the structural cleanup against its execution-start snapshot, not all pending branch work. Its recorded final production proof gates have zero errors; do not describe this as a new whole-branch review.
- `/tmp/verus-eq-workaround.1u0mnkwb/summary.json` records zero repository edits and no successful explicit-reference workaround. The production field-level equality bypass remains the chosen workaround; the original standalone Verus failure is preserved.
- The retained `final-ci-debug.log:5958-5969` records a successful `cargo check --features std,arc,full-opa,allocator-memory-limits --no-default-features` with an unused `memory::current_thread_live_bytes` re-export warning. Current `src/utils/limits/mod.rs:17-18` enables that re-export without `rvm`; its three consumers are in `src/rvm/vm/machine.rs`, and `src/lib.rs:168-169` gates that module with `rvm`. This is optional cfg hygiene, not a failed build or history correctness blocker.
- Current seam inspection found no concrete incomplete history cutover. `tests/history_table.rs:1297-1320` intentionally rejects the removed builtin in both interpreter evaluation and Rego-to-RVM compilation; `docs/builtins.md:243-249` intentionally limits the typed API to native Rust/RVM. Do not reintroduce binding forwarding or a compatibility builtin.
- `src/languages/history_table/store.rs:475-489,815-830` retains every history in the owner's vector. Dropping a `HistoryHandle` does not remove its history while the store survives. This documented lifetime is a deployment consideration for long-lived owners, not a request to invent deletion semantics.
- Only the six benchmark smoke cases were executed (`final-bench-smoke.json`, `final-bench-smoke.log`); no latency measurement was produced. `benches/history_table.rs:16-66` and `docs/builtins.md:337-341` deliberately exclude compilation, ingestion and setup from the measured decision path.
- The completed cutover also has a retained source review at `/tmp/history-structural-results.t1pkl5d_/prior-deep-review-report.md`. Its old production proof failures are superseded by the final zero-exit results in `final-proof-results.json`; they must not be reopened from the old report.
- The five changed binding manifests remove `history = ["regorus/history"]`; this is an intentional breaking contract recorded in `CHANGELOG.md:13`, not an unfinished feature. Native binding integration remains unexercised by the retained core-only gates.
- `xtask/src/tasks/bindings/all.rs:88-144` invokes seven targets only: C, C++, C-no_std, Java, Python, WASM and C#. It omits Go and Ruby, and the FFI unit/contention suite is separate. This contradicts the repository instruction describing the aggregate as all nine; use the existing individual tasks rather than changing that runner during this work.
- PATH discovery found Cargo, Rust, CMake, C/C++ compilers, Java, Python, Node and Ruby, but not `mvn`, `maturin`, `wasm-pack`, `dotnet`, `go` or `bundle`. The first five are direct-launch prerequisites with no task bootstrap. Ruby can attempt to install Bundler, but that is not authorization to provision tools during the inventory. Missing tools are not binding test failures.

## Approach

### 1. Preserve the pending patch and create an isolated validation snapshot

After approval, create a new temporary directory outside `/home/eioannidis/git/regorus`. Enumerate tracked and nonignored untracked paths with `git ls-files --cached --others --exclude-standard -z`, copy their current existing contents with relative paths and symlinks preserved, and skip paths deleted in the working tree. Include the new history directory and the three other untracked additions listed above. Do not use a HEAD-only archive or worktree: it would omit the actual pending patch. Do not copy `.git` or ignored build/package artifacts.

Run all subsequent commands from the snapshot root, with `CARGO_TARGET_DIR` unset so existing binding runners find their expected per-crate outputs. Root `build.rs:8-15` then cannot replace the original checkout's hooks. Keep stdout/stderr and exit statuses in the temporary evidence directory; do not write a report or harness into the repository. Existing tasks can regenerate headers, update copied lockfiles, run `go mod tidy`, and install local test dependencies; the snapshot prevents those actions from altering the pending patch. Do not copy any generated changes back.

### 2. Exercise the available native binding paths

Use existing commands, in this order, independently recording each result rather than aborting the whole inventory at the first failure:

```sh
cargo xtask test-ffi --release
cargo xtask test-c --release
cargo xtask test-cpp --release --skip-ffi
cargo xtask test-c-no-std --release --skip-ffi
```

The C command prepares FFI artifacts itself; C++ and C-no_std may reuse them only if that preparation succeeded. If it did not, omit `--skip-ffi` for those two commands so each receives an independent attempt. These are real sample/unit-test executions, not substitute Cargo checks. Use the existing `contention_checks` selection made by `TestFfiCommand`; add no new tests, helper APIs or binding history feature.

### 3. Attempt remaining bindings only when their prerequisites are available

Use the individual commands below instead of the fail-fast aggregate so missing Maven does not hide other runnable suites. Preflight the named tools and versions; do not manually install missing SDKs, package managers or toolchains as part of this diagnostic scope. Normal dependency restore by an otherwise runnable existing task is allowed after approval. Mark a suite `blocked — missing prerequisite` if unavailable, name the exact tool/version, and continue with the others.

| Suite | Required local prerequisite beyond Rust/native tools | Exact command from snapshot root |
|---|---|---|
| Java | `mvn`, `java`, `javac`, `python3` | `cargo xtask test-java --release` |
| Python | Python >=3.10 with venv/pip, `maturin` | `cargo xtask test-python --release --python python3` |
| WASM | `wasm-pack`, Node and its supported WASM toolchain | `cargo xtask test-wasm --release --node node` |
| C# | .NET SDK 8.0.412 or compatible `latestFeature` roll-forward per `bindings/csharp/global.json` | `cargo xtask test-csharp --release --force-nuget` |
| Go | Go >=1.21.5 and cgo/native compiler | `cargo xtask test-go --release` |
| Ruby | Ruby >=3.4.2, RubyGems >=3.6.5 and existing Bundler | `cargo xtask test-ruby --skip-bundler-install --skip-clippy` |

The forced C# package rebuild prevents stale package success. Ruby has no `--release` flag; skip only its optional Rust lint prepass, not Rake's compile/test flow, and identify that skip in the evidence. Do not change `TestAllBindingsCommand`, add binding exports, repair unrelated failures, or redesign history lifetimes. A source failure is a new, explicitly located loose end to report, not permission to start a separate implementation.

### 4. Return the readiness inventory

Report each of the nine language targets and the separate FFI suite as passed, failed with its first actionable diagnostic, or blocked by a named prerequisite. Keep historical production proof/runtime successes separate from new binding results. List unrecorded full format/lint checks and the unrun aggregate hook as delivery deferrals; leave the optional allocator warning, measured-performance gap, retained-history lifetime and upstream verifier defect unchanged. Do not call the branch fully push-ready while these delivery gaps remain.

## Verification

- Planning itself runs no builds/tests/hooks and changes no repository files. Current findings derive from the read-only source inspection and the retained logs named above.
- The new diagnostic evidence must exercise a binding executable, not just compile it. In `bindings/c/rvm_tests.c:28-47,157-170`, data assigns `alice` the `admin` role and input requests `read`; the binary compiles, serializes/deserializes, loads and evaluates the policy, and must print `Decision: user=alice action=read -> allow=true`. Its HostAwait continuation receives `{"tier":"gold"}` and must produce `true` (`:250-258`). The C runner launches this binary as well as its interpreter sample. Record those observed outputs after the branch's manifest/serialization changes.
- A passed binding suite requires its existing runtime tests/sample to complete successfully; a dependency download or compiler success alone is not a pass. Ruby runtime success with `--skip-clippy` is not full lint success. Any copied lockfile resolution changes must be disclosed rather than claimed as verification of unchanged locks.
- Completion of this diagnostic plan means every listed suite has an observed result or concrete prerequisite blocker and the readiness report preserves the unresolved items. It does not mean all suites passed. With the currently missing tools, full nine-language coverage remains blocked unless the execution environment has been provisioned separately.
- Do not rerun the known standalone inherited-ensures failure or the already-passing production matrix merely to reproduce historical output. No production code changes are proposed.

## Assumptions & contingencies

- Approval authorizes only the diagnostic validation above and its temporary build artifacts/dependency restores. The original working tree, index, hooks and pending source changes remain untouched; publication needs separate authorization.
- If a required tool or version is missing, do not install it or claim a suite was exercised. Finish every runnable independent suite and report the missing prerequisite with the exact command still needed. A broken test is reported with its source/diagnostic; fixing it is a different task.
- If the temporary historical evidence files are no longer available, report those prior results as unavailable instead of inventing counts. The current source still establishes the documented limitations; do not rerun unchanged failures to reconstruct old logs.
- Keep `local://history-structural-cleanup-plan.md` as completed execution history. Optional warning cleanup, performance measurement, history deletion semantics and upstream Verus changes are not silently added to this validation pass.
