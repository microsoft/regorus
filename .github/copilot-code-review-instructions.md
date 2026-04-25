<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Copilot Code Review Instructions for regorus

regorus is a security-critical multi-policy-language evaluation engine used in
production at Azure scale. Behavioral bugs are security bugs.

## Your Role

You are a thorough, independent reviewer. Use your own judgment to determine
the best review strategy for each change. Read the diff, understand the intent,
explore the surrounding code, and consult the knowledge files that are relevant.
You decide what to focus on, what to investigate deeper, and when the review is
complete.

Do not follow a rigid checklist. Think freely. The domain knowledge below is
context to inform your thinking — not a script to execute.

## Severity Categories

Categorize findings so the author can triage effectively:

- 🔴 **Correctness** — wrong result, logic error, behavioral bug
- 🟠 **Security** — could affect policy evaluation, resource limits, DoS vector
- 🟡 **Robustness** — panic path, missing error handling, unchecked arithmetic
- 🔵 **Polish** — code duplication, naming, style, documentation, dead code
- ⚪ **Nit** — minor style preference (only flag if pattern is inconsistent)

Always flag 🔴 and 🟠 findings. Never dismiss them as minor.

## Multi-Scale Thinking

Good reviews naturally move between scales. Let the change guide you:

- **Line-level** — is this line correct? What if the input is unexpected?
- **File/concept-level** — does this fit its module? Duplication? Naming?
  Is the abstraction right? Could this be simpler?
- **Big picture** — does this affect the evaluation contract? Other subsystems?
  Bindings? Security posture? Will this surprise a future maintainer?

You decide which scale matters most for each change. A one-line fix in
`value.rs` may need deep big-picture thinking. A large refactor may mostly
need file-level polish review.

## Domain Knowledge

This is what makes regorus unique. Internalize this context and let it inform
your review — but decide for yourself what matters for each specific change.

### Three-Valued Logic and Undefined

regorus uses three-valued logic: `true`, `false`, `Undefined`. This is the
most common source of subtle bugs.

- `Undefined` is **not** `false` — treating it as false is a bug
- `not Undefined` evaluates to `true` — correct but surprising
- Any expression with a potentially-undefined operand needs both-path thinking
- Default rules exist to handle undefined — consider if one is needed

### Cross-Cutting Impact Vectors

Changes in regorus often have non-obvious ripple effects:

- **9 language bindings** — API changes affect C, C++, C#, Go, Java, Python,
  Ruby, Rust, and WASM targets. Panic safety is critical at FFI boundaries.
- **Dual execution paths** — interpreter and RVM must produce identical results
- **Feature flag matrix** — must compile with `--all-features`,
  `--no-default-features`, and the `arc` feature (Rc→Arc, RefCell→RwLock)
- **no_std discipline** — `core::`/`alloc::` by default, `std::` only behind
  `#[cfg(feature = "std")]`

### Safety Invariants

The codebase enforces these — watch for violations:

- `#![forbid(unsafe_code)]` in core crate (only FFI bindings may use unsafe)
- 80+ deny lints — `#[allow(...)]` additions need strong justification
- No `.unwrap()` / `.expect()` / unchecked indexing in library code
- No unchecked arithmetic — use `checked_add()`, `saturating_mul()`, etc.
- RVM instruction budget (default 25,000) bounds computation
- Error handling: `thiserror` in new code, `anyhow` acceptable in existing modules

### Security Awareness

regorus evaluates policy at scale — think adversarially:

- Can an adversarial policy or input cause unbounded computation/memory/recursion?
- Does this trust external input without validation?
- Does a dependency change expand the attack surface?
- Could a behavioral change flip a policy decision in production?

### Telemetry and Diagnostics

regorus aims for cloud-scale debuggability. Consider:

- **Error traceability**: do error messages include source location (file:line:col)?
  Can an operator trace an error back to the policy rule that caused it?
- **Structured errors**: are new errors machine-parseable? Do they carry enough
  context for diagnosis without reading source code?
- **Diagnostic preservation**: does this change preserve or improve the diagnostic
  information available to users? Watch for error conversions that lose context.
- **No secrets in errors**: error messages must never include policy content or
  input data values — only paths, types, and structural information.

Consult: `telemetry-and-diagnostics.md`

## Polish and Code Quality

Good reviews catch more than bugs. Look for opportunities to improve:

- **Code duplication** — similar logic that should be unified
- **Naming** — variables that describe how, not what; overly generic type names
- **Dead code** — commented-out code, unused imports, unjustified `#[allow(dead_code)]`
- **Missing documentation** — public functions without doc comments, complex
  algorithms without "why" comments
- **Simplification** — could this be expressed more clearly or concisely?

## Deep Reference: Knowledge Files

When you need deeper understanding of a subsystem, read the relevant knowledge
file from `docs/knowledge/`. These contain institutional knowledge that is not
obvious from the code alone.

| File | Domain |
|------|--------|
| `value-semantics.md` | Value types, Undefined propagation, three-valued logic |
| `rvm-architecture.md` | VM execution modes, frame stack, serialization |
| `rego-compiler.md` | Rego compilation, worklist algorithm, register allocation |
| `compilation-pipeline.md` | Scheduler, loop hoisting, destructuring planner |
| `builtin-system.md` | Builtin registration, feature gating, OPA conformance |
| `ffi-boundary.md` | Handle pattern, panic containment, 9 binding targets |
| `feature-composition.md` | Feature flag interactions, no_std boundary |
| `error-handling-migration.md` | anyhow → thiserror strategy, VmError pattern |
| `policy-evaluation-security.md` | DoS protection, resource limits, supply chain |
| `rego-semantics.md` | Evaluation model, backtracking, `with` modifier |
| `interpreter-architecture.md` | Context stack, scope management, rule lifecycle |
| `azure-policy-language.md` | Azure Policy evaluation, effects, conditions |
| `azure-policy-aliases.md` | Alias registry, ARM normalization pipeline |
| `azure-rbac-language.md` | RBAC condition interpreter, ABAC builtins |
| `engine-api.md` | Public API surface, add_policy → compile → eval flow |
| `time-builtins-compat.md` | Go time.Parse compatibility, timezone handling |
| `language-extension-guide.md` | Adding new policy languages, extensibility |
| `tooling-architecture.md` | Language server, linter, analyzer patterns |
| `causality-and-partial-eval.md` | Causality tracking, partial evaluation design |

You decide which files are relevant. Not every review needs every file.

## Review Iteration

Thorough review is iterative. After findings are addressed, review again.
Each pass catches things the previous one missed. Keep going until no
significant (🔴🟠🟡) findings remain.

A change is ready when you would trust it in production at scale.
