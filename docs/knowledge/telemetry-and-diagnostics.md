<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Telemetry and Diagnostics

## Overview

regorus evaluates authorization and compliance policies at Azure scale. When a
policy returns an unexpected result, operators need to understand **why** —
without reading regorus source code, without reproducing the exact environment,
and often under time pressure during an incident.

This knowledge file captures the telemetry and diagnostics architecture: what
exists today, what's planned, and the design principles that guide diagnostic
features.

## Design Principles

1. **Every decision must be explainable** — "policy X denied request Y because
   condition Z at policy.rego:42 evaluated to Undefined"
2. **Errors trace back to policy source** — file, line, column, rule name
3. **Structured over unstructured** — machine-parseable diagnostics enable tooling
4. **Zero-cost when off** — diagnostics must not affect evaluation performance
   when not enabled (compile-time or runtime gating)
5. **Cloud-scale observability** — span-based tracing that integrates with
   distributed tracing systems (OpenTelemetry)
6. **Defense in depth** — no secrets in diagnostics (policy content, input data)

## Current State

### Source Location Tracking (Strong)

Every syntax element carries a `Span` with source file, line, column, and byte
offset. The `Source::message()` method produces formatted error output:

```
error: policy.rego:42:5
  |
  42 | input.role == "admin"
  |     ^^^^^^^^^ type mismatch: expected string, got number
```

This works for **parse and compile errors**. Evaluation errors have partial
coverage — some carry Span, others lose it during execution.

### Error Types (Comprehensive but Fragmented)

Multiple error hierarchies exist across subsystems:

| Subsystem | Error type | Location tracking |
|-----------|-----------|-------------------|
| Lexer/Parser | `Span`-annotated errors | ✅ file:line:col |
| Rego compiler | `SpannedCompilerError` | ✅ file:line:col |
| RVM execution | `VmError` (40+ variants) | ⚠️ program counter only |
| Schema validation | `ValidationError` (20+ variants) | ⚠️ JSON path only |
| Azure RBAC | `ConditionEvalError` | ⚠️ limited |
| Interpreter | `anyhow::Error` with context | ⚠️ varies |

**Gap**: RVM errors have a program counter (`pc`) but no reverse mapping to
policy source location. This is the most critical diagnostic gap — when the VM
reports `InstructionLimitExceeded at pc=1234`, operators cannot trace back to
which policy rule was executing.

### Trace Builtin (Exists, Not Exported)

The `trace(msg)` builtin accumulates messages internally via
`Interpreter::set_traces(bool)`. However:
- **No public API** to retrieve traces from `Engine`
- Traces are string-only (not structured)
- No trace correlation with evaluation steps
- No RVM equivalent of trace collection

### Print Gathering

`Engine::take_prints()` retrieves accumulated `print()` output. This works
but is designed for debugging by policy authors, not for operational telemetry.

### Limit Enforcement

Resource limits produce diagnostic VmError variants:
- `InstructionLimitExceeded { pc, limit }`
- `MemoryLimitExceeded { usage, limit }`
- `TimeLimitExceeded { elapsed, limit }`

These include numeric context but not evaluation context (which rule, which
input).

### Coverage Tracking (Internal Only)

Feature-gated coverage tracking exists in the interpreter but has no public
API. This could be the foundation for evaluation path diagnostics.

## Planned Capabilities

### Phase 1: Error Traceability (Foundation)

- **PC-to-source mapping**: RVM bytecode instructions should carry source
  location metadata, enabling reverse mapping from `pc` to policy:line:col
- **Export trace builtin**: Expose `traces` through the public `Engine` API
- **Structured errors**: Migrate key errors to structured types with
  `serde::Serialize` for machine consumption
- **Evaluation context in limits**: When limits are hit, include the rule name
  and approximate policy location

### Phase 2: Evaluation Explanation

- **Decision attribution**: "rule `allow` returned true because all conditions
  in the rule body at policy.rego:15-28 were satisfied"
- **Undefined explanation**: "rule `allow` was Undefined because `input.role`
  at policy.rego:18 was not present in the input document"
- **Causality tracking**: integration with the planned causality system
  (see `causality-and-partial-eval.md`)
- **Coverage export**: public API for evaluation path coverage data

### Phase 3: Cloud-Scale Telemetry

- **OpenTelemetry integration**: optional spans for parse, compile, evaluate
  phases, gated behind a feature flag
- **Metric hooks**: evaluation count, duration, cache hit rate, rule count —
  exposed as callbacks or trait implementations
- **Evaluation replay**: record input + policy + configuration as a
  deterministic replay bundle for reproduction
- **Diagnostic verbosity levels**: off / errors-only / summary / detailed / trace

## Review Checklist for Diagnostics

When reviewing code changes, consider:

1. **Error messages**: Do they include source location (file:line:col)?
   Do they include the rule/function name? Are they actionable without
   reading regorus source?
2. **New error paths**: Is the error type structured? Does it carry enough
   context for diagnosis?
3. **Evaluation changes**: If this changes what a policy returns, can a user
   understand why the result changed?
4. **Resource limits**: When limits trigger, does the error help the operator
   fix the issue (e.g., "increase instruction limit" or "simplify rule X")?
5. **RVM changes**: Do new instructions carry source location metadata?
6. **FFI boundary**: Are errors properly translated for each binding target?
   Do they preserve diagnostic information across the FFI?
7. **No secrets**: Error messages must never include policy content or input
   data values — only paths, types, and structural information.

## Architecture Notes

### Zero-Cost Diagnostics Pattern

Diagnostics should use Rust's zero-cost abstraction patterns:

```rust
// Feature-gated: zero cost when disabled
#[cfg(feature = "diagnostics")]
fn record_evaluation_step(&mut self, rule: &Rule, result: &Value) { ... }

#[cfg(not(feature = "diagnostics"))]
fn record_evaluation_step(&mut self, _rule: &Rule, _result: &Value) {}
```

Or runtime-gated with branch prediction hints:

```rust
if unlikely(self.diagnostics_enabled) {
    self.record_step(pc, instruction);
}
```

### Structured Diagnostic Output

```json
{
  "evaluation_id": "uuid",
  "policy": "rbac.rego",
  "query": "data.rbac.allow",
  "result": false,
  "duration_us": 142,
  "rules_evaluated": 7,
  "explanation": [
    {
      "rule": "allow",
      "location": "rbac.rego:15",
      "result": "undefined",
      "reason": "input.role not present in input"
    }
  ]
}
```

### Integration Points

- **Engine API**: `Engine::set_diagnostics(DiagnosticLevel)` + `Engine::take_diagnostics()`
- **FFI**: `regorusSetDiagnostics()` / `regorusGetDiagnostics()` across all bindings
- **CLI**: `--diagnostics=detailed` flag for `regorusctl` / evaluation tools
- **OpenTelemetry**: Optional `tracing` crate integration behind feature flag
