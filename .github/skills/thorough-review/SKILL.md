---
name: thorough-review
description: >-
  Multi-agent thorough code review for regorus. Use this skill when asked to
  do a thorough review, deep review, or comprehensive review of code changes.
  Orchestrates parallel focused review agents for correctness, security, and
  polish, then synthesizes findings.
allowed-tools: shell
---

# Thorough Review Skill

You are orchestrating a multi-agent code review of a regorus change. regorus is
a security-critical multi-policy-language evaluation engine used in production
at Azure scale. Behavioral bugs are security bugs.

## Strategy

Run **automated checks first**, then launch **parallel focused review agents**,
then **synthesize** their findings into a unified report. You decide the
best approach based on the change — the guidance below is a starting point,
not a rigid script.

## Phase 1: Understand the Change

Before reviewing, understand what changed and why:

1. Get the diff: `git diff` (unstaged), `git diff --cached` (staged), or
   `git diff main...HEAD` (branch diff)
2. Read the changed files and their surrounding context
3. Identify which subsystems are affected
4. Read relevant knowledge files from `docs/knowledge/` — consult the
   reference table in `.github/copilot-instructions.md`

## Phase 2: Automated Checks

Run these before the AI review passes. Fix any failures before proceeding.

```bash
# Format check
cargo fmt --check

# Lint with all features
cargo clippy --all-features -- -D warnings

# Lint with no features (no_std)
cargo clippy --no-default-features -- -D warnings

# Run tests
cargo test

# OPA conformance (if Rego evaluation changed)
cargo test --test opa --features opa-testutil
```

Report any automated check failures immediately — they take priority over
review findings.

## Phase 3: Parallel Focused Reviews

Launch multiple focused review agents in parallel. Each agent reviews the
same diff but with a different perspective. Select agents based on what
changed — not every PR needs all agents.

### Agent Selection Guide

Choose agents based on the change type:

| Change type | Always invoke | Also consider |
|-------------|--------------|---------------|
| **Rego evaluation** | `semantics-expert`, `test-engineer` | `red-teamer`, `performance-engineer` |
| **RVM/compiler** | `semantics-expert`, `verification-engineer` | `performance-engineer`, `reliability-engineer` |
| **FFI/bindings** | `architect`, `api-steward` | `security-auditor`, `test-engineer` |
| **New feature** | `architect`, `program-manager`, `test-engineer` | `semantics-expert`, `demo-engineer` |
| **Security-sensitive** | `red-teamer`, `security-auditor` | `reliability-engineer`, `verification-engineer` |
| **Performance** | `performance-engineer`, `test-engineer` | `reliability-engineer` |
| **Refactoring** | `refactorer`, `test-engineer` | `architect` |
| **CI/build** | `ci-engineer` | `dx-engineer` |
| **API change** | `api-steward`, `architect` | `dx-engineer`, `demo-engineer` |
| **Any significant PR** | `tech-lead` (after other agents) | — |

### Invoking Agents

For each selected agent, launch it as a subagent with:
1. The full diff
2. A summary of what changed and why
3. The relevant knowledge file context (from Phase 1)

Agents are defined in `.github/agents/`. Each has specific focus areas,
knowledge file references, and output formats. Let them do their work
independently — diversity of perspective is the goal.

### Cross-Agent Context

To enable agents to build on each other's findings, use a shared context
document. After each agent completes, append its key findings to the context
so subsequent agents can reference them.

**Context structure:**

```markdown
## Shared Review Context

### Change Summary
(Your Phase 1 analysis — shared with all agents)

### Subsystems Affected
(List of modules, features, and boundaries touched)

### Agent Findings
#### [agent-name] — [timestamp]
- Key findings: ...
- Concerns raised: ...
- Questions for other agents: ...
```

**Context flow:**
1. Start with your Phase 1 analysis as the seed context
2. Launch the first wave of agents (e.g., semantics-expert + red-teamer)
3. Append their findings to the context
4. Launch the second wave with the enriched context (e.g., test-engineer
   can now see what the semantics-expert flagged)
5. Pass the full context to tech-lead for final synthesis

This is optional — for simple changes, parallel-only is fine. Use the
context protocol when agents' findings might inform each other (e.g.,
the red-teamer finds an attack vector that the test-engineer should
write a test for).

## Phase 4: Synthesize

Invoke the **tech-lead** agent with all agent findings to produce a unified
assessment. The tech-lead will:

1. **Collect** all findings from all agents
2. **Deduplicate** — multiple agents may flag the same issue
3. **Resolve conflicts** — when agents disagree, apply the priority framework
   (correctness > security > reliability > stability > performance > maintainability > DX)
4. **Categorize** every finding:
   - 🔴 **Correctness** — wrong result, logic error, behavioral bug
   - 🟠 **Security** — could affect policy evaluation, resource limits, DoS
   - 🟡 **Robustness** — panic path, missing error handling, unchecked arithmetic
   - 🔵 **Polish** — duplication, naming, style, documentation, dead code
   - ⚪ **Nit** — minor style preference
5. **Sort** by severity (🔴 first, then 🟠, 🟡, 🔵, ⚪)
6. **Present** the unified report with clear context for each finding:
   - File and line reference
   - What the issue is
   - Why it matters
   - Suggested fix (if not obvious)
7. **Make the call**: Ship / Ship with follow-ups / Revise / Redesign

## Phase 5: Iterate

If 🔴 or 🟠 findings exist:
- Help the author fix them
- After fixes, re-run the relevant focused review
- Repeat until no significant findings remain

A change is ready when you would trust it in production at scale.

## Adapting the Strategy

Not every change needs all agents. Use your judgment:

- **Tiny fix** (1-2 lines): a single correctness pass may suffice
- **New feature**: all three agents, plus extra attention to test coverage
- **Refactor**: polish agent is primary, correctness verifies behavior preservation
- **Dependency update**: security agent is primary
- **FFI change**: security agent with heavy focus on `ffi-boundary.md`

The goal is thoroughness, not ceremony. Skip what doesn't add value.
