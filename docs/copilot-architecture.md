<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Copilot Configuration Architecture

This document describes the GitHub Copilot configuration for regorus — how the
pieces fit together, when each layer activates, and how to extend or modify the
configuration.

## Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    GitHub Copilot Layers                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Auto-loaded every session:                                     │
│  ┌───────────────────────────────────────────┐                  │
│  │  .github/copilot-instructions.md (5 KB)   │ ← Identity,     │
│  │  Lean orientation + knowledge file refs    │   coding rules  │
│  └───────────────────────────────────────────┘                  │
│                                                                 │
│  Auto-loaded during code review:                                │
│  ┌───────────────────────────────────────────┐                  │
│  │  .github/copilot-code-review-instructions │ ← "Think freely"│
│  │  Severity categories + domain context     │   review guide   │
│  └───────────────────────────────────────────┘                  │
│                                                                 │
│  Loaded on demand (by description match or explicit invocation):│
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
│  │ Skills (6)   │  │ Agents (16)  │  │ Knowledge    │          │
│  │ Task workflows│  │ Role personas│  │ Files (20)   │          │
│  └──────────────┘  └──────────────┘  └──────────────┘          │
│                                                                 │
│  Cloud agent environment:                                       │
│  ┌───────────────────────────────────────────┐                  │
│  │  copilot-setup-steps.yml                  │ ← Rust toolchain │
│  │  Rust 1.92.0 + clippy + fmt + cache      │   + dependencies │
│  └───────────────────────────────────────────┘                  │
│                                                                 │
│  CI validation:                                                 │
│  ┌───────────────────────────────────────────┐                  │
│  │  copilot-config-validation.yml            │ ← Freshness +   │
│  │  YAML syntax, refs, staleness detection   │   correctness   │
│  └───────────────────────────────────────────┘                  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Layer Details

### 1. Instructions (`copilot-instructions.md`)

**When loaded**: Automatically, every Copilot session.

**Purpose**: Orient the agent to regorus identity, coding rules, build commands,
and provide a reference table of all 20 knowledge files.

**Design principle**: Keep this lean (~5 KB). Deep knowledge lives in
`docs/knowledge/` — this file just tells the agent where to look.

### 2. Code Review Instructions (`copilot-code-review-instructions.md`)

**When loaded**: Automatically during GitHub PR code reviews.

**Purpose**: Guide review thinking with severity categories, multi-scale review
approach, and domain-specific context (Undefined, FFI, dual-path, telemetry).

**Design principle**: "Think freely" — provides domain knowledge as context,
not a prescriptive checklist. The agent decides what to focus on.

### 3. Knowledge Files (`docs/knowledge/*.md`)

**When loaded**: On demand, when an agent or skill references them.

**Purpose**: Deep institutional knowledge about specific subsystems. Each file
captures knowledge that is not obvious from reading the code alone.

**20 files, ~70 KB total:**

| Category | Files |
|----------|-------|
| Core engine | `value-semantics`, `engine-api`, `error-handling-migration` |
| Execution | `interpreter-architecture`, `rvm-architecture`, `compilation-pipeline` |
| Rego language | `rego-semantics`, `rego-compiler`, `builtin-system` |
| Azure languages | `azure-policy-language`, `azure-policy-aliases`, `azure-rbac-language` |
| Safety & security | `policy-evaluation-security`, `ffi-boundary`, `feature-composition` |
| Diagnostics | `telemetry-and-diagnostics`, `causality-and-partial-eval` |
| Extensibility | `language-extension-guide`, `tooling-architecture`, `time-builtins-compat` |

**To add a knowledge file**: Create `docs/knowledge/<name>.md`, add it to the
reference table in `copilot-instructions.md`, and reference it from relevant
agents/skills.

### 4. Skills (`.github/skills/`)

**When loaded**: When the agent determines a skill is relevant (by description
match) or when explicitly invoked via `/skill-name`.

**Purpose**: Task-oriented workflows — step-by-step guidance for specific
operations.

| Skill | Purpose |
|-------|---------|
| `thorough-review` | Multi-agent parallel review with cross-agent context |
| `design-alternatives` | Generate 3+ approaches, evaluate against 9 dimensions |
| `add-builtin` | Step-by-step guide for adding a new builtin function |
| `opa-conformance` | OPA conformance testing workflow |
| `security-review` | Adversarial threat analysis |
| `verification` | Miri, property testing, Z3, Verus verification strategies |

### 5. Agents (`.github/agents/`)

**When loaded**: When explicitly invoked via `@agent-name` in chat, or when
another agent/skill spawns them as subagents.

**Purpose**: Role-based personas — each brings a distinct thinking mode to
code review, feature planning, or technical decisions.

**17 agents organized by function:**

| Group | Agents | When to use |
|-------|--------|-------------|
| **Core engineering** | `red-teamer`, `semantics-expert`, `architect`, `performance-engineer` | Every significant change |
| **Quality** | `test-engineer`, `verification-engineer`, `security-auditor` | Test coverage, safety-critical changes |
| **Operations** | `reliability-engineer`, `support-engineer`, `ci-engineer` | Production behavior, diagnostics, CI changes |
| **Security** | `ci-cd-security` | CI/CD pipeline security, workflow hardening |
| **Evolution** | `refactorer`, `api-steward` | Cleanup, API surface changes |
| **Product** | `program-manager`, `demo-engineer`, `dx-engineer` | Feature planning, examples, contributor experience |
| **Leadership** | `tech-lead` | Reconcile multi-agent findings, make decisions |

**Key features:**
- **Constitutional rules** in `tech-lead` — 9 inviolable guardrails
- **Cross-agent context protocol** — agents can build on each other's findings
- **Decision framework** — priority ordering: correctness > security > reliability > stability > performance > maintainability > DX

### 6. Cloud Agent Setup (`copilot-setup-steps.yml`)

**When loaded**: Before the cloud agent starts working on an issue/PR.

**Purpose**: Install Rust 1.92.0, clippy, rustfmt, cargo cache, and fetch
dependencies so the agent can build and test immediately.

### 7. Config Validation (`copilot-config-validation.yml`)

**When loaded**: On PR (config file changes), push to main, weekly Monday 7AM UTC.

**Purpose**: Validate YAML syntax, knowledge file references, skill frontmatter,
and detect stale knowledge files (source changed but knowledge file didn't).

## How It All Connects

### PR Review Flow

```
PR opened
  │
  ├─ GitHub auto-loads: copilot-instructions.md
  ├─ GitHub auto-loads: copilot-code-review-instructions.md
  │
  ├─ Single-pass review (default)
  │   Agent uses domain knowledge to review freely
  │
  └─ /thorough-review (when invoked)
      ├─ Phase 1: Understand the change
      ├─ Phase 2: Run automated checks
      ├─ Phase 3: Select and invoke agents (3-5 based on change type)
      │   ├─ Wave 1: Independent agents (parallel)
      │   ├─ Cross-agent context sharing
      │   └─ Wave 2: Agents informed by Wave 1 findings
      ├─ Phase 4: tech-lead synthesizes + applies constitutional rules
      └─ Phase 5: Iterate on critical findings
```

### Feature Development Flow

```
@program-manager "Should we build X?"
  → Scope, stakeholders, success criteria
@architect "How should we design X?"
  → System design, boundary impact, trade-offs
@design-alternatives "What are the options?"
  → 3+ approaches, evaluation matrix
@red-teamer "What could go wrong?"
  → Attack vectors, failure modes
@tech-lead "Which approach should we take?"
  → Decision with rationale
```

## Extending the Configuration

### Adding a Knowledge File
1. Create `docs/knowledge/<name>.md`
2. Add to the table in `.github/copilot-instructions.md`
3. Reference from relevant agents and skills
4. The CI validation workflow will check for broken references

### Adding an Agent
1. Create `.github/agents/<name>.agent.md` with YAML frontmatter
2. Include: description, tools, user-invocable, argument-hint
3. Add to the agent selection guide in `thorough-review` skill
4. Follow the existing pattern: Identity → Mission → What You Look For → Rules → Output Format

### Adding a Skill
1. Create `.github/skills/<name>/SKILL.md` with YAML frontmatter
2. Include: name, description, allowed-tools
3. Skills are task workflows — step-by-step guidance, not personas

### Modifying Constitutional Rules
Constitutional rules in `tech-lead.agent.md` are inviolable guardrails.
They should only change through deliberate, reviewed decisions — never
as a side effect of another change.
