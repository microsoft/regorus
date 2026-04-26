<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Workflow and Script Security Patterns

## Overview

regorus uses GitHub Actions workflows and shell scripts for CI/CD, automated
code review, and codebase auditing. These scripts interact with untrusted
input (PR diffs, workflow_dispatch parameters, AI model outputs) and post
results using privileged tokens. This document catalogs the security patterns
and anti-patterns relevant to this infrastructure.

## GitHub Actions Expression Injection

### The Problem

GitHub Actions `${{ }}` expressions are **string-interpolated before shell
execution**. Any user-controlled value injected this way can break out of
string context and execute arbitrary commands.

**Dangerous patterns:**
```yaml
# BAD — attacker-controlled input directly in shell
run: |
  PR_NUMBER="${{ github.event.inputs.pr_number }}"

# BAD — PR title/body/branch are attacker-controlled
run: |
  echo "Processing: ${{ github.event.pull_request.title }}"
```

**Safe patterns:**
```yaml
# GOOD — pass via env, validate before use
env:
  PR_NUMBER: ${{ github.event.inputs.pr_number }}
run: |
  if [[ ! "$PR_NUMBER" =~ ^[0-9]+$ ]]; then
    echo "::error::Invalid PR number"
    exit 1
  fi
```

### Values That Are Safe to Interpolate

- `github.repository` — controlled by the org, not PR authors
- `github.event_name` — GitHub-controlled enum
- `github.sha`, `github.ref` — Git references (but validate format)
- `steps.*.outputs.*` — safe **only if** the step that set them validated input

### Values That Are NEVER Safe to Interpolate

- `github.event.inputs.*` — user-provided workflow_dispatch inputs
- `github.event.pull_request.title` / `.body` / `.head.ref`
- `github.event.issue.title` / `.body`
- `github.event.comment.body`
- `github.event.review.body`
- Any value derived from Git commit messages

## GITHUB_OUTPUT and GITHUB_ENV Injection

### The Problem

Writing to `$GITHUB_OUTPUT` or `$GITHUB_ENV` using simple echo:

```bash
# VULNERABLE — newlines in VALUE inject additional outputs/env vars
echo "key=${VALUE}" >> "$GITHUB_OUTPUT"
```

If `VALUE` contains a newline followed by `other_key=malicious`, the attacker
controls additional workflow outputs.

### Safe Pattern

```bash
# Reject newlines entirely (recommended for simple values)
if [[ "$VALUE" == *$'\n'* ]] || [[ "$VALUE" == *$'\r'* ]]; then
  echo "::error::Input contains newlines"
  exit 1
fi
echo "key=${VALUE}" >> "$GITHUB_OUTPUT"

# Or use heredoc delimiter for multiline values
{
  echo "key<<GHEOF"
  echo "$VALUE"
  echo "GHEOF"
} >> "$GITHUB_OUTPUT"
```

## Shell Script Hardening

### Required Header

All regorus scripts begin with:
```bash
#!/usr/bin/env bash
set -euo pipefail
```

### Input Validation

Validate all inputs at script entry:
```bash
# Repo format: owner/name
if [[ ! "$REPO" =~ ^[A-Za-z0-9._-]+/[A-Za-z0-9._-]+$ ]]; then
  echo "::error::Invalid repo format: '${REPO}'"
  exit 1
fi

# Numeric values
if [[ ! "$PR_NUMBER" =~ ^[0-9]+$ ]]; then
  echo "::error::Invalid PR number: '${PR_NUMBER}'"
  exit 1
fi

# Script names (for dispatch)
if [[ ! "$SCRIPT" =~ ^[a-z0-9-]+$ ]]; then
  echo "::error::Invalid script name: '${SCRIPT}'"
  exit 1
fi
```

### Temp File Safety

```bash
# BAD — predictable path, symlink race
DIFF="/tmp/pr_diff.txt"

# GOOD — private temp directory, auto-cleanup
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT
DIFF="$TMPDIR/pr_diff.txt"
```

### Heredoc Safety

```bash
# BAD — unquoted heredoc expands variables and backticks
cat <<PROMPT
Review this diff: ${DIFF_CONTENT}
PROMPT

# GOOD — quoted heredoc prevents expansion
cat <<'PROMPT'
Review this diff: ${DIFF_CONTENT}
PROMPT

# BEST — use jq to build JSON payloads with untrusted content
jq -n --arg diff "$DIFF_CONTENT" '{"prompt": $diff}'
```

## Model Output Sanitization

### The Problem

AI model responses are posted via GitHub API as review comments, issue bodies,
or PR reviews. These responses are **untrusted** — an attacker can craft PR
diffs that cause prompt injection, making the model output:

- `@username` mentions → notification spam
- Malicious URLs → phishing via trusted-looking automation
- Markdown that mimics GitHub UI → social engineering
- Excessive content → review noise

### Sanitization Patterns

```bash
# Defang @mentions: insert zero-width joiner after @
# @user → @‍user (invisible but prevents GitHub notification)

# In jq (preferred — handles JSON and Unicode safely):
jq '.title = (.title | gsub("@(?<u>[A-Za-z0-9_-])"; "@\u200d\(.u)"))
  | .body  = (.body  | gsub("@(?<u>[A-Za-z0-9_-])"; "@\u200d\(.u)"))'

# In Perl (for plain text streams):
echo "$model_output" | perl -CSD -pe 's/\@([A-Za-z0-9_-])/\@\x{200d}$1/g'

# Note: sed does not reliably support Unicode codepoint escapes; prefer jq or Perl.
```

### Silent Failure Detection

```bash
# Track failures across perspectives/analyses
FAILED=0
TOTAL=0

for item in $ITEMS; do
  TOTAL=$((TOTAL + 1))
  result=$(call_model ...) || { FAILED=$((FAILED + 1)); continue; }
done

# Fail if ALL analyses failed (model/API issue, not "no findings")
if [ "$TOTAL" -gt 0 ] && [ "$FAILED" -eq "$TOTAL" ]; then
  echo "::error::All $TOTAL analyses failed"
  exit 1
fi
```

## SIGPIPE Handling

### The Problem

Under `set -eo pipefail`, piping to `head` causes SIGPIPE (exit 141) when
the upstream command produces more output than `head` consumes:

```bash
# BAD — SIGPIPE if diff > 60000 bytes
gh api ... | head -c 60000
```

### Safe Pattern

```bash
# GOOD — fetch to file first, then truncate
gh api ... > "$TMPDIR/full_output.txt"
head -c 60000 "$TMPDIR/full_output.txt" > "$TMPDIR/truncated.txt"
```

## Workflow Permission Model

### Principle of Least Privilege

```yaml
permissions:
  contents: read        # Only if checking out code
  pull-requests: write  # Only if posting review comments
  issues: write         # Only if creating/updating issues
  models: read          # Only if calling GitHub Models API
```

### Token Scoping

- `GITHUB_TOKEN` permissions are set per-workflow, not per-step
- Use the `copilot` environment for secrets that should only be available
  to Copilot-related workflows
- Never pass tokens to model API calls beyond what's needed for authentication

## regorus-Specific Patterns

### Action Pinning Convention

All `actions/*` references use full SHA pins, managed by Dependabot:
```yaml
uses: actions/checkout@de0fac2e4500dabe0009e67214ff5f5447ce83dd  # v6.0.2
```

### Script Dispatch Safety

The codebase-audit workflow allows preset configs to specify a script name.
This must be validated:
```bash
# Script name must be [a-z0-9-]+ — no path separators, no dots
if [[ ! "$SCRIPT" =~ ^[a-z0-9-]+$ ]]; then
  echo "::error::Invalid script name"
  exit 1
fi
# Script must exist in the expected directory
if [ ! -f ".github/scripts/${SCRIPT}.sh" ]; then
  echo "::error::Script not found: ${SCRIPT}"
  exit 1
fi
```

## Checklist for New Workflows/Scripts

1. ☐ No `${{ }}` expressions in `run:` blocks (use `env:`)
2. ☐ All inputs validated at entry (format, length, no control chars)
3. ☐ Temp files use `mktemp` + `trap` cleanup
4. ☐ Heredocs are quoted when containing external data
5. ☐ Model output sanitized before posting (defang @mentions, URLs)
6. ☐ Silent failures detected and reported
7. ☐ Permissions minimally scoped
8. ☐ Actions pinned by SHA
9. ☐ SIGPIPE handled (no `| head` on unbounded streams)
10. ☐ `set -euo pipefail` at script entry
