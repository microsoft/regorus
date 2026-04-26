#!/usr/bin/env bash
# Copyright (c) Microsoft Corporation. All rights reserved.
# Licensed under the MIT License.
#
# Knowledge accuracy audit using GitHub Models API.
# Compares each knowledge file against the actual source code it documents.
# Detects: inaccuracies, stale descriptions, deleted/renamed files,
# new untracked source files, and refactored APIs.
#
# Usage: knowledge-accuracy.sh <repo>
# Requires: GITHUB_TOKEN env var, jq, gh CLI

set -euo pipefail

REPO="$1"

# Validate inputs
if [[ ! "$REPO" =~ ^[A-Za-z0-9._-]+/[A-Za-z0-9._-]+$ ]]; then
  echo "::error::Invalid repo format: '${REPO}'"
  exit 1
fi

COMMIT_SHA=$(git rev-parse HEAD)
MODEL="openai/gpt-4.1-mini"
API_URL="https://models.github.ai/inference/chat/completions"

# Secure temp directory — cleaned up on exit
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

# Sanitize model output: defang @mentions and neutralize URLs
sanitize_model_output() {
  jq '
    def defang: gsub("@(?<u>[A-Za-z0-9_-])"; "@\u200d\(.u)");
    def defang_urls: gsub("(?<proto>https?)://"; "\(.proto)[://]");
    if type == "array" then
      [.[] |
        .title = ((.title // "") | defang | defang_urls) |
        .body  = ((.body  // "") | defang | defang_urls) |
        .snippet = ((.snippet // "") | defang | defang_urls)]
    elif type == "object" then
      .title = ((.title // "") | defang | defang_urls) |
      .body  = ((.body  // "") | defang | defang_urls) |
      .snippet = ((.snippet // "") | defang | defang_urls)
    else . end'
}

FAILED_ANALYSES=0
TOTAL_ANALYSES=0

echo "=== Knowledge Accuracy Audit ==="
echo "Repository: ${REPO}"
echo "Commit: ${COMMIT_SHA}"

# ── Phase 1: Inventory ──────────────────────────────────────────────────
# Build a map of knowledge files → referenced source files, and discover
# source files not covered by any knowledge doc.

echo ""
echo "=== Phase 1: Inventory ==="

ALL_FINDINGS="[]"
KNOWLEDGE_DIR="docs/knowledge"
KNOWLEDGE_FILES=()
for kf in "${KNOWLEDGE_DIR}"/*.md; do
  [ -f "$kf" ] && KNOWLEDGE_FILES+=("$kf")
done
echo "Knowledge files: ${#KNOWLEDGE_FILES[@]}"

# Build full source inventory for coverage analysis
SOURCE_FILES=$(find src/ bindings/ -type f -name '*.rs' 2>/dev/null | sort)
SOURCE_COUNT=$(echo "$SOURCE_FILES" | wc -l | tr -d ' ')
echo "Source files in repo: ${SOURCE_COUNT}"

# Track which source files are referenced by at least one knowledge doc
REFERENCED_FILES=""

# ── Phase 2: Per-Knowledge-File Analysis ─────────────────────────────────

echo ""
echo "=== Phase 2: Knowledge File Analysis ==="

for kf in "${KNOWLEDGE_FILES[@]}"; do
  kf_name=$(basename "$kf")
  echo ""
  echo "--- Checking: ${kf_name} ---"

  # Extract source file references from this knowledge doc
  REFS=$(grep -oE '(src|bindings|tests|examples|xtask)/[a-zA-Z0-9_/.*-]+\.(rs|toml|yml|yaml)' "$kf" 2>/dev/null | sort -u || true)
  # Also extract backtick-quoted module paths like `src/value.rs`
  REFS2=$(grep -oE '`(src|bindings|tests|examples|xtask)/[a-zA-Z0-9_/.*-]+\.(rs|toml)`' "$kf" 2>/dev/null | tr -d '`' | sort -u || true)
  ALL_REFS=$(printf '%s\n%s' "$REFS" "$REFS2" | sort -u | grep -v '^$' || true)

  REF_COUNT=$(echo "$ALL_REFS" | grep -c . || echo 0)
  echo "  Referenced files: ${REF_COUNT}"

  # Check for deleted/missing files
  MISSING=""
  EXISTING_REFS=""
  REPO_REAL=$(cd "$(git rev-parse --show-toplevel)" && pwd -P)
  while IFS= read -r ref; do
    [ -z "$ref" ] && continue
    # Reject absolute paths and parent traversal
    case "$ref" in
      /*|*../*) MISSING="${MISSING}  - ${ref} (rejected: path traversal)\n"; continue ;;
    esac
    # Handle glob patterns (e.g., src/builtins/*.rs)
    if [[ "$ref" == *"*"* ]]; then
      expanded=$(compgen -G "$ref" 2>/dev/null | head -5 || true)
      if [ -z "$expanded" ]; then
        MISSING="${MISSING}  - ${ref} (glob pattern matches nothing)\n"
      else
        EXISTING_REFS="${EXISTING_REFS}${expanded}\n"
      fi
    elif [ -L "$ref" ]; then
      continue  # Skip symlinks
    elif [ ! -f "$ref" ] && [ ! -d "$ref" ]; then
      MISSING="${MISSING}  - ${ref}\n"
    else
      # Verify realpath stays within repo
      ref_real=$(cd "$(dirname "$ref")" 2>/dev/null && echo "$(pwd -P)/$(basename "$ref")") || continue
      case "$ref_real" in
        "${REPO_REAL}/"*) ;;
        *) continue ;;  # Skip out-of-repo paths
      esac
      EXISTING_REFS="${EXISTING_REFS}${ref}\n"
      REFERENCED_FILES="${REFERENCED_FILES}${ref}\n"
    fi
  done <<< "$ALL_REFS"

  if [ -n "$MISSING" ]; then
    echo "  ⚠ Missing/deleted files:"
    echo -e "$MISSING" | sed 's/^/    /'
    # Add as a finding
    missing_text=$(echo -e "$MISSING" | sed '/^$/d')
    ALL_FINDINGS=$(echo "$ALL_FINDINGS" | jq -c --arg kf "$kf_name" --arg missing "$missing_text" \
      '. + [{
        "severity": "important",
        "perspective": "knowledge-accuracy",
        "title": ("Missing source files referenced by " + $kf),
        "file": ("docs/knowledge/" + $kf),
        "snippet": "",
        "body": ("The following files are referenced but no longer exist. They may have been deleted or renamed:\n" + $missing + "\n\nUpdate the knowledge file to reflect current file locations.")
      }]')
  fi

  # Read the knowledge file content
  KF_CONTENT=$(cat "$kf")

  # Read existing referenced source files (truncate each to 6KB)
  SOURCE_CONTEXT=""
  while IFS= read -r ref; do
    [ -z "$ref" ] && continue
    if [ -f "$ref" ]; then
      SOURCE_CONTEXT="${SOURCE_CONTEXT}
--- source: ${ref} ---
$(head -c 6000 "$ref")
"
    fi
  done <<< "$(echo -e "$EXISTING_REFS" | sort -u)"

  # Skip LLM call if no source context
  if [ -z "$SOURCE_CONTEXT" ]; then
    echo "  No source files to compare against, skipping LLM check"
    continue
  fi

  # Call LLM to compare knowledge doc against actual source
  echo "  Comparing against source code..."

  PROMPT="You are auditing a knowledge documentation file for accuracy against the actual source code.

KNOWLEDGE FILE: ${kf_name}
${KF_CONTENT}

ACTUAL SOURCE CODE:
${SOURCE_CONTEXT}

=== TASK ===
Compare the knowledge file against the actual source code. Find:

1. **INACCURACIES**: Statements in the knowledge doc that contradict the actual code
   (wrong types, wrong function signatures, wrong behavior descriptions, wrong module structure)

2. **STALE CONTENT**: Descriptions of features, APIs, or patterns that have been
   refactored, renamed, or significantly changed in the source

3. **MISSING COVERAGE**: Important public APIs, types, or patterns in the source code
   that the knowledge doc should mention but doesn't

Focus on factual errors that would mislead someone using this knowledge doc.
Do NOT report style issues or minor wording preferences.

=== OUTPUT FORMAT ===
Return a JSON array. Each finding:
- \"severity\": \"critical\" (factual error) | \"important\" (stale/missing) | \"suggestion\" (minor gap)
- \"title\": one-sentence heading
- \"file\": \"docs/knowledge/${kf_name}\"
- \"snippet\": the specific incorrect or stale text from the knowledge doc (quote it exactly)
- \"body\": explanation of what's wrong and what the correct information is, citing the actual source code

If the knowledge file is accurate, return: []
Return ONLY valid JSON."

  echo "$PROMPT" > "$TMPDIR/accuracy_prompt.txt"
  RESPONSE=$(jq -n \
    --arg model "$MODEL" \
    --rawfile prompt "$TMPDIR/accuracy_prompt.txt" \
    '{
      model: $model,
      messages: [
        {role: "system", content: "You are a documentation accuracy auditor. Return findings as a JSON array only."},
        {role: "user", content: $prompt}
      ],
      temperature: 0.1
    }' | curl -s -X POST "$API_URL" \
      -H "Authorization: Bearer ${GITHUB_TOKEN}" \
      -H "Content-Type: application/json" \
      -d @- 2>/dev/null || echo '{"error": "API call failed"}')

  CONTENT=$(echo "$RESPONSE" | jq -r '.choices[0].message.content // empty' 2>/dev/null || true)

  TOTAL_ANALYSES=$((TOTAL_ANALYSES + 1))

  if [ -z "$CONTENT" ]; then
    ERROR_MSG=$(echo "$RESPONSE" | jq -r '.error // .message // "Unknown error"' 2>/dev/null || echo "Unknown error")
    echo "  API error: ${ERROR_MSG}"
    FAILED_ANALYSES=$((FAILED_ANALYSES + 1))
    continue
  fi

  CONTENT=$(echo "$CONTENT" | sed 's/^```json//; s/^```//; /^$/d')

  if ! echo "$CONTENT" | jq -e 'type == "array"' > /dev/null 2>&1; then
    echo "  Invalid JSON response, skipping"
    FAILED_ANALYSES=$((FAILED_ANALYSES + 1))
    continue
  fi

  # Sanitize and tag each finding
  TAGGED=$(echo "$CONTENT" | sanitize_model_output | jq -c '[.[] | . + {perspective: "knowledge-accuracy"}]')
  COUNT=$(echo "$TAGGED" | jq 'length')
  echo "  Findings: ${COUNT}"

  ALL_FINDINGS=$(echo "$ALL_FINDINGS" "$TAGGED" | jq -s 'add')
done

# ── Phase 3: Coverage Analysis ───────────────────────────────────────────
# Find important source files not covered by any knowledge doc.

echo ""
echo "=== Phase 3: Coverage Analysis ==="

REFERENCED_UNIQUE=$(echo -e "$REFERENCED_FILES" | sort -u | grep -v '^$' || true)

# Find source files with significant content (>100 lines) not referenced
UNCOVERED=""
UNCOVERED_COUNT=0
while IFS= read -r src; do
  [ -z "$src" ] && continue
  if ! echo "$REFERENCED_UNIQUE" | grep -qF "$src"; then
    line_count=$(wc -l < "$src" 2>/dev/null | tr -d ' ')
    if [ "$line_count" -gt 100 ]; then
      UNCOVERED="${UNCOVERED}  - ${src} (${line_count} lines)\n"
      UNCOVERED_COUNT=$((UNCOVERED_COUNT + 1))
    fi
  fi
done <<< "$SOURCE_FILES"

echo "Significant uncovered source files: ${UNCOVERED_COUNT}"

if [ "$UNCOVERED_COUNT" -gt 0 ]; then
  uncovered_text=$(echo -e "$UNCOVERED" | sed '/^$/d' | head -20)
  ALL_FINDINGS=$(echo "$ALL_FINDINGS" | jq -c --arg files "$uncovered_text" --arg count "$UNCOVERED_COUNT" \
    '. + [{
      "severity": "suggestion",
      "perspective": "knowledge-accuracy",
      "title": ($count + " significant source files have no knowledge documentation"),
      "file": "docs/knowledge/",
      "snippet": "",
      "body": ("The following source files are >100 lines and not referenced by any knowledge doc:\n" + $files + "\n\nConsider adding knowledge documentation for the most critical of these.")
    }]')
fi

# ── Phase 4: Post Results ────────────────────────────────────────────────

TOTAL=$(echo "$ALL_FINDINGS" | jq 'length' 2>/dev/null || echo 0)
echo ""
echo "=== Total findings: ${TOTAL} ==="
echo "Analysis stats: ${FAILED_ANALYSES}/${TOTAL_ANALYSES} failed"

# Fail if all analyses failed
if [ "$TOTAL_ANALYSES" -gt 0 ] && [ "$FAILED_ANALYSES" -eq "$TOTAL_ANALYSES" ]; then
  echo "::error::All ${TOTAL_ANALYSES} analyses failed — possible model/API issue"
  exit 1
fi

if [ "$TOTAL" -eq 0 ]; then
  echo "All knowledge files are accurate. Exiting."
  exit 0
fi

# Build issue body
ISSUE_BODY="## 📚 Knowledge Accuracy Audit

**Commit:** \`${COMMIT_SHA:0:8}\`
**Knowledge files checked:** ${#KNOWLEDGE_FILES[@]}
**Source files in repo:** ${SOURCE_COUNT}
**Total findings:** ${TOTAL}

---
"

# Group by severity
for severity in critical important suggestion; do
  sev_findings=$(echo "$ALL_FINDINGS" | jq -c --arg s "$severity" '[.[] | select(.severity == $s)]')
  sev_count=$(echo "$sev_findings" | jq 'length')
  [ "$sev_count" -eq 0 ] && continue

  case "$severity" in
    critical)   icon="🔴"; label="Critical — Factual Errors" ;;
    important)  icon="🟠"; label="Important — Stale or Missing" ;;
    suggestion) icon="🔵"; label="Suggestions — Coverage Gaps" ;;
  esac

  ISSUE_BODY="${ISSUE_BODY}
### ${icon} ${label} (${sev_count})

"

  findings_text=$(echo "$sev_findings" | jq -r '
    .[] |
    "#### " + .title + "\n" +
    "📁 `" + .file + "`\n" +
    .body + "\n" +
    (if .snippet != "" then "\n> " + (.snippet | gsub("\n"; "\n> ")) + "\n" else "" end) +
    "\n---\n"
  ' 2>/dev/null || true)

  ISSUE_BODY="${ISSUE_BODY}${findings_text}"
done

# Add provenance
ISSUE_BODY="${ISSUE_BODY}

<details>
<summary>Audit Provenance</summary>

- **Model:** ${MODEL}
- **Commit:** ${COMMIT_SHA}
- **Knowledge files:** ${#KNOWLEDGE_FILES[@]}
- **Source files scanned:** ${SOURCE_COUNT}
- **Uncovered significant files:** ${UNCOVERED_COUNT}

</details>"

# Post as rolling issue
AUDIT_LABEL="audit:knowledge-accuracy"
gh label create "$AUDIT_LABEL" --description "Knowledge documentation accuracy audit" --color "7057ff" --repo "$REPO" 2>/dev/null || true

EXISTING=$(gh issue list --repo "$REPO" --label "$AUDIT_LABEL" --state open --json number --jq '.[0].number' 2>/dev/null || true)

if [ -n "$EXISTING" ] && [ "$EXISTING" != "null" ]; then
  echo "Updating existing issue #${EXISTING}..."
  gh issue comment "$EXISTING" --repo "$REPO" --body "$ISSUE_BODY"
  echo "Updated: https://github.com/${REPO}/issues/${EXISTING}"
else
  echo "Creating new issue..."
  ISSUE_URL=$(gh issue create --repo "$REPO" \
    --title "📚 Knowledge Accuracy Audit" \
    --label "$AUDIT_LABEL" \
    --body "$ISSUE_BODY" 2>&1)
  echo "Created: ${ISSUE_URL}"
fi

echo "=== Knowledge accuracy audit complete ==="
