#!/usr/bin/env bash
# Copyright (c) Microsoft Corporation. All rights reserved.
# Licensed under the MIT License.
#
# Codebase audit using GitHub Models API.
# Discovers all relevant files for a topic, analyzes them with multiple
# perspectives, and posts findings as a GitHub issue.
#
# Usage: codebase-audit.sh <repo> <topic> [perspectives]
# Requires: GITHUB_TOKEN env var, jq, gh CLI

set -euo pipefail

REPO="$1"
TOPIC="$2"
PERSPECTIVES="${3:-auto}"

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

echo "=== Codebase Audit: ${TOPIC} ==="
echo "Repository: ${REPO}"
echo "Commit: ${COMMIT_SHA}"

# ── Phase 1: Deterministic File Discovery ──────────────────────────────
# Use knowledge files as the primary source of truth for topic→file mapping,
# then expand with grep. LLM only reranks/prunes.

echo ""
echo "=== Phase 1: File Discovery ==="

# 1a. Find relevant knowledge files by searching for topic keywords
echo "Searching knowledge files for topic relevance..."
TOPIC_WORDS=$(echo "$TOPIC" | tr '[:upper:]' '[:lower:]' | tr -cs '[:alnum:]' '\n' | sort -u)
RELEVANT_KNOWLEDGE=()
for kf in docs/knowledge/*.md; do
  kf_lower=$(tr '[:upper:]' '[:lower:]' < "$kf")
  match=0
  for word in $TOPIC_WORDS; do
    if [ ${#word} -ge 3 ] && echo "$kf_lower" | grep -q "$word"; then
      match=1
      break
    fi
  done
  if [ "$match" -eq 1 ]; then
    RELEVANT_KNOWLEDGE+=("$kf")
  fi
done

echo "Matched knowledge files: ${#RELEVANT_KNOWLEDGE[@]}"
for kf in "${RELEVANT_KNOWLEDGE[@]}"; do
  echo "  - $kf"
done

# 1b. Extract explicit file paths mentioned in knowledge files
echo "Extracting file paths from knowledge files..."
KNOWLEDGE_PATHS=()
for kf in "${RELEVANT_KNOWLEDGE[@]}"; do
  # Extract paths that look like src/..., bindings/..., tests/..., build.rs, Cargo.toml
  while IFS= read -r path; do
    if [ -f "$path" ] || [ -d "$path" ]; then
      KNOWLEDGE_PATHS+=("$path")
    fi
  done < <(grep -oE '(src|bindings|tests|examples|xtask)/[a-zA-Z0-9_/.-]+\.(rs|toml|yml|yaml)' "$kf" 2>/dev/null || true)
  # Also match bare filenames like build.rs, Cargo.toml
  while IFS= read -r path; do
    if [ -f "$path" ]; then
      KNOWLEDGE_PATHS+=("$path")
    fi
  done < <(grep -oE '(build\.rs|Cargo\.toml|Cargo\.lock)' "$kf" 2>/dev/null || true)
done

# Deduplicate
KNOWLEDGE_PATHS=($(printf '%s\n' "${KNOWLEDGE_PATHS[@]}" | sort -u))
echo "Paths from knowledge files: ${#KNOWLEDGE_PATHS[@]}"

# 1c. Expand via grep — search for topic keywords in source files
echo "Expanding via grep..."
GREP_PATHS=()
for word in $TOPIC_WORDS; do
  if [ ${#word} -ge 4 ]; then
    while IFS= read -r f; do
      GREP_PATHS+=("$f")
    done < <(grep -rl --include='*.rs' --include='*.toml' "$word" src/ bindings/ tests/ 2>/dev/null | head -30 || true)
  fi
done
GREP_PATHS=($(printf '%s\n' "${GREP_PATHS[@]}" 2>/dev/null | sort -u || true))
echo "Paths from grep: ${#GREP_PATHS[@]}"

# 1d. Merge all discovered paths
ALL_PATHS=($(printf '%s\n' "${KNOWLEDGE_PATHS[@]}" "${GREP_PATHS[@]}" 2>/dev/null | sort -u || true))
echo "Total candidate files: ${#ALL_PATHS[@]}"

# 1e. Let LLM rerank — identify the most relevant files for the topic
echo "LLM reranking for topic relevance..."
FILE_LIST=$(printf '%s\n' "${ALL_PATHS[@]}")

# Build repo tree for context (compact)
REPO_TREE=$(find src/ bindings/ tests/ examples/ -type f \( -name '*.rs' -o -name '*.toml' \) 2>/dev/null | grep -v target/ | sort)

DISCOVERY_PROMPT="You are analyzing a Rust codebase. Given the topic below, select the files most relevant to audit.

TOPIC: ${TOPIC}

CANDIDATE FILES (from knowledge docs and grep):
${FILE_LIST}

FULL REPO TREE (for context — you may add files not in candidates if critical):
${REPO_TREE}

Return a JSON object with:
- \"files\": array of file paths (most relevant first, max 30)
- \"rationale\": one sentence explaining your selection

Return ONLY valid JSON."

DISCOVERY_RESPONSE=$(echo "$DISCOVERY_PROMPT" > "$TMPDIR/discovery_prompt.txt" && jq -n \
  --arg model "$MODEL" \
  --rawfile prompt "$TMPDIR/discovery_prompt.txt" \
  '{
    model: $model,
    messages: [
      {role: "system", content: "You are a code analysis assistant. Return JSON only."},
      {role: "user", content: $prompt}
    ],
    temperature: 0.1
  }' | curl -s -X POST "$API_URL" \
    -H "Authorization: Bearer ${GITHUB_TOKEN}" \
    -H "Content-Type: application/json" \
    -d @- 2>/dev/null)

DISCOVERY_CONTENT=$(echo "$DISCOVERY_RESPONSE" | jq -r '.choices[0].message.content // empty' 2>/dev/null || true)
DISCOVERY_CONTENT=$(echo "$DISCOVERY_CONTENT" | sed 's/^```json//; s/^```//; /^$/d')

if echo "$DISCOVERY_CONTENT" | jq -e '.files' > /dev/null 2>&1; then
  AUDIT_FILES=($(echo "$DISCOVERY_CONTENT" | jq -r '.files[]' 2>/dev/null))
  RATIONALE=$(echo "$DISCOVERY_CONTENT" | jq -r '.rationale // "No rationale provided"' 2>/dev/null)
  echo "LLM selected ${#AUDIT_FILES[@]} files: ${RATIONALE}"
else
  echo "LLM reranking failed, using all candidates"
  AUDIT_FILES=("${ALL_PATHS[@]}")
fi

# Filter to files that actually exist and are within the repo
REPO_REAL=$(cd "$(git rev-parse --show-toplevel)" && pwd -P)
VALID_FILES=()
for f in "${AUDIT_FILES[@]}"; do
  # Reject absolute paths and parent traversal
  case "$f" in
    /*|*../*) continue ;;
  esac
  [ -L "$f" ] && continue  # Skip symlinks
  [ -f "$f" ] || continue
  # Verify realpath stays within repo
  f_real=$(cd "$(dirname "$f")" 2>/dev/null && echo "$(pwd -P)/$(basename "$f")") || continue
  case "$f_real" in
    "${REPO_REAL}/"*) VALID_FILES+=("$f") ;;
    *) echo "  Skipping out-of-repo path: $f" ;;
  esac
done
echo "Valid files to audit: ${#VALID_FILES[@]}"

if [ ${#VALID_FILES[@]} -eq 0 ]; then
  echo "No files found for topic '${TOPIC}'. Exiting."
  exit 0
fi

# ── Phase 2: Per-File Analysis ──────────────────────────────────────────
# Analyze each file individually to stay within context limits, then
# synthesize cross-file findings.

echo ""
echo "=== Phase 2: Per-File Analysis ==="

# Build knowledge context from relevant knowledge files
KNOWLEDGE_CTX=""
for kf in "${RELEVANT_KNOWLEDGE[@]}"; do
  kf_name=$(basename "$kf")
  KNOWLEDGE_CTX="${KNOWLEDGE_CTX}
--- ${kf_name} ---
$(head -c 3000 "$kf")
"
done

# Analyze files in clusters to reduce API calls
# Group by directory, max ~15KB per cluster
CLUSTER=""
CLUSTER_SIZE=0
CLUSTER_FILES=""
ALL_FINDINGS="[]"
CLUSTER_NUM=0

analyze_cluster() {
  local cluster_content="$1"
  local cluster_files="$2"
  local perspective="$3"
  local agent_file=".github/agents/${perspective}.agent.md"
  local agent_instructions=""
  if [ -f "$agent_file" ]; then
    agent_instructions=$(head -c 3000 "$agent_file")
  fi

  local display_name
  display_name=$(echo "$perspective" | sed 's/-/ /g' | awk '{for(i=1;i<=NF;i++) $i=toupper(substr($i,1,1)) substr($i,2)}1')

  local prompt="You are auditing existing code from the perspective of a ${display_name}.

AUDIT TOPIC: ${TOPIC}

Your agent instructions:
${agent_instructions}

Relevant knowledge:
${KNOWLEDGE_CTX}

FILES BEING AUDITED:
${cluster_content}

=== INSTRUCTIONS ===
Analyze these files for issues related to: ${TOPIC}
Focus on real bugs, security issues, correctness problems, and design concerns.
Do NOT report style/formatting issues.

For each finding, cite a specific CODE SNIPPET (the exact line of code, not a line number) so the finding can be located.

=== OUTPUT FORMAT ===
Return a JSON array. Each finding:
- \"severity\": \"critical\" | \"important\" | \"suggestion\"
- \"title\": one-sentence heading
- \"file\": exact file path
- \"snippet\": the exact code line(s) where the issue is (copy from the source)
- \"body\": 2-4 sentence explanation

If no issues found, return: []
Return ONLY valid JSON."

  local response
  echo "$prompt" > "$TMPDIR/analysis_prompt.txt"
  response=$(jq -n \
    --arg model "$MODEL" \
    --rawfile prompt "$TMPDIR/analysis_prompt.txt" \
    '{
      model: $model,
      messages: [
        {role: "system", content: "You are a code auditor. Return findings as a JSON array only."},
        {role: "user", content: $prompt}
      ],
      temperature: 0.1
    }' | curl -s -X POST "$API_URL" \
      -H "Authorization: Bearer ${GITHUB_TOKEN}" \
      -H "Content-Type: application/json" \
      -d @- 2>/dev/null)

  local content
  content=$(echo "$response" | jq -r '.choices[0].message.content // empty' 2>/dev/null || true)
  content=$(echo "$content" | sed 's/^```json//; s/^```//; /^$/d')

  if echo "$content" | jq -e 'type == "array"' > /dev/null 2>&1; then
    # Sanitize and add perspective tag to each finding
    echo "$content" | sanitize_model_output | jq -c --arg p "$perspective" '[.[] | . + {perspective: $p}]'
  else
    echo "  Analysis failed or returned invalid JSON" >&2
    echo "[]"
    return 1
  fi
}

# Build file clusters (~15KB each)
CLUSTERS=()
CLUSTER_FILE_LISTS=()
current_cluster=""
current_files=""
current_size=0

for f in "${VALID_FILES[@]}"; do
  file_size=$(wc -c < "$f" 2>/dev/null || echo 0)

  # If adding this file exceeds 15KB, start a new cluster
  if [ $current_size -gt 0 ] && [ $((current_size + file_size)) -gt 15000 ]; then
    CLUSTERS+=("$current_cluster")
    CLUSTER_FILE_LISTS+=("$current_files")
    current_cluster=""
    current_files=""
    current_size=0
  fi

  # Add file to current cluster (truncate individual files at 8KB)
  file_content=$(head -c 8000 "$f")
  current_cluster="${current_cluster}
--- file: ${f} ---
${file_content}
"
  current_files="${current_files}${f} "
  current_size=$((current_size + ${#file_content}))
done

# Don't forget the last cluster
if [ -n "$current_cluster" ]; then
  CLUSTERS+=("$current_cluster")
  CLUSTER_FILE_LISTS+=("$current_files")
fi

echo "Organized into ${#CLUSTERS[@]} cluster(s)"

# ── Phase 2b: Perspective Selection ─────────────────────────────────────

if [ "$PERSPECTIVES" = "auto" ]; then
  # Default floor: always include these for a security-critical codebase
  PERSPECTIVES="security-auditor,reliability-engineer"

  # Add topic-specific perspectives
  topic_lower=$(echo "$TOPIC" | tr '[:upper:]' '[:lower:]')
  case "$topic_lower" in
    *error*|*panic*|*unwrap*|*crash*)
      PERSPECTIVES="${PERSPECTIVES},semantics-expert" ;;
    *security*|*safety*|*attack*|*inject*)
      PERSPECTIVES="${PERSPECTIVES},red-teamer" ;;
    *ffi*|*binding*|*api*)
      PERSPECTIVES="${PERSPECTIVES},architect,api-steward" ;;
    *performance*|*speed*|*memory*|*allocat*)
      PERSPECTIVES="${PERSPECTIVES},performance-engineer" ;;
    *test*|*coverage*|*conformance*)
      PERSPECTIVES="${PERSPECTIVES},test-engineer" ;;
    *undefined*|*value*|*rego*|*semantic*)
      PERSPECTIVES="${PERSPECTIVES},semantics-expert" ;;
    *compil*|*interpret*|*vm*|*rvm*)
      PERSPECTIVES="${PERSPECTIVES},semantics-expert,performance-engineer" ;;
  esac

  # Deduplicate
  PERSPECTIVES=$(echo "$PERSPECTIVES" | tr ',' '\n' | sort -u | tr '\n' ',' | sed 's/,$//')
fi

echo "Perspectives: ${PERSPECTIVES}"

# ── Phase 3: Run Analysis ───────────────────────────────────────────────

echo ""
echo "=== Phase 3: Perspective Analysis ==="

ALL_FINDINGS="[]"

for perspective in $(echo "$PERSPECTIVES" | tr ',' ' '); do
  display_name=$(echo "$perspective" | sed 's/-/ /g' | awk '{for(i=1;i<=NF;i++) $i=toupper(substr($i,1,1)) substr($i,2)}1')
  echo "--- Analyzing: ${display_name} ---"

  perspective_findings="[]"
  cluster_idx=0

  for cluster_content in "${CLUSTERS[@]}"; do
    cluster_idx=$((cluster_idx + 1))
    TOTAL_ANALYSES=$((TOTAL_ANALYSES + 1))
    echo "  Cluster ${cluster_idx}/${#CLUSTERS[@]}..."
    findings=$(analyze_cluster "$cluster_content" "${CLUSTER_FILE_LISTS[$((cluster_idx-1))]}" "$perspective") || {
      FAILED_ANALYSES=$((FAILED_ANALYSES + 1))
      continue
    }
    count=$(echo "$findings" | jq 'length' 2>/dev/null || echo 0)
    echo "  Found ${count} finding(s)"

    # Merge into perspective findings
    perspective_findings=$(echo "$perspective_findings" "$findings" | jq -s 'add')
  done

  pcount=$(echo "$perspective_findings" | jq 'length' 2>/dev/null || echo 0)
  echo "  ${display_name} total: ${pcount} finding(s)"

  ALL_FINDINGS=$(echo "$ALL_FINDINGS" "$perspective_findings" | jq -s 'add')
done

TOTAL=$(echo "$ALL_FINDINGS" | jq 'length' 2>/dev/null || echo 0)
echo ""
echo "Total findings across all perspectives: ${TOTAL}"
echo "Analysis stats: ${FAILED_ANALYSES}/${TOTAL_ANALYSES} failed"

# Fail if all analyses failed
if [ "$TOTAL_ANALYSES" -gt 0 ] && [ "$FAILED_ANALYSES" -eq "$TOTAL_ANALYSES" ]; then
  echo "::error::All ${TOTAL_ANALYSES} analyses failed — possible model/API issue"
  exit 1
fi

if [ "$TOTAL" -eq 0 ]; then
  echo "No findings. Exiting."
  exit 0
fi

# ── Phase 4: Post Results as GitHub Issue ───────────────────────────────

echo ""
echo "=== Phase 4: Posting Results ==="

# Build issue body
ISSUE_BODY="## 🔍 Codebase Audit: ${TOPIC}

**Commit:** \`${COMMIT_SHA:0:8}\`
**Perspectives:** ${PERSPECTIVES}
**Files audited:** ${#VALID_FILES[@]}
**Total findings:** ${TOTAL}

---
"

# Group findings by perspective
for perspective in $(echo "$PERSPECTIVES" | tr ',' ' '); do
  display_name=$(echo "$perspective" | sed 's/-/ /g' | awk '{for(i=1;i<=NF;i++) $i=toupper(substr($i,1,1)) substr($i,2)}1')
  case "$perspective" in
    red-teamer)              emoji="🔴" ;;
    security-auditor)        emoji="🔒" ;;
    reliability-engineer)    emoji="⚙️" ;;
    test-engineer)           emoji="🧪" ;;
    semantics-expert)        emoji="📐" ;;
    performance-engineer)    emoji="⚡" ;;
    architect)               emoji="🏗️" ;;
    api-steward)             emoji="📡" ;;
    *)                       emoji="🔍" ;;
  esac

  p_findings=$(echo "$ALL_FINDINGS" | jq -c --arg p "$perspective" '[.[] | select(.perspective == $p)]')
  p_count=$(echo "$p_findings" | jq 'length' 2>/dev/null || echo 0)

  if [ "$p_count" -eq 0 ]; then
    continue
  fi

  ISSUE_BODY="${ISSUE_BODY}
### ${emoji} ${display_name} (${p_count} finding(s))

"

  # Add each finding (already sanitized by sanitize_model_output)
  findings_text=$(echo "$p_findings" | jq -r '
    .[] |
    (if .severity == "critical" then "🔴 **Critical**"
     elif .severity == "important" then "🟠 **Important**"
     else "🔵 **Suggestion**" end) +
    ": " + .title + "\n" +
    .body + "\n" +
    (if .file then "📁 `" + .file + "`" else "" end) +
    (if .snippet then "\n```rust\n" + .snippet + "\n```" else "" end) +
    "\n"
  ' 2>/dev/null || true)

  ISSUE_BODY="${ISSUE_BODY}${findings_text}
"
done

# Add provenance section
ISSUE_BODY="${ISSUE_BODY}
---

<details>
<summary>Audit Provenance</summary>

- **Model:** ${MODEL}
- **Commit:** ${COMMIT_SHA}
- **Knowledge files used:** $(printf '%s, ' "${RELEVANT_KNOWLEDGE[@]}" | sed 's/, $//')
- **Files audited:**
$(printf '  - %s\n' "${VALID_FILES[@]}")

</details>"

# Check for existing open audit issue with same topic label
AUDIT_LABEL="audit:${TOPIC// /-}"
# Truncate label to 50 chars (GitHub limit)
AUDIT_LABEL="${AUDIT_LABEL:0:50}"

# Ensure the label exists
gh label create "$AUDIT_LABEL" --description "Codebase audit: ${TOPIC}" --color "7057ff" --repo "$REPO" 2>/dev/null || true

# Check for existing open issue
EXISTING=$(gh issue list --repo "$REPO" --label "$AUDIT_LABEL" --state open --json number --jq '.[0].number' 2>/dev/null || true)

if [ -n "$EXISTING" ] && [ "$EXISTING" != "null" ]; then
  echo "Updating existing issue #${EXISTING}..."
  gh issue comment "$EXISTING" --repo "$REPO" --body "$ISSUE_BODY"
  echo "Updated issue: https://github.com/${REPO}/issues/${EXISTING}"
else
  echo "Creating new issue..."
  ISSUE_URL=$(gh issue create --repo "$REPO" \
    --title "🔍 Codebase Audit: ${TOPIC}" \
    --label "$AUDIT_LABEL" \
    --body "$ISSUE_BODY" 2>&1)
  echo "Created: ${ISSUE_URL}"
fi

echo "=== Audit complete ==="
