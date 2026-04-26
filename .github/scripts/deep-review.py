#!/usr/bin/env python3
# Copyright (c) Microsoft Corporation. All rights reserved.
# Licensed under the MIT License.
#
# Agentic deep review using GitHub Models API with function calling.
# Each perspective agent gets read-only tools to explore the codebase,
# enabling cross-file reasoning that single-shot reviews cannot do.
#
# Usage: deep-review.py <repo> <pr_number>
# Requires: GITHUB_TOKEN env var

import json
import os
import re
import subprocess
import sys
import time
import glob as globmod
import tempfile

# ── Configuration ────────────────────────────────────────────────────────

if len(sys.argv) != 3:
    print("::error::Usage: deep-review.py <repo> <pr_number>", file=sys.stderr)
    sys.exit(1)

REPO = sys.argv[1]
PR_NUMBER = sys.argv[2]
MODEL = os.environ.get("DEEP_REVIEW_MODEL", "openai/gpt-4.1-mini")
API_URL = "https://models.github.ai/inference/chat/completions"
MAX_TURNS = 15          # Max conversation turns per perspective
MAX_TOOL_CALLS = 20     # Total tool calls per perspective
MAX_FILE_BYTES = 15000  # Max bytes returned by read_file
MAX_GREP_RESULTS = 20   # Max grep matches returned
REPO_ROOT = os.getcwd()

# Validate inputs
if not re.match(r'^[A-Za-z0-9._-]+/[A-Za-z0-9._-]+$', REPO):
    print(f"::error::Invalid repo format: '{REPO}'", file=sys.stderr)
    sys.exit(1)
if not re.match(r'^[0-9]+$', PR_NUMBER):
    print(f"::error::Invalid PR number: '{PR_NUMBER}'", file=sys.stderr)
    sys.exit(1)

# ── Tool Definitions ─────────────────────────────────────────────────────

TOOLS = [
    {
        "type": "function",
        "function": {
            "name": "read_file",
            "description": "Read contents of a file in the repository. Returns the file text with line numbers.",
            "parameters": {
                "type": "object",
                "properties": {
                    "path": {"type": "string", "description": "Relative path from repo root"},
                    "start_line": {"type": "integer", "description": "Start line (1-indexed, optional)"},
                    "end_line": {"type": "integer", "description": "End line (inclusive, optional)"},
                },
                "required": ["path"],
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "grep_code",
            "description": "Search for a regex pattern in repository files. Returns matching lines with file paths and line numbers.",
            "parameters": {
                "type": "object",
                "properties": {
                    "pattern": {"type": "string", "description": "Regex pattern to search for"},
                    "file_glob": {"type": "string", "description": "File glob pattern (e.g. '*.rs', 'src/**/*.rs'). Defaults to all files."},
                    "max_results": {"type": "integer", "description": "Max results (default 20, max 30)"},
                },
                "required": ["pattern"],
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "list_files",
            "description": "List files matching a glob pattern in the repository.",
            "parameters": {
                "type": "object",
                "properties": {
                    "pattern": {"type": "string", "description": "Glob pattern (e.g. 'src/**/*.rs', '.github/scripts/*')"},
                },
                "required": ["pattern"],
            },
        },
    },
    {
        "type": "function",
        "function": {
            "name": "submit_review",
            "description": "Submit your final review findings. Call this when you have completed your investigation.",
            "parameters": {
                "type": "object",
                "properties": {
                    "findings": {
                        "type": "array",
                        "description": "Array of findings from your review",
                        "items": {
                            "type": "object",
                            "properties": {
                                "severity": {"type": "string", "enum": ["critical", "important", "suggestion"]},
                                "title": {"type": "string", "description": "One-sentence heading"},
                                "body": {"type": "string", "description": "2-4 sentence explanation"},
                                "file": {"type": "string", "description": "File path (if applicable)"},
                                "line": {"type": "integer", "description": "Line number (if applicable)"},
                            },
                            "required": ["severity", "title", "body"],
                        },
                    },
                },
                "required": ["findings"],
            },
        },
    },
]


# ── Path Security ────────────────────────────────────────────────────────

DENIED_PREFIXES = (".git/", ".git\\", ".svn/", ".hg/")

def safe_resolve(path: str) -> str | None:
    """Resolve a path safely within the repo root. Returns None if unsafe."""
    joined = os.path.join(REPO_ROOT, path)
    # Deny symlinks before resolving (check the original path)
    if os.path.islink(joined):
        return None
    # Normalize and resolve
    resolved = os.path.realpath(joined)
    # Must share repo root as common ancestor
    try:
        common = os.path.commonpath([os.path.realpath(REPO_ROOT), resolved])
    except ValueError:
        return None
    if common != os.path.realpath(REPO_ROOT):
        return None
    # Deny .git and other VCS directories
    rel = os.path.relpath(resolved, os.path.realpath(REPO_ROOT))
    for prefix in DENIED_PREFIXES:
        if rel.startswith(prefix) or rel == prefix.rstrip("/"):
            return None
    return resolved


# ── Tool Implementations ─────────────────────────────────────────────────

def tool_read_file(args: dict) -> str:
    path = args.get("path", "")
    resolved = safe_resolve(path)
    if not resolved:
        return f"Error: path '{path}' is outside the repository or denied"
    if not os.path.isfile(resolved):
        return f"Error: file '{path}' not found"
    try:
        with open(resolved, "r", errors="replace") as f:
            lines = f.readlines()
    except Exception as e:
        return f"Error reading '{path}': {e}"

    start = args.get("start_line", 1)
    end = args.get("end_line", len(lines))
    start = max(1, min(start, len(lines)))
    end = max(start, min(end, len(lines)))

    selected = lines[start - 1 : end]
    content = ""
    total_bytes = 0
    for i, line in enumerate(selected, start=start):
        content += f"{i}. {line}"
        total_bytes += len(line)
        if total_bytes > MAX_FILE_BYTES:
            content += f"\n... truncated at {MAX_FILE_BYTES} bytes (file has {len(lines)} lines total)"
            break
    return content


def tool_grep_code(args: dict) -> str:
    pattern = args.get("pattern", "")
    file_glob = args.get("file_glob", "**/*")
    max_results = min(args.get("max_results", 20), MAX_GREP_RESULTS)

    # Use ripgrep if available (faster, respects .gitignore), fall back to grep
    try:
        cmd = ["rg", "-n", "--no-heading", "--max-count", str(max_results),
               "--max-filesize", "100K", "-g", file_glob, "--", pattern, "."]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=10,
                                cwd=REPO_ROOT)
        lines = result.stdout.strip().split("\n") if result.stdout.strip() else []
    except FileNotFoundError:
        # Fallback to grep (doesn't support ** globs — convert to simple pattern)
        try:
            include_glob = file_glob.replace("**/", "")  # grep --include doesn't support **
            cmd = ["grep", "-rn", "--include", include_glob, "-m", str(max_results), "--", pattern, "."]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=10,
                                    cwd=REPO_ROOT)
            lines = result.stdout.strip().split("\n") if result.stdout.strip() else []
        except Exception as e:
            return f"Error: grep failed: {e}"

    # Filter out .git paths from results
    filtered = [l for l in lines if not any(p in l for p in DENIED_PREFIXES)]
    if not filtered:
        return "No matches found"
    if len(filtered) > max_results:
        filtered = filtered[:max_results]
    return "\n".join(filtered)


def tool_list_files(args: dict) -> str:
    pattern = args.get("pattern", "**/*")
    # Reject absolute paths and parent traversal
    if os.path.isabs(pattern) or ".." in pattern.split(os.sep):
        return "Error: pattern must be relative and cannot contain '..'"
    repo_real = os.path.realpath(REPO_ROOT)
    matches = []
    for path in globmod.glob(os.path.join(REPO_ROOT, pattern), recursive=True):
        # Skip symlinks
        if os.path.islink(path):
            continue
        real = os.path.realpath(path)
        if not real.startswith(repo_real + os.sep):
            continue
        if os.path.isfile(path):
            rel = os.path.relpath(path, REPO_ROOT)
            if not any(rel.startswith(p) for p in DENIED_PREFIXES):
                matches.append(rel)
    matches.sort()
    if not matches:
        return "No files matched"
    if len(matches) > 200:
        return "\n".join(matches[:200]) + f"\n... and {len(matches) - 200} more"
    return "\n".join(matches)


TOOL_DISPATCH = {
    "read_file": tool_read_file,
    "grep_code": tool_grep_code,
    "list_files": tool_list_files,
}


# ── API Client ───────────────────────────────────────────────────────────

def call_model(messages: list, token: str) -> dict:
    """Call GitHub Models API with function calling."""
    import urllib.request

    payload = json.dumps({
        "model": MODEL,
        "messages": messages,
        "tools": TOOLS,
        "temperature": 0.1,
    }).encode()

    req = urllib.request.Request(
        API_URL,
        data=payload,
        headers={
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json",
        },
    )

    for attempt in range(3):
        try:
            with urllib.request.urlopen(req, timeout=180) as resp:
                return json.loads(resp.read())
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt < 2:
                wait = 2 ** (attempt + 1)
                print(f"    Rate limited, retrying in {wait}s...")
                time.sleep(wait)
                continue
            body = e.read().decode(errors="replace")[:500]
            return {"error": f"HTTP {e.code}: {body}"}
        except Exception as e:
            if attempt < 2:
                time.sleep(2)
                continue
            return {"error": str(e)}

    return {"error": "Max retries exceeded"}


# ── Sanitization ─────────────────────────────────────────────────────────

def sanitize_text(text: str) -> str:
    """Defang @mentions and neutralize URLs to prevent notification spam and phishing."""
    text = re.sub(r'@([A-Za-z0-9_-])', lambda m: '@\u200d' + m.group(1), text)
    text = re.sub(r'(https?)://', lambda m: m.group(1) + '[://]', text)
    return text


def sanitize_findings(findings: list) -> list:
    sanitized = []
    for f in findings:
        if not isinstance(f, dict):
            continue
        f["title"] = sanitize_text(f.get("title", ""))
        f["body"] = sanitize_text(f.get("body", ""))
        sanitized.append(f)
    return sanitized


# ── Perspective Agent ────────────────────────────────────────────────────

def run_perspective(perspective: str, system_prompt: str, seed_context: str,
                    valid_anchors: set, api_token: str) -> list:
    """Run one perspective agent. Returns list of findings."""
    print(f"--- Deep review: {perspective} ---")

    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": seed_context},
    ]

    total_tool_calls = 0
    recent_calls = []  # Track last N calls to detect loops

    for turn in range(MAX_TURNS):
        response = call_model(messages, api_token)

        if "error" in response:
            print(f"  API error: {response['error']}")
            return None

        choice = response.get("choices", [{}])[0].get("message", {})

        # Check for tool calls
        tool_calls = choice.get("tool_calls", [])

        if not tool_calls:
            # No tool calls — check if submit_review was called or parse final text
            content = choice.get("content", "")
            if content:
                # Try to parse as JSON findings (fallback for models that return text)
                try:
                    findings = json.loads(content)
                    if isinstance(findings, list):
                        print(f"  Completed with {len(findings)} finding(s) via text response")
                        return sanitize_findings(findings)
                except (json.JSONDecodeError, TypeError):
                    pass
                print(f"  Completed with non-JSON response (no findings)")
            return []

        # Process tool calls
        messages.append(choice)  # assistant message with tool_calls

        for tc in tool_calls:
            try:
                func_name = tc["function"]["name"]
                call_id = tc["id"]
            except (KeyError, TypeError):
                continue  # Skip malformed tool calls

            try:
                args = json.loads(tc["function"]["arguments"])
            except (json.JSONDecodeError, KeyError, TypeError):
                messages.append({
                    "role": "tool", "tool_call_id": call_id,
                    "content": "Error: invalid JSON arguments",
                })
                continue

            total_tool_calls += 1

            # Check for submit_review (terminal tool)
            if func_name == "submit_review":
                findings = args.get("findings", [])
                if not isinstance(findings, list):
                    findings = []
                # Validate findings against valid diff anchors
                for f in findings:
                    if not isinstance(f, dict):
                        continue
                    if f.get("file") and f.get("line"):
                        anchor = f"{f['file']}:{f['line']}"
                        if anchor not in valid_anchors:
                            f.pop("line", None)  # Demote to unanchored
                print(f"  Submitted {len(findings)} finding(s) after {total_tool_calls} tool calls")
                return sanitize_findings(findings)

            # Budget enforcement
            if total_tool_calls > MAX_TOOL_CALLS:
                messages.append({
                    "role": "tool", "tool_call_id": call_id,
                    "content": "Error: tool call budget exhausted. Call submit_review now with your findings.",
                })
                continue

            # Loop detection
            call_sig = f"{func_name}:{json.dumps(args, sort_keys=True)}"
            if call_sig in recent_calls[-5:]:
                messages.append({
                    "role": "tool", "tool_call_id": call_id,
                    "content": "Error: duplicate tool call detected. Move on to a different investigation or call submit_review.",
                })
                continue
            recent_calls.append(call_sig)

            # Execute tool
            handler = TOOL_DISPATCH.get(func_name)
            if not handler:
                messages.append({
                    "role": "tool", "tool_call_id": call_id,
                    "content": f"Error: unknown tool '{func_name}'",
                })
                continue

            print(f"    [{total_tool_calls}] {func_name}({json.dumps(args)[:100]})")
            result = handler(args)

            messages.append({
                "role": "tool",
                "tool_call_id": call_id,
                "content": result[:MAX_FILE_BYTES],
            })

    print(f"  Max turns reached ({MAX_TURNS})")
    return None


# ── Main ─────────────────────────────────────────────────────────────────

def main():
    # Save token and scrub from environment
    api_token = os.environ.pop("GITHUB_TOKEN", "")
    os.environ.pop("GH_TOKEN", None)
    if not api_token:
        print("::error::GITHUB_TOKEN not set", file=sys.stderr)
        sys.exit(1)

    print(f"=== Deep Review for {REPO}#{PR_NUMBER} ===")
    print(f"Model: {MODEL}")

    # Fetch PR metadata using gh CLI (temporarily re-inject token)
    os.environ["GH_TOKEN"] = api_token
    try:
        pr_data = json.loads(subprocess.run(
            ["gh", "api", f"repos/{REPO}/pulls/{PR_NUMBER}"],
            capture_output=True, text=True, check=True,
        ).stdout)
        head_sha = pr_data["head"]["sha"]

        changed_files_raw = subprocess.run(
            ["gh", "api", f"repos/{REPO}/pulls/{PR_NUMBER}/files",
             "--paginate", "--jq", ".[].filename"],
            capture_output=True, text=True, check=True,
        ).stdout.strip().split("\n")

        # Fetch diff
        diff_result = subprocess.run(
            ["gh", "api", f"repos/{REPO}/pulls/{PR_NUMBER}",
             "-H", "Accept: application/vnd.github.v3.diff"],
            capture_output=True, text=True, check=True,
        )
        full_diff = diff_result.stdout
    except subprocess.CalledProcessError as e:
        print(f"::error::Failed to fetch PR data: {e.stderr}", file=sys.stderr)
        sys.exit(1)
    finally:
        os.environ.pop("GH_TOKEN", None)

    print(f"Head SHA: {head_sha}")
    print(f"Changed files: {len(changed_files_raw)}")
    print(f"Diff size: {len(full_diff)} bytes")

    # Parse valid diff anchors for inline comment validation
    valid_anchors = set()
    current_file = None
    current_line = 0
    for raw_line in full_diff.split("\n"):
        if raw_line.startswith("+++ b/"):
            current_file = raw_line[6:]
        elif raw_line.startswith("@@ "):
            # Parse hunk header: @@ -old,count +new,count @@
            m = re.search(r'\+(\d+)', raw_line)
            if m:
                current_line = int(m.group(1))
        elif current_file:
            if raw_line.startswith("\\"):
                pass  # Diff metadata like "\ No newline at end of file"
            elif raw_line.startswith("+"):
                valid_anchors.add(f"{current_file}:{current_line}")
                current_line += 1
            elif raw_line.startswith("-"):
                pass  # Deleted lines don't advance new-side counter
            else:
                current_line += 1

    print(f"Valid anchors: {len(valid_anchors)}")

    # Determine perspectives (same logic as quick mode)
    perspectives = ["reliability-engineer", "test-engineer"]
    files_str = "\n".join(changed_files_raw)
    if re.search(r'\.(yml|yaml|sh)$', files_str, re.MULTILINE) or ".github/" in files_str:
        perspectives.append("ci-cd-security")
    if re.search(r'src/builtins/', files_str):
        perspectives.extend(["semantics-expert", "red-teamer"])
    if re.search(r'bindings/|src/.*ffi', files_str):
        perspectives.extend(["architect", "api-steward"])
    if re.search(r'Cargo\.(toml|lock)', files_str):
        perspectives.extend(["security-auditor", "architect"])
    if re.search(r'src/(interpreter|rvm|compiler|scheduler)', files_str):
        perspectives.extend(["semantics-expert", "performance-engineer"])
    perspectives = list(dict.fromkeys(perspectives))  # Deduplicate preserving order
    print(f"Perspectives: {', '.join(perspectives)}")

    # Don't embed full knowledge files in system prompt — agent can read them via tools.
    # Just mention they exist so the agent knows to check them if relevant.
    knowledge_files = [
        "docs/knowledge/builtin-system.md",
        "docs/knowledge/value-semantics.md",
        "docs/knowledge/policy-evaluation-security.md",
        "docs/knowledge/ffi-boundary.md",
        "docs/knowledge/workflow-security.md",
    ]
    knowledge_hint = "Knowledge files available in docs/knowledge/: " + ", ".join(
        os.path.basename(kf) for kf in knowledge_files if os.path.isfile(kf)
    )

    # Prepare seed context — just the changed files list; the agent uses tools to read specifics.
    # Don't embed the diff in the prompt to save context for tool results.
    seed_context = f"""You are performing a deep review of PR #{PR_NUMBER} in {REPO}.

## Changed Files ({len(changed_files_raw)} files)
{files_str}

## Instructions
1. Focus on the most important changed files first — read them with read_file.
2. Be selective: read 5-8 key files, not every file in the PR.
3. Use grep_code to check if patterns are applied consistently across related files.
4. Cross-reference: if you find a pattern in one file, check if sibling files follow it.
5. Focus on: correctness, security, consistency, error handling, edge cases.
6. When done, call submit_review with your findings.

Budget: you have ~{MAX_TOOL_CALLS} tool calls. Prioritize investigation over exhaustive reading.
Only report genuine issues. Do NOT flag documentation text as having the problems it describes.
For inline comments, use file paths and line numbers from the actual changed code only."""

    # Run each perspective
    all_findings = []
    failed = 0

    for perspective in perspectives:
        # Load agent definition
        agent_file = f".github/agents/{perspective}.agent.md"
        agent_instructions = ""
        if os.path.isfile(agent_file):
            with open(agent_file, "r") as f:
                agent_instructions = f.read()

        system_prompt = f"""You are a {perspective.replace('-', ' ')} performing a deep code review.
You have access to tools to read files, search code, and list files in the repository.
Use these tools to investigate thoroughly — don't just look at the diff.

{agent_instructions}

{knowledge_hint}

When you have completed your investigation, call submit_review with your findings as a JSON array.
Each finding needs: severity (critical/important/suggestion), title, body, and optionally file and line."""

        findings = run_perspective(perspective, system_prompt, seed_context,
                                   valid_anchors, api_token)
        if findings is None:
            failed += 1
            continue

        for f in findings:
            f["perspective"] = perspective
        all_findings.extend(findings)

    print(f"\n=== Deep review complete: {len(all_findings)} total findings, {failed}/{len(perspectives)} perspectives failed ===")

    if failed > 0:
        print(f"::warning::{failed} of {len(perspectives)} perspectives failed")

    if not all_findings:
        if failed == len(perspectives):
            print("::error::All perspectives failed")
            sys.exit(1)
        if failed > 0:
            print("::warning::No findings, but some perspectives failed — results may be incomplete")
        else:
            print("No findings from any perspective.")
        sys.exit(0)

    # Post results as PR review — re-inject token for posting only
    os.environ["GH_TOKEN"] = api_token

    # Group by perspective
    by_perspective = {}
    for f in all_findings:
        p = f.get("perspective", "unknown")
        by_perspective.setdefault(p, []).append(f)

    EMOJI_MAP = {
        "red-teamer": "🔴", "security-auditor": "🔒",
        "reliability-engineer": "⚙️", "test-engineer": "🧪",
        "semantics-expert": "📐", "performance-engineer": "⚡",
        "architect": "🏗️", "api-steward": "📡",
        "ci-cd-security": "🛡️",
    }

    for perspective, findings in by_perspective.items():
        emoji = EMOJI_MAP.get(perspective, "🔍")
        display = perspective.replace("-", " ").title()

        # Build review body
        body = f"{emoji} **{display}** (Deep Review) — {len(findings)} finding(s)"

        # Separate anchored vs unanchored
        inline_comments = []
        for f in findings:
            sev_icon = {"critical": "🔴", "important": "🟠", "suggestion": "🔵"}.get(f["severity"], "⚪")
            comment_body = f"**{sev_icon} {f['severity'].title()}**: {f['title']}\n\n{f['body']}"

            if f.get("file") and f.get("line"):
                anchor = f"{f['file']}:{f['line']}"
                if anchor in valid_anchors:
                    inline_comments.append({
                        "path": f["file"],
                        "line": f["line"],
                        "side": "RIGHT",
                        "body": comment_body,
                    })
                    continue
            # Unanchored — add to body
            body += f"\n\n{comment_body}"
            if f.get("file"):
                body += f"\n📁 `{f['file']}`"
                if f.get("line"):
                    body += f":{f['line']}"

        # Post review
        review_payload = json.dumps({
            "commit_id": head_sha,
            "body": body,
            "event": "COMMENT",
            "comments": inline_comments,
        })

        try:
            result = subprocess.run(
                ["gh", "api", f"repos/{REPO}/pulls/{PR_NUMBER}/reviews",
                 "--input", "-"],
                input=review_payload, capture_output=True, text=True, check=True,
            )
            review_id = json.loads(result.stdout).get("id", "?")
            print(f"  Posted review {review_id} for {perspective}")
        except subprocess.CalledProcessError:
            # Retry without inline comments
            review_payload = json.dumps({
                "commit_id": head_sha,
                "body": body,
                "event": "COMMENT",
                "comments": [],
            })
            try:
                subprocess.run(
                    ["gh", "api", f"repos/{REPO}/pulls/{PR_NUMBER}/reviews",
                     "--input", "-"],
                    input=review_payload, capture_output=True, text=True, check=True,
                )
                print(f"  Posted body-only review for {perspective}")
            except subprocess.CalledProcessError as e:
                print(f"  Failed to post review for {perspective}: {e.stderr[:200]}")

    os.environ.pop("GH_TOKEN", None)


if __name__ == "__main__":
    main()
