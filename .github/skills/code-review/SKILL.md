---
name: code-review
description: >-
  Fast multi-perspective code review for regorus. Use for everyday code reviews.
  Reviews from 3 perspectives with calibrated severity and noise filtering.
allowed-tools: shell
---

# Code Review Skill

## What You're Protecting

A bug in regorus can mean `allow` when the answer should be `deny`.
Review this diff to find bugs that matter at that severity level.

Key constraints (details in copilot-instructions.md):
- **Undefined ≠ false** — silent wrong policy results
- **Panics across FFI** → permanent engine poisoning (process-wide)
- **9 binding targets** → any API change has 9x blast radius
- **Dual execution paths** — interpreter and RVM must agree
- **`enforce_limit()`** required in accumulation loops

**Do not** run cargo, clippy, tests, or build commands. Diff-review only.

## Step 1: Get the Diff

```bash
BASE=$(git merge-base upstream/main HEAD 2>/dev/null \
    || git merge-base origin/main HEAD 2>/dev/null)
if [ -z "$BASE" ]; then
  echo "ERROR: Cannot find upstream/main or origin/main. Cannot determine review scope."
  exit 1
fi
echo "Reviewing changes since: $BASE"
git diff "$BASE"..HEAD --stat
git diff "$BASE"..HEAD -- '*.rs' '*.toml' 'examples/'
```

If the diff is empty, stop and report: "No changes found to review."

## Step 2: Triage and Inventory

Classify the diff before reviewing:
- **Trivial/mechanical**: renames, formatting, comments, dep version bumps, generated code
  → Report "No material issues found" unless something catches your eye. Skip Step 3.
- **Targeted change**: ≤300 changed lines in a focused area → Review with relevant perspectives.
- **Large/cross-cutting**: >300 lines or multiple subsystems → Review all perspectives.

**Quick inventory:** List every changed function/struct/pub item (one line each).
At the end of Step 3, confirm you examined each one.

## Step 3: Review — Three Passes

**Your goal is breadth.** Cover the entire diff, don't fixate on one area.
Report anything suspicious even if you're only 60% sure — better to include a
Low finding than miss a Medium.

### Pass 1: Line-by-line correctness

Walk through every changed line. For each, ask:
- What was the author's intent? Does the code achieve it for ALL inputs?
- What happens with: empty, null, zero, max-size, wrong-type, nested, Undefined?
- What happens on Windows? With non-ASCII? With empty string vs absent?
- If output must follow a standard (SARIF, URI, JSON Schema): are all MUST
  requirements met? Reserved chars escaped? Required fields present?
- What does the most common real-world input to this function look like?
  Does the code handle that correctly? What about the second and third most
  common patterns?

For suspicious code paths, trace a concrete value through them:
```
input = <concrete example>
→ after line N: variable = <concrete value>
→ after line M: result = <concrete value>
→ expected: <what it should be>
```
Concrete traces strengthen Critical/High findings but are NOT required to
report a finding. If something looks wrong, report it — even at Medium/Low
confidence.

Use `view` to read surrounding context for anything suspicious.

### Pass 2: System-level consequences

Step back from individual lines:
- Does this new API freeze anything via semver? (pub fields, pub types, pub mods
  without feature gates)
- Could a caller misuse this API in a way the author didn't anticipate?
- Resource consumption: is anything proportional to untrusted input without bounds?
- Error handling: are errors propagated or silently swallowed? Appropriate types?
- Does this interact badly with existing features? (feature flags, no_std, `arc`,
  dual interpreter/RVM paths)
- If touching `src/engine.rs`, `src/lib.rs`, or `bindings/`: do all 9 targets handle it?
- If touching `Cargo.toml` or `#[cfg(feature)]`: feature gate correctness, no_std?

### Pass 3: What's missing

Scan the diff stat one final time:
- Are there files or functions you haven't examined closely? Look now.
- For each new public function: what happens with every `Value` variant?
  (Null, Bool, Number, String, Array, Set, Object, Undefined)
- What test cases would you write? Are the obvious ones present?
- What does the code assume about inputs that isn't validated?
- If control flow uses `break` in nested loops — does it exit the right level?

### Edge-Case Exploration

For each significant new function or data transformation:

1. **Boundary inputs**: empty collections, zero/max integers, single vs many,
   deeply nested
2. **Type mismatches**: expected object with fields → gets string/array/Undefined?
   Silent default? Error? Wrong output passed downstream?
3. **Platform variance**: Unix assumptions? (path separators, encoding, locale).
   Wrong output on Windows?
4. **Composition**: How does this interact with other modules? Could a valid
   combination produce unexpected behavior?
5. **Specification conformance**: If output follows a standard, are all MUST/SHOULD
   met? Reserved chars escaped? Required fields always present?

Only report edge cases with concrete example input → wrong output.

## Step 4: Design Considerations

Skip if the diff is trivial/mechanical or <50 changed lines.

Otherwise, briefly assess (2-3 sentences each, only if relevant):
- Is there a fundamentally simpler way to achieve the same goal?
- Does this duplicate existing infrastructure that could be reused?
- Are there tradeoffs the author may not have considered?

Only suggest alternatives you can concretely describe with clear benefit.

## Step 5: Report

### Findings (sorted by severity)

For each finding:
- **Severity**: Critical / High / Medium / Low
- **Confidence**: High / Medium / Low
- **Perspective**: which perspective found it
- **Location**: file:line
- **Issue**: one-sentence summary
- **Trace**: concrete input → concrete intermediate values → concrete wrong output
  (strengthens Critical/High but not required for Medium/Low)
- **Evidence**: the specific code (max 5 lines) and why it's wrong
- **Suggestion**: concrete fix (include code snippet when possible)

**Confidence guide:**
- **High**: you have a concrete trace showing wrong output
- **Medium**: pattern match + plausible scenario but no full trace
- **Low**: suspicious but cannot fully demonstrate the issue

**Severity calibration — lean toward reporting, not filtering.**
A separate review step can always downgrade. If you're unsure between two
severity levels, pick the higher one.

- **Critical**: Wrong policy result (allow/deny), panic reachable from FFI, security bypass.
  Every Critical MUST include: who triggers it, what specific input, why guards fail.
  If you can't construct a trigger path, downgrade to High.
- **High**: Panic in non-FFI path, unbounded resource usage, API break, data loss/corruption
- **Medium**: Logic error with limited blast radius, silent wrong output for edge-case inputs,
  missing bound on trusted path, design issue with concrete consequence
- **Low**: Minor inefficiency with measurable impact, missing validation, documentation gap

**Do NOT report:**
- Style preferences (naming, formatting) with no functional impact
- Anything the compiler or ~53 deny lints would catch
- "Consider using X" without explaining what goes wrong if you don't

**0 findings is valid** — do not manufacture findings without evidence.

**Calibration examples:**

Good finding:
> HIGH | src/eval.rs:42 | `items[idx]` where `idx` comes from untrusted input
> via `parse_array()` at line 38. No bounds check between parse and use.
> **Fix:** `items.get(idx).ok_or_else(|| anyhow!("index out of bounds"))?`

Bad finding (reject):
> "This unwrap could panic" — without verifying the value isn't guaranteed
> `Some` by construction. Check first.

Bad finding (reject):
> "Consider using a more descriptive variable name."

### Design Notes

Observations from Step 4 (if applicable).

### Coverage Check

Confirm: every function/struct from your inventory was examined in at least
one pass. If any were skipped, note them and briefly assess.

### Summary

X findings (N critical, N high, N medium, N low). One sentence overall assessment.
