// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// Match action strings against slash-delimited patterns with "*" wildcards.
//
// Behavior examples:
// - action:  "Microsoft.Storage/storageAccounts/read"
//   pattern: "Microsoft.Storage/storageAccounts/read" => true
// - action:  "Microsoft.Storage/storageAccounts/read"
//   pattern: "Microsoft.Storage/storageAccounts/*"    => true
// - action:  "Microsoft.Storage/storageAccounts/read"
//   pattern: "Microsoft.Storage/*/read"              => true
// - action:  "Microsoft.Storage/storageAccounts/read"
//   pattern: "Microsoft.Storage/*/write"             => false
// - action:  "Microsoft.Storage/storageAccounts/read"
//   pattern: "Microsoft.Storage/storageAccounts"     => false (segment count mismatch)
pub(super) fn action_matches_pattern(action: &str, pattern: &str) -> bool {
    // Split action and pattern into fixed segments (delimited by '/').
    let action_parts: alloc::vec::Vec<&str> = action.split('/').collect();
    let pattern_parts: alloc::vec::Vec<&str> = pattern.split('/').collect();

    // Require the same number of segments for a match.
    if action_parts.len() != pattern_parts.len() {
        return false;
    }

    // Compare segment-by-segment; "*" matches any single segment.
    for (action_part, pattern_part) in action_parts.iter().zip(pattern_parts.iter()) {
        if *pattern_part == "*" {
            // Wildcard segment matches anything in the corresponding position.
            continue;
        }
        if action_part != pattern_part {
            // Non-wildcard segment must match exactly.
            return false;
        }
    }

    // All segments matched.
    true
}
