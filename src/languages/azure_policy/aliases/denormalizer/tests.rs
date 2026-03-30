// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Inline denormalizer unit tests.

use alloc::collections::BTreeMap;
use alloc::string::ToString as _;
use alloc::vec;
use alloc::vec::Vec;

use super::super::types::ResolvedEntry;
use super::casing::build_casing_map;

fn make_entry(short: &str, default: &str, versioned: Vec<(&str, &str)>) -> ResolvedEntry {
    ResolvedEntry::new(
        short.to_string(),
        default.to_string(),
        versioned
            .into_iter()
            .map(|(v, p)| (v.to_string(), p.to_string()))
            .collect(),
        None,
    )
}

#[test]
fn build_casing_map_extracts_from_aliases() {
    let mut entries = BTreeMap::new();
    entries.insert(
        "supportshttpstrafficonly".to_string(),
        make_entry(
            "supportsHttpsTrafficOnly",
            "properties.supportsHttpsTrafficOnly",
            vec![],
        ),
    );
    entries.insert(
        "networkacls.defaultaction".to_string(),
        make_entry(
            "networkAcls.defaultAction",
            "properties.networkAcls.defaultAction",
            vec![],
        ),
    );

    let map = build_casing_map(&entries);
    assert_eq!(
        map.get("supportshttpstrafficonly"),
        Some(&"supportsHttpsTrafficOnly".to_string())
    );
    assert_eq!(map.get("networkacls"), Some(&"networkAcls".to_string()));
    assert_eq!(map.get("defaultaction"), Some(&"defaultAction".to_string()));
    assert_eq!(map.get("managedby"), Some(&"managedBy".to_string()));
    assert_eq!(map.get("apiversion"), Some(&"apiVersion".to_string()));
}
