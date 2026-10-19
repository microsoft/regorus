// Acceptance gate: consuming an untrusted compiled-policy blob must fail closed. Corrupt
// current-version sections, truncation, trailing data, and forged lengths are errors rather than
// silent fallbacks to an empty or partial program. Legacy versions retain their documented
// recompilation path.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::print_stdout)]

use regorus::rvm::program::DeserializationResult;
use regorus::rvm::Program;

const HDR: usize = 25; // MAGIC(4) version(4) 4x len(4) rego_v0(1)

fn sample() -> Vec<u8> {
    let mut p = Program::new();
    p.entry_points.insert("main".to_string(), 0usize);
    p.rule_tree = regorus::Value::from(7i64);
    p.rego_v0 = false;
    p.serialize_binary().expect("serialize")
}

fn u32_at(b: &[u8], off: usize) -> usize {
    u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]) as usize
}

fn consume(bytes: &[u8]) -> Result<DeserializationResult, String> {
    Program::deserialize_binary(bytes)
}

/// Byte offsets of the four extensible sections, derived from the header we know we produced.
fn sections(
    b: &[u8],
) -> (
    std::ops::Range<usize>,
    std::ops::Range<usize>,
    std::ops::Range<usize>,
    std::ops::Range<usize>,
) {
    let ep = u32_at(b, 8);
    let so = u32_at(b, 12);
    let li = u32_at(b, 16);
    let rt = u32_at(b, 20);
    let a = HDR..HDR + ep;
    let bs = a.end..a.end + so;
    let cs = bs.end..bs.end + li;
    let ds = cs.end..cs.end + rt;
    (a, bs, cs, ds)
}

#[test]
fn valid_blob_round_trips_and_is_within_limits() {
    let blob = sample();
    let got = consume(&blob).expect("a well-formed blob must consume");
    match got {
        DeserializationResult::Complete(p) => {
            assert!(
                !p.needs_recompilation,
                "a valid blob must not ask for recompilation"
            );
            p.validate_limits()
                .expect("valid program must pass its own limits");
            assert_eq!(p.entry_points.len(), 1);
            assert_eq!(p.rule_tree, regorus::Value::from(7i64));
        }
        DeserializationResult::Partial(p) => {
            panic!(
                "a well-formed current-version blob came back Partial (needs_recompilation={})",
                p.needs_recompilation
            );
        }
    }
}

#[test]
fn magic_mismatch_is_rejected() {
    let mut blob = sample();
    blob[0] = b'X';
    let err = consume(&blob).expect_err("bad magic must be rejected");
    assert!(
        err.to_lowercase().contains("magic"),
        "unexpected message: {err}"
    );
}

#[test]
fn future_version_is_rejected() {
    let mut blob = sample();
    blob[4..8].copy_from_slice(&(Program::SERIALIZATION_VERSION + 1).to_le_bytes());
    let err = consume(&blob).expect_err("a future version must be rejected");
    assert!(
        err.to_lowercase().contains("version"),
        "unexpected message: {err}"
    );
}

#[test]
fn legacy_versions_still_take_the_recompile_path() {
    // Pinned on purpose: the decision above is about CURRENT-version blobs only. Do not turn the
    // documented legacy path into an error.
    for v in 1..=5u32 {
        let mut blob = sample();
        blob[4..8].copy_from_slice(&v.to_le_bytes());
        match consume(&blob)
            .unwrap_or_else(|e| panic!("version {v} must be accepted as legacy: {e}"))
        {
            DeserializationResult::Partial(p) => assert!(
                p.needs_recompilation,
                "legacy version {v} must set needs_recompilation"
            ),
            DeserializationResult::Complete(p) => panic!(
                "legacy version {v} came back Complete (needs_recompilation={})",
                p.needs_recompilation
            ),
        }
    }
}

#[test]
fn truncated_blob_is_rejected() {
    let blob = sample();
    for cut in [1usize, 4, 9, 20, 24, 25, blob.len() / 2, blob.len() - 1] {
        if cut >= blob.len() {
            continue;
        }
        let err =
            consume(&blob[..blob.len() - cut]).expect_err("truncation at -{cut} must be rejected");
        assert!(!err.is_empty(), "empty error for truncation at -{cut}");
    }
}

#[test]
fn trailing_data_is_rejected() {
    let mut blob = sample();
    blob.extend_from_slice(b"trailing");
    let err = consume(&blob).expect_err("trailing data must be rejected");
    assert!(
        err.to_lowercase().contains("trailing"),
        "unexpected message: {err}"
    );
}

#[test]
fn corrupted_rule_tree_is_an_error_not_a_silent_recompile() {
    let mut blob = sample();
    let (a, b, c, d) = sections(&blob);
    assert!(d.len() > 0, "test program must have a non-empty rule tree");
    for byte in blob[d.clone()].iter_mut() {
        *byte = byte.wrapping_add(0x5a);
    }
    let _ = (a, b, c);
    match consume(&blob) {
        Err(err) => {
            println!("corrupt rule tree rejected: {err}");
        }
        Ok(DeserializationResult::Partial(p)) => panic!(
            "RED: a corrupt rule_tree section was swallowed as needs_recompilation={} \
             (rule_tree replaced with {}); a current-version blob must be rejected",
            p.needs_recompilation, p.rule_tree
        ),
        Ok(DeserializationResult::Complete(p)) => panic!(
            "RED: a corrupt rule_tree section produced a Complete program (rule_tree={})",
            p.rule_tree
        ),
    }
}

#[test]
fn corrupted_program_section_is_an_error_not_a_silent_recompile() {
    let mut blob = sample();
    let (_, _, _, d) = sections(&blob);
    let bin_len_at = d.end + 4; // binary_len u32 then the postcard Program
    assert!(
        bin_len_at + 4 <= blob.len(),
        "blob too small to have a program section"
    );
    for byte in blob[bin_len_at..].iter_mut() {
        *byte = byte.wrapping_add(0xa5);
    }
    match consume(&blob) {
        Err(err) => println!("corrupt program section rejected: {err}"),
        Ok(DeserializationResult::Partial(p)) => panic!(
            "RED: a corrupt Program section was swallowed (needs_recompilation={}, instructions={}, \
             entry_points={}); executing that program would evaluate an empty instruction table",
            p.needs_recompilation,
            p.instructions.len(),
            p.entry_points.len()
        ),
        Ok(DeserializationResult::Complete(p)) => panic!(
            "RED: corrupt Program section came back Complete with {} instructions",
            p.instructions.len()
        ),
    }
}

#[test]
fn forged_section_lengths_are_rejected_without_allocating() {
    let blob = sample();
    for off in [8usize, 12, 16, 20] {
        let mut b = blob.clone();
        b[off..off + 4].copy_from_slice(&u32::MAX.to_le_bytes());
        let err = consume(&b).expect_err("a forged section length must be rejected");
        assert!(!err.is_empty(), "empty error for forged length at {off}");
    }
    // The forged-length path must not allocate from the declared size: this test process is still
    // alive and small if that held (a with_capacity(u32::MAX) would have aborted it).
    let rss = std::fs::read_to_string("/proc/self/status")
        .unwrap_or_default()
        .lines()
        .find_map(|l| {
            l.strip_prefix("VmHWM:").map(|v| {
                v.trim()
                    .trim_end_matches(" kB")
                    .trim()
                    .parse::<u64>()
                    .unwrap_or(0)
            })
        })
        .unwrap_or(0);
    assert!(
        rss < 300_000,
        "consume peaked at {rss} kB from a forged section length"
    );
}
