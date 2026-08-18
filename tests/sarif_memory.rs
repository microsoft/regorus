// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Memory-residency measurement on a real SARIF workload.
//!
//! This test wraps the system allocator to track live / peak memory while
//! parsing a SARIF JSON payload into a `Value`, building an engine, and
//! evaluating a small compliance policy. It prints the numbers and applies
//! coarse sanity bounds so a catastrophic memory regression breaks CI.
//!
//! It is intentionally **the only test in this file** so the custom global
//! allocator's counters reflect only this workload (a cargo integration test
//! file is compiled as its own binary).
//!
//! The dataset can be amplified by setting the `MULT` env var (default 1).
//! `MULT=50` reproduces the original customer-scale memory-pressure scenario
//! that motivated the storage abstractions: ~6.6 MiB JSON → ~227 MiB peak
//! on the unmodified `BTreeMap`-backed `Object`.

// The custom global allocator below conflicts with regorus's `mimalloc`
// global allocator (set when the `mimalloc` feature is enabled). When that
// feature is on, this whole test becomes a no-op; the test only makes sense
// against the system allocator anyway.
#![cfg(not(feature = "mimalloc"))]

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

struct Tracking;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static TOTAL_ALLOC: AtomicUsize = AtomicUsize::new(0);
static NALLOC: AtomicUsize = AtomicUsize::new(0);
static LOCK: Mutex<()> = Mutex::new(());

unsafe impl GlobalAlloc for Tracking {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = System.alloc(l);
        if !p.is_null() {
            let n = l.size();
            let cur = LIVE.fetch_add(n, Ordering::Relaxed) + n;
            TOTAL_ALLOC.fetch_add(n, Ordering::Relaxed);
            NALLOC.fetch_add(1, Ordering::Relaxed);
            let mut peak = PEAK.load(Ordering::Relaxed);
            while cur > peak {
                match PEAK.compare_exchange_weak(peak, cur, Ordering::Relaxed, Ordering::Relaxed) {
                    Ok(_) => break,
                    Err(p) => peak = p,
                }
            }
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        System.dealloc(p, l);
        LIVE.fetch_sub(l.size(), Ordering::Relaxed);
    }
}

#[global_allocator]
static A: Tracking = Tracking;

#[derive(Copy, Clone)]
struct Snap {
    live: usize,
    peak: usize,
    total: usize,
    nalloc: usize,
}

fn snap() -> Snap {
    Snap {
        live: LIVE.load(Ordering::Relaxed),
        peak: PEAK.load(Ordering::Relaxed),
        total: TOTAL_ALLOC.load(Ordering::Relaxed),
        nalloc: NALLOC.load(Ordering::Relaxed),
    }
}

fn reset_peak_to_live() {
    PEAK.store(LIVE.load(Ordering::Relaxed), Ordering::Relaxed);
}

fn mib(b: usize) -> f64 {
    b as f64 / (1024.0 * 1024.0)
}

fn report(label: &str, s: Snap, base: Snap) {
    println!(
        "  {:30} live={:>9.3} MiB  peak={:>9.3} MiB  total_alloc={:>9.3} MiB  nalloc={}",
        label,
        mib(s.live.saturating_sub(base.live)),
        mib(s.peak.saturating_sub(base.peak)),
        mib(s.total - base.total),
        s.nalloc - base.nalloc,
    );
}

#[test]
fn sarif_memory_residency() {
    // The global allocator counters are process-wide; keep the measurement
    // serialized even if another test is added to this binary later.
    let _guard = LOCK.lock().expect("sarif memory measurement lock poisoned");
    let policy =
        std::fs::read_to_string("tests/data/sarif_memory/policy.rego").expect("read policy.rego");
    let input =
        std::fs::read_to_string("tests/data/sarif_memory/input.json").expect("read input.json");

    let mult: usize = std::env::var("MULT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1);

    // Amplify runs[0].results by MULT so larger workloads can be probed.
    let mut v: serde_json::Value = serde_json::from_str(&input).expect("parse SARIF input as JSON");
    if let Some(runs) = v.get_mut("runs").and_then(|r| r.as_array_mut()) {
        if let Some(r0) = runs.get_mut(0) {
            if let Some(results) = r0.get_mut("results").and_then(|r| r.as_array_mut()) {
                let original = results.clone();
                for _ in 1..mult {
                    results.extend(original.iter().cloned());
                }
            }
            // Synthesize an invocations array so the policy can succeed.
            if r0.get("invocations").is_none() {
                if let Some(obj) = r0.as_object_mut() {
                    obj.insert(
                        "invocations".into(),
                        serde_json::json!([{"executionSuccessful": true}]),
                    );
                }
            }
        }
    }

    // Wrap to match policy schema: input.PrefastConfigContent.resolvedData.content
    let wrapped = serde_json::json!({
        "PrefastConfigContent": { "resolvedData": { "content": v } }
    });
    let input_json = serde_json::to_string(&wrapped).expect("serialize wrapped input");
    drop(wrapped);

    // Reset baseline so we only count work done from here on.
    reset_peak_to_live();
    let base = snap();
    let raw_bytes = input_json.len();

    println!();
    println!(
        "=== SARIF memory residency (MULT={mult}, input JSON = {:.3} MiB) ===",
        mib(raw_bytes)
    );
    report("baseline", base, base);

    let mut engine = regorus::Engine::new();
    engine
        .add_policy("policy.rego".into(), policy.clone())
        .expect("add policy");
    let after_policy = snap();
    report("after add_policy", after_policy, base);

    let input_value =
        regorus::Value::from_json_str(&input_json).expect("parse input JSON to Value");
    let after_input_parse = snap();
    report("after Value::from_json_str", after_input_parse, base);

    drop(input_json);
    let after_drop_json = snap();
    report("after drop JSON string", after_drop_json, base);

    engine.set_input(input_value);
    let after_set_input = snap();
    report("after set_input", after_set_input, base);

    let results = engine
        .eval_query(
            "data.staticAnalysisResult.Verification.compliant".to_string(),
            false,
        )
        .expect("eval query");
    let after_eval = snap();
    report("after eval_query", after_eval, base);

    let result_value = results
        .result
        .first()
        .and_then(|r| r.expressions.first())
        .map(|e| e.value.clone());
    println!("  query result: {result_value:?}");

    let parse_live = after_input_parse.live.saturating_sub(after_policy.live);
    let eval_live = after_eval.live.saturating_sub(after_set_input.live);
    let peak_during_eval = after_eval.peak.saturating_sub(base.peak);
    let value_blowup = parse_live as f64 / raw_bytes as f64;

    println!();
    println!(
        "  --> Value::from_json_str cost: live +{:.3} MiB ({:.2}× JSON size)",
        mib(parse_live),
        value_blowup
    );
    println!(
        "  --> eval cost:                  live +{:.3} MiB",
        mib(eval_live)
    );
    println!(
        "  --> peak during run:            {:.3} MiB",
        mib(peak_during_eval)
    );

    // Coarse sanity bound: even an unoptimized BTreeMap-backed Object should
    // not balloon to more than ~50× the JSON size for the un-amplified case
    // (MULT=1). The historical baseline (MULT=50, BTreeMap) was ~30× live
    // blow-up; we leave plenty of headroom for the unamplified case so this
    // assert only catches genuinely catastrophic regressions.
    let max_blowup = 50.0;
    assert!(
        value_blowup < max_blowup,
        "Value blow-up ratio {value_blowup:.2}× exceeds {max_blowup}× — \
         possible memory regression in Value/Object representation"
    );
}
