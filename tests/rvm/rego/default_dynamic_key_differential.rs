// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Differential test for `default` rules beneath a dynamically keyed rule.
//!
//! Like OPA, a rule whose ref head has a dynamic key (`p[k] := 1`) owns its
//! whole extent: a `default` rule beneath it (`default p.r := 0`) is ignored,
//! so `p.r` is defined only when `p[k]` produces `r`. A default beside a deeper
//! dynamic rule (`p.q[k]`) or beside a constant key still applies. (OPA rejects
//! a default exactly at the owner's path, `default p := 0`, as a conflict;
//! regorus ignores it too.) The expected values were produced by OPA 1.2.0;
//! each must match in the interpreter (`eval_rule` and `eval_query`) and in
//! both RVM execution modes, unless pinned. Most cases are also rerun without
//! their shadowed defaults (see `Case::twin`).

use anyhow::Result;
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, RegoVM};
use regorus::{Engine, Value};

struct Case {
    name: &'static str,
    v0: bool,
    /// If set, the queries, except those listed, are rerun with the `default`
    /// lines not marked `# kept` removed and must give the same results, i.e.
    /// regorus must ignore the shadowed defaults. This compares regorus with
    /// itself, not with OPA, which rejects some twins (e.g. `default_two_levels`
    /// and `array_key_owner` as type errors, `subpkg_owner_default_above` for
    /// an unsafe `sub`). The listed queries are usually entry points at a
    /// default's path, which only the default makes valid in regorus.
    twin: Option<&'static [&'static str]>,
    modules: &'static [&'static str],
    /// Query, then input and the expected result (JSON, `undefined` or
    /// `error`) from OPA, optionally followed by `; <engine>=<value>` pins
    /// that record a divergence of that engine from OPA. The engine is
    /// `interpreter`, `eval_query`, `rvm` (both RVM execution modes) or `rvm
    /// suspendable` (that mode only, for divergences of the suspendable mode
    /// alone, e.g. some virtual documents read as undefined); a later pin
    /// overrides an earlier one. Unless noted, each divergence is the same
    /// with the default removed (e.g. the RVM does not support nested dynamic
    /// keys such as `p.q[k].s`); `twin` and the `*_no_default` cases check
    /// this. A pin value of `error` expects the engine to fail (e.g. the RVM
    /// accepts only rule paths as entry points).
    queries: &'static [(&'static str, &'static [(&'static str, &'static str)])],
}

#[rustfmt::skip]
const CASES: &[Case] = &[
    Case {
        name: "base", v0: false, twin: Some(&["data.probe.p.r"]),
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
parent := p
child := p.r
"#],
        queries: &[
            ("data.probe.parent", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
            ]),
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
            ("data.probe.p.r", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
            ("data.probe.p", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
            ]),
        ],
    },
    Case {
        name: "default_two_levels", v0: false, twin: Some(&["data.probe.p.r.s"]),
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r.s := 0
parent := p
child := p.r.s
"#],
        queries: &[
            ("data.probe.parent", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
            ]),
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"undefined"#),
            ]),
            ("data.probe.p.r.s", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"undefined"#),
            ]),
            ("data.probe.p.r", &[
                (r#"{"ks":[]}"#, r#"undefined; interpreter=error; rvm=error"#),
                (r#"{"ks":["a"]}"#, r#"undefined; interpreter=error; rvm=error"#),
                (r#"{"ks":["r"]}"#, r#"1; interpreter=error; rvm=error"#),
            ]),
            ("data.probe.p", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
            ]),
        ],
    },
    Case {
        name: "multi_module_pkg", v0: false, twin: Some(&["data.probe.p.r"]),
        modules: &[
            r#"package probe
p[k] := 1 if { some k in input.ks }
parent := p
child := p.r
"#,
            r#"package probe.p
default r := 0
"#,
        ],
        queries: &[
            ("data.probe.parent", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
            ]),
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
            ("data.probe.p.r", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
        ],
    },
    Case {
        name: "default_first_module", v0: false, twin: Some(&[]),
        modules: &[
            r#"package probe
default p.r := 0
child := p.r
"#,
            r#"package probe
p[k] := 1 if { some k in input.ks }
"#,
        ],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
        ],
    },
    Case {
        name: "two_defaults_under_dyn", v0: false, twin: Some(&["data.probe.p.s"]),
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
default p.s := 1
parent := p
child := p.r
"#],
        queries: &[
            ("data.probe.parent", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
            ]),
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
            ("data.probe.p.s", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"undefined"#),
            ]),
        ],
    },
    Case {
        name: "dyn_deeper_default_under", v0: false, twin: Some(&[]),
        modules: &[r#"package probe
p.q[k] := 1 if { some k in input.ks }
default p.q.r := 0
child := p.q.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
        ],
    },
    Case {
        name: "default_obj_value", v0: false, twin: Some(&[]),
        modules: &[r#"package probe
p[k] := {"v": 1} if { some k in input.ks }
default p.r := {"v": 0}
parent := p
child := p.r
"#],
        queries: &[
            ("data.probe.parent", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":{"v":1}}"#),
                (r#"{"ks":["r"]}"#, r#"{"r":{"v":1}}"#),
            ]),
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"{"v":1}"#),
            ]),
        ],
    },
    // No twin: without the default, `r` is unsafe.
    Case {
        name: "subpkg_local_ref", v0: false, twin: None,
        modules: &[
            r#"package probe
p[k] := 1 if { some k in input.ks }
child := p.y
"#,
            r#"package probe.p
default r := 0
y := r
"#,
        ],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
        ],
    },
    Case {
        name: "dyn_key_lookup_var", v0: false, twin: Some(&[]),
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
y := p[input.k]
z := v if { some k; v := p[k]; k == input.k }
"#],
        queries: &[
            ("data.probe.y", &[
                (r#"{"ks":[],"k":"r"}"#, r#"undefined"#),
                (r#"{"ks":["r"],"k":"r"}"#, r#"1"#),
                (r#"{"ks":["a"],"k":"r"}"#, r#"undefined"#),
                (r#"{"ks":["a"],"k":"a"}"#, r#"1"#),
            ]),
            ("data.probe.z", &[
                (r#"{"ks":[],"k":"r"}"#, r#"undefined"#),
                (r#"{"ks":["r"],"k":"r"}"#, r#"1"#),
                (r#"{"ks":["a"],"k":"r"}"#, r#"undefined"#),
            ]),
        ],
    },
    Case {
        name: "virtual_pkg_from_other", v0: false, twin: Some(&[]),
        modules: &[
            r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
"#,
            r#"package q
all := data.probe
child := data.probe.p.r
"#,
        ],
        queries: &[
            ("data.q.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
        ],
    },
    Case {
        name: "static_rule_and_default", v0: false, twin: Some(&[]),
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
p.r := 2 if input.x
default p.r := 0
child := p.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":[],"x":true}"#, r#"2"#),
                (r#"{"ks":["a"],"x":true}"#, r#"2"#),
            ]),
        ],
    },
    // The default applies (no twin).
    Case {
        name: "no_dynamic", v0: false, twin: None,
        modules: &[r#"package probe
p.a := 1 if { "a" in input.ks }
default p.r := 0
child := p.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
            ("data.probe.p.r", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
        ],
    },
    // The default applies (no twin).
    Case {
        name: "dyn_sibling_deeper", v0: false, twin: None,
        modules: &[r#"package probe
p.q[k] := 1 if { some k in input.ks }
default p.r := 0
child := p.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
            ("data.probe.p.r", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
        ],
    },
    // The default applies (no twin).
    Case {
        name: "static_key_rule_sibling_default", v0: false, twin: None,
        modules: &[r#"package probe
p["a"] := 1 if { "a" in input.ks }
default p.r := 0
child := p.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
            ("data.probe.p.r", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
        ],
    },
    // The default applies (no twin).
    Case {
        name: "contains_sibling", v0: false, twin: None,
        modules: &[r#"package probe
p.q contains k if { some k in input.ks }
default p.r := 0
child := p.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
            ("data.probe.p.r", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
        ],
    },
    // The default applies (no twin).
    Case {
        name: "v0_partial_set_sibling", v0: true, twin: None,
        modules: &[r#"package probe
p.q[x] { x := input.ks[_] }
default p.r = 0
child := p.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
            ("data.probe.p.r", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
        ],
    },
    // The default applies (no twin).
    Case {
        name: "dyn_in_other_pkg_deeper", v0: false, twin: None,
        modules: &[
            r#"package probe.p
q[k] := 1 if { some k in input.ks }
"#,
            r#"package probe
default p.r := 0
child := p.r
"#,
        ],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
            ("data.probe.p.r", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["a"]}"#, r#"0"#),
                (r#"{"ks":["r"]}"#, r#"0"#),
            ]),
        ],
    },
    // The default applies (no twin).
    Case {
        name: "sibling_defaults_no_dyn", v0: false, twin: None,
        modules: &[r#"package probe
p.r := 5 if input.x
default p.r := 0
default p.s := 1
child := p.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{}"#, r#"0"#),
                (r#"{"x":true}"#, r#"5"#),
            ]),
            ("data.probe.p.s", &[
                (r#"{}"#, r#"1"#),
                (r#"{"x":true}"#, r#"1"#),
            ]),
        ],
    },
    // No twin: without the default, regorus reports recursion for `p.r`.
    Case {
        name: "rule_reads_shadowed_default", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := 1 if some k in input.ks
default p.r := 0
p.s := x if { x := p.r }
"#],
        queries: &[
            ("data.probe.p.s", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
        ],
    },
    // No twin: without the default, regorus reports recursion for `p.r`.
    Case {
        name: "rule_tests_shadowed_default", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks; k != "s" }
default p.r := 0
p.s := 7 if { p.r }
"#],
        queries: &[
            ("data.probe.p.s", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"7"#),
            ]),
        ],
    },
    Case {
        name: "nested_owner_default_beneath", v0: false, twin: Some(&["data.probe.p.q.r.s"]),
        modules: &[r#"package probe
p.q[k].s := 1 if { some k in input.ks }
default p.q.r.s := 0
default p.t := 2 # kept
parent := p
child := p.q.r.s
t := p.t
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1; rvm=undefined"#),
            ]),
            ("data.probe.parent", &[
                (r#"{"ks":[]}"#, r#"{"q":{},"t":2}; interpreter={"t":2}; eval_query={"t":2}; rvm={"t":2}"#),
                (r#"{"ks":["a"]}"#, r#"{"q":{"a":{"s":1}},"t":2}; rvm=1"#),
                (r#"{"ks":["r"]}"#, r#"{"q":{"r":{"s":1}},"t":2}; rvm=1"#),
            ]),
            ("data.probe.p.q.r.s", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1; rvm=undefined"#),
            ]),
            ("data.probe.t", &[
                (r#"{"ks":[]}"#, r#"2"#),
                (r#"{"ks":["a"]}"#, r#"2"#),
                (r#"{"ks":["r"]}"#, r#"2"#),
            ]),
        ],
    },
    Case {
        name: "virtual_lookup_beneath_owner", v0: false, twin: Some(&[]),
        modules: &[
            r#"package probe
p[k] := 1 if some k in input.ks
default p.r := 0
"#,
            r#"package q
y := data.probe[input.n].r
all := data.probe
"#,
        ],
        queries: &[
            ("data.q.y", &[
                (r#"{"ks":[],"n":"p"}"#, r#"undefined"#),
                (r#"{"ks":["r"],"n":"p"}"#, r#"1; rvm=undefined"#),
            ]),
        ],
    },
    // `eval_query` pre-creates `p.r` for `p.r.s`, which then conflicts with
    // `p[x]` for x = "r". Without the default, every engine ignores `p[x]`
    // here and is undefined (see the next case; hence no `twin`).
    Case {
        name: "static_rule_beside_owner", v0: false, twin: None,
        modules: &[r#"package probe
p[x] := {"t": 1} if some x in input.ks
p.r.s := 2 if input.y
default p.r.t := 0
a := data.probe.p.r.t
b := p.r.t
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1; eval_query=error"#),
            ]),
            ("data.probe.b", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1; eval_query=error"#),
            ]),
        ],
    },
    // Twin of static_rule_beside_owner without the default.
    Case {
        name: "static_rule_beside_owner_no_default", v0: false, twin: None,
        modules: &[r#"package probe
p[x] := {"t": 1} if some x in input.ks
p.r.s := 2 if input.y
a := data.probe.p.r.t
b := p.r.t
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1; interpreter=undefined; eval_query=undefined; rvm=undefined"#),
            ]),
            ("data.probe.b", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1; interpreter=undefined; eval_query=undefined; rvm=undefined"#),
            ]),
        ],
    },
    // The default applies (no twin).
    Case {
        name: "number_owner_string_default", v0: false, twin: None,
        modules: &[r#"package probe
p[1][k] := 1 if some k in input.ks
default p["1"].s := 0
a := p["1"].s
b := p[1]
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["s"]}"#, r#"0"#),
            ]),
        ],
    },
    // The default applies (no twin).
    Case {
        name: "bool_owner_string_default", v0: false, twin: None,
        modules: &[r#"package probe
p[true][k] := 1 if some k in input.ks
default p["true"].s := 0
a := p["true"].s
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[]}"#, r#"0"#),
                (r#"{"ks":["s"]}"#, r#"0"#),
            ]),
        ],
    },
    Case {
        name: "number_key_default", v0: false, twin: Some(&[]),
        modules: &[r#"package probe
p[k] := {"s": 9} if some k in input.ks
default p[1].s := 0
a := p[1].s
b := p["1"].s
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":[1]}"#, r#"9"#),
                (r#"{"ks":["1"]}"#, r#"undefined"#),
            ]),
            ("data.probe.b", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":[1]}"#, r#"undefined"#),
                (r#"{"ks":["1"]}"#, r#"9"#),
            ]),
        ],
    },
    // No twin: without the default, the RVM rejects `p.r` beside `p.q`.
    Case {
        name: "constant_rule_beside_owner", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := 1 if some k in input.ks
p.q := 2 if input.x
default p.r := 0
a := p.r
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
                (r#"{"ks":["r"],"x":true}"#, r#"1"#),
            ]),
            ("data.probe.p.r", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
                (r#"{"ks":["r"],"x":true}"#, r#"1"#),
            ]),
        ],
    },
    Case {
        name: "default_named_like_key_var", v0: false, twin: Some(&["data.probe.p.k"]),
        modules: &[r#"package probe
p[k].s := 1 if some k in input.ks
default p.k := 0
a := p.k
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["k"]}"#, r#"{"s":1}; rvm=1"#),
                (r#"{"ks":["a"]}"#, r#"undefined; rvm=1"#),
            ]),
            ("data.probe.p.k", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["k"]}"#, r#"{"s":1}; rvm=1"#),
                (r#"{"ks":["a"]}"#, r#"undefined; rvm=1"#),
            ]),
        ],
    },
    Case {
        name: "import_alias", v0: false, twin: Some(&[]),
        modules: &[
            r#"package probe
p[k] := 1 if some k in input.ks
default p.r := 0
"#,
            r#"package q
import data.probe.p.r as pr
y := pr
"#,
        ],
        queries: &[
            ("data.q.y", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
        ],
    },
    Case {
        name: "nested_owner_defaults_first", v0: false, twin: Some(&[]),
        modules: &[r#"package probe
default p.t := 2 # kept
default p.q.r.s := 0
p.q[k].s := 1 if { some k in input.ks }
t := p.t
child := p.q.r.s
"#],
        queries: &[
            ("data.probe.t", &[
                (r#"{"ks":[]}"#, r#"2"#),
                (r#"{"ks":["r"]}"#, r#"2"#),
            ]),
            ("data.probe.child", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1; rvm=undefined"#),
            ]),
            ("data.probe.p.t", &[
                (r#"{"ks":[]}"#, r#"2"#),
                (r#"{"ks":["r"]}"#, r#"2"#),
            ]),
        ],
    },
    // OPA rejects this policy (`p.q` conflicts with `p.q.r`); the expected
    // values are those without the default, which regorus falls back to.
    Case {
        name: "default_beneath_constant_rule", v0: false, twin: Some(&["data.probe.p.q.r"]),
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
p.q := {"r": 5} if input.x
default p.q.r := 0
a := p.q.r
b := data.probe.p.q.r
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"],"x":true}"#, r#"5"#),
            ]),
            ("data.probe.b", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"],"x":true}"#, r#"5"#),
            ]),
            ("data.probe.p.q.r", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"],"x":true}"#, r#"5"#),
            ]),
        ],
    },
    Case {
        name: "subpackage_rule_beneath_owner", v0: false, twin: Some(&["data.probe.p.q.r"]),
        modules: &[
            r#"package probe
p[k] := 1 if { some k in input.ks }
child := p.q.r
"#,
            r#"package probe.p
q[j] := 2 if { some j in input.js }
default q.r := 0
"#,
        ],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[],"js":[]}"#, r#"undefined"#),
                (r#"{"ks":[],"js":["r"]}"#, r#"2"#),
                (r#"{"ks":["a"],"js":["r"]}"#, r#"2"#),
                (r#"{"ks":["a"],"js":["z"]}"#, r#"undefined"#),
            ]),
            ("data.probe.p.q.r", &[
                (r#"{"ks":[],"js":[]}"#, r#"undefined"#),
                (r#"{"ks":[],"js":["r"]}"#, r#"2"#),
                (r#"{"ks":["a"],"js":["r"]}"#, r#"2"#),
                (r#"{"ks":["a"],"js":["z"]}"#, r#"undefined"#),
            ]),
            ("data.probe.p", &[
                (r#"{"ks":[],"js":[]}"#, r#"{}; eval_query={"q":{}}"#),
                (r#"{"ks":[],"js":["r"]}"#, r#"{"q":{"r":2}}; interpreter={}; rvm={}"#),
                (r#"{"ks":["a"],"js":["r"]}"#, r#"{"a":1,"q":{"r":2}}; interpreter={"a":1}; rvm={"a":1}"#),
                (r#"{"ks":["a"],"js":["z"]}"#, r#"{"a":1,"q":{"z":2}}; interpreter={"a":1}; rvm={"a":1}"#),
            ]),
        ],
    },
    Case {
        name: "nested_owners", v0: false, twin: Some(&["data.probe.p.q.r"]),
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
p.q[j] := 2 if { some j in input.js }
default p.q.r := 0
child := p.q.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":[],"js":[]}"#, r#"undefined"#),
                (r#"{"ks":[],"js":["r"]}"#, r#"2"#),
                (r#"{"ks":["a"],"js":["r"]}"#, r#"2"#),
                (r#"{"ks":["a"],"js":["z"]}"#, r#"undefined"#),
            ]),
            ("data.probe.p.q.r", &[
                (r#"{"ks":[],"js":[]}"#, r#"undefined"#),
                (r#"{"ks":[],"js":["r"]}"#, r#"2"#),
                (r#"{"ks":["a"],"js":["r"]}"#, r#"2"#),
                (r#"{"ks":["a"],"js":["z"]}"#, r#"undefined"#),
            ]),
            ("data.probe.p", &[
                (r#"{"ks":[],"js":[]}"#, r#"{}; interpreter={"q":{}}; eval_query={"q":{}}"#),
                (r#"{"ks":[],"js":["r"]}"#, r#"{"q":{"r":2}}; rvm={"r":2}"#),
                (r#"{"ks":["a"],"js":["r"]}"#, r#"{"a":1,"q":{"r":2}}; rvm={"a":1,"r":2}"#),
                (r#"{"ks":["a"],"js":["z"]}"#, r#"{"a":1,"q":{"z":2}}; rvm={"a":1,"z":2}"#),
            ]),
        ],
    },
    Case {
        name: "two_owner_rules_entry_point", v0: false, twin: Some(&["data.probe.p.r.t"]),
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
p[x].t := 2 if { some x in input.xs }
default p.r.t := 0
a := p.r.t
"#],
        queries: &[
            ("data.probe.p.r.t", &[
                (r#"{"ks":[],"xs":[]}"#, r#"undefined; rvm=error"#),
                (r#"{"ks":[],"xs":["r"]}"#, r#"2; rvm=error"#),
                (r#"{"ks":["r"],"xs":[]}"#, r#"undefined; rvm=error"#),
                (r#"{"ks":["a"],"xs":["z"]}"#, r#"undefined; rvm=error"#),
            ]),
            ("data.probe.a", &[
                (r#"{"ks":[],"xs":[]}"#, r#"undefined; rvm=error"#),
                (r#"{"ks":[],"xs":["r"]}"#, r#"2; rvm=error"#),
                (r#"{"ks":["r"],"xs":[]}"#, r#"undefined; rvm=error"#),
                (r#"{"ks":["a"],"xs":["z"]}"#, r#"undefined; rvm=error"#),
            ]),
        ],
    },
    // A default beneath an owner in a subpackage registers no rule above the
    // owner: `data.probe.sub` is read as a virtual document.
    Case {
        name: "subpkg_owner_default_above", v0: false, twin: Some(&["data.probe.z"]),
        modules: &[
            r#"package probe
default sub.p.r := 0
x := data.probe.sub
z := sub
"#,
            r#"package probe.sub
p[k] := 1 if { some k in input.ks }
"#,
        ],
        queries: &[
            ("data.probe.x", &[
                (r#"{"ks":[]}"#, r#"{"p":{}}"#),
                (r#"{"ks":["a"]}"#, r#"{"p":{"a":1}}; rvm suspendable=undefined"#),
                (r#"{"ks":["r"]}"#, r#"{"p":{"r":1}}; rvm suspendable=undefined"#),
            ]),
            ("data.probe.z", &[
                (r#"{"ks":[]}"#, r#"{"p":{}}"#),
                (r#"{"ks":["a"]}"#, r#"{"p":{"a":1}}; rvm suspendable=undefined"#),
                (r#"{"ks":["r"]}"#, r#"{"p":{"r":1}}; rvm suspendable=undefined"#),
            ]),
            ("data.probe.sub", &[
                (r#"{"ks":[]}"#, r#"{"p":{}}; interpreter=error; rvm=error"#),
                (r#"{"ks":["a"]}"#, r#"{"p":{"a":1}}; interpreter=error; rvm=error"#),
                (r#"{"ks":["r"]}"#, r#"{"p":{"r":1}}; interpreter=error; rvm=error"#),
            ]),
        ],
    },
    // The default registers no rule above the owner, but `sub` is still read
    // as `data.probe.sub`. (Without the default, `sub` is unsafe, in OPA too;
    // see the next case.)
    Case {
        name: "subpkg_owner_read_default_ref", v0: false, twin: None,
        modules: &[
            r#"package probe
default sub.p.r := 0
y := sub.p.r
w := sub.p
"#,
            r#"package probe.sub
p[k] := 1 if { some k in input.ks }
"#,
        ],
        queries: &[
            ("data.probe.y", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"undefined"#),
                (r#"{"ks":["r"]}"#, r#"1"#),
            ]),
            ("data.probe.w", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
                (r#"{"ks":["r"]}"#, r#"{"r":1}"#),
            ]),
        ],
    },
    // Without the default, the bare `sub` is unsafe, in OPA too.
    Case {
        name: "subpkg_owner_bare_ref_no_default", v0: false, twin: None,
        modules: &[
            r#"package probe
z := sub
"#,
            r#"package probe.sub
p[k] := 1 if { some k in input.ks }
"#,
        ],
        queries: &[("data.probe.z", &[(r#"{"ks":["a"]}"#, r#"error"#)])],
    },
    // Reading `sub.p` through the default's prefix must not hide the real rule
    // `sub.q` of the same package.
    Case {
        name: "subpkg_owner_prefix_and_real_rule", v0: false, twin: Some(&[]),
        modules: &[
            r#"package probe
default sub.p.r := 0
sub.q := 2
x := [y, z] if { y := sub.p; z := sub.q }
"#,
            r#"package probe.sub
p[k] := 1 if { some k in input.ks }
"#,
        ],
        queries: &[
            ("data.probe.x", &[
                (r#"{"ks":[]}"#, r#"[{},2]"#),
                (r#"{"ks":["a"]}"#, r#"[{"a":1},2]"#),
            ]),
        ],
    },
    // Reading `sub.p.a` through the default's prefix evaluates only `sub.p`,
    // not the rest of the package (`t` would recurse and `u` conflicts). No
    // twin: without the default, `sub` is unsafe.
    Case {
        name: "subpkg_owner_prefix_lazy", v0: false, twin: None,
        modules: &[
            r#"package probe
default sub.p.r := 0
y := sub.p.a
"#,
            r#"package probe.sub
p[k] := 1 if { some k in input.ks }
t := data.probe.y
u := 1
u := 2 if input.ks
"#,
        ],
        queries: &[
            ("data.probe.y", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"1"#),
                (r#"{"ks":["r"]}"#, r#"undefined"#),
            ]),
            ("data.probe.sub.t", &[
                (r#"{"ks":[]}"#, r#"undefined"#),
                (r#"{"ks":["a"]}"#, r#"1"#),
            ]),
        ],
    },
    // Reading the owner `p` evaluates only its rules, not the subpackage
    // `probe.p.z` (whose `y` conflicts).
    Case {
        name: "owner_read_skips_subpackage", v0: false, twin: Some(&[]),
        modules: &[
            r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
child := p.r
parent := p
"#,
            r#"package probe.p.z
y := 1 if input.c
y := 2 if input.c
"#,
        ],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":["r"],"c":true}"#, r#"1"#),
                (r#"{"ks":["r"],"c":false}"#, r#"1"#),
                (r#"{"ks":[],"c":true}"#, r#"undefined"#),
            ]),
            ("data.probe.parent", &[
                (r#"{"ks":["r"],"c":false}"#, r#"{"r":1}"#),
                (r#"{"ks":[],"c":false}"#, r#"{}"#),
                (r#"{"ks":["r"],"c":true}"#, r#"error; interpreter={"r":1}; eval_query={"r":1}; rvm={"r":1}"#),
            ]),
        ],
    },
    Case {
        name: "subpkg_owner_sibling_default", v0: false, twin: Some(&[]),
        modules: &[
            r#"package probe
default sub.p.r := 0
default sub.t := 5 # kept
x := data.probe.sub
z := sub
"#,
            r#"package probe.sub
p[k] := 1 if { some k in input.ks }
"#,
        ],
        queries: &[
            ("data.probe.x", &[
                (r#"{"ks":[]}"#, r#"{"p":{},"t":5}; rvm={"t":5}"#),
                (r#"{"ks":["a"]}"#, r#"{"p":{"a":1},"t":5}; rvm={"t":5}"#),
                (r#"{"ks":["r"]}"#, r#"{"p":{"r":1},"t":5}; rvm={"t":5}"#),
            ]),
            ("data.probe.z", &[
                (r#"{"ks":[]}"#, r#"{"p":{},"t":5}; interpreter={"t":5}; eval_query={"t":5}; rvm={"t":5}"#),
                (r#"{"ks":["a"]}"#, r#"{"p":{"a":1},"t":5}; interpreter={"t":5}; eval_query={"t":5}; rvm={"t":5}"#),
                (r#"{"ks":["r"]}"#, r#"{"p":{"r":1},"t":5}; interpreter={"t":5}; eval_query={"t":5}; rvm={"t":5}"#),
            ]),
            ("data.probe.sub", &[
                (r#"{"ks":[]}"#, r#"{"p":{},"t":5}; interpreter=error; rvm=error"#),
                (r#"{"ks":["a"]}"#, r#"{"p":{"a":1},"t":5}; interpreter=error; rvm=error"#),
                (r#"{"ks":["r"]}"#, r#"{"p":{"r":1},"t":5}; interpreter=error; rvm=error"#),
            ]),
        ],
    },
    // No rule of the owner can produce `p.r.u`.
    Case {
        name: "no_rule_produces_path", v0: false, twin: Some(&["data.probe.p.r.u"]),
        modules: &[r#"package probe
p[x].t := 2 if { some x in input.xs }
default p.r.u := 0
a := p.r.u
"#],
        queries: &[
            ("data.probe.p.r.u", &[
                (r#"{"xs":[]}"#, r#"undefined"#),
                (r#"{"xs":["r"]}"#, r#"undefined"#),
            ]),
            ("data.probe.a", &[
                (r#"{"xs":[]}"#, r#"undefined"#),
                (r#"{"xs":["r"]}"#, r#"undefined"#),
            ]),
        ],
    },
    // Only `p[k]` can produce `p.r.u`; `p[x].t` cannot.
    // No twin: without the default, the RVM rejects `p.r.u` (see the next case).
    Case {
        name: "only_producing_rules", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := {"u": 5} if { some k in input.ks }
p[x].t := 2 if { some x in input.xs }
default p.r.u := 0
a := p.r.u
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[],"xs":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"],"xs":[]}"#, r#"5"#),
                (r#"{"ks":[],"xs":["r"]}"#, r#"undefined"#),
                (r#"{"ks":["a"],"xs":["b"]}"#, r#"undefined"#),
            ]),
            ("data.probe.p.r.u", &[
                (r#"{"ks":[],"xs":[]}"#, r#"undefined"#),
                (r#"{"ks":["r"],"xs":[]}"#, r#"5"#),
                (r#"{"ks":[],"xs":["r"]}"#, r#"undefined"#),
                (r#"{"ks":["a"],"xs":["b"]}"#, r#"undefined"#),
            ]),
        ],
    },
    // Twin of only_producing_rules without the default.
    Case {
        name: "only_producing_rules_no_default", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := {"u": 5} if { some k in input.ks }
p[x].t := 2 if { some x in input.xs }
a := p.r.u
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[],"xs":[]}"#, r#"undefined; rvm=error"#),
                (r#"{"ks":["r"],"xs":[]}"#, r#"5; rvm=error"#),
                (r#"{"ks":[],"xs":["r"]}"#, r#"undefined; rvm=error"#),
                (r#"{"ks":["a"],"xs":["b"]}"#, r#"undefined; rvm=error"#),
            ]),
            ("data.probe.p.r.u", &[
                (r#"{"ks":[],"xs":[]}"#, r#"undefined; interpreter=error; rvm=error"#),
                (r#"{"ks":["r"],"xs":[]}"#, r#"5; interpreter=error; rvm=error"#),
                (r#"{"ks":[],"xs":["r"]}"#, r#"undefined; interpreter=error; rvm=error"#),
                (r#"{"ks":["a"],"xs":["b"]}"#, r#"undefined; interpreter=error; rvm=error"#),
            ]),
        ],
    },
    // `p.q[j].t` cannot produce `p.q.r.u`, so it is read through `p[k]`.
    // No twin: without the default, regorus is undefined (see the next case).
    Case {
        name: "deeper_rule_cannot_produce", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := {"r": {"u": 9}} if { some k in input.ks }
p.q[j].t := 2 if { some j in input.js }
default p.q.r.u := 0
a := p.q.r.u
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[],"js":[]}"#, r#"undefined"#),
                (r#"{"ks":["q"],"js":[]}"#, r#"9"#),
                (r#"{"ks":[],"js":["r"]}"#, r#"undefined"#),
            ]),
        ],
    },
    // Twin of deeper_rule_cannot_produce without the default.
    Case {
        name: "deeper_rule_cannot_produce_no_default", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := {"r": {"u": 9}} if { some k in input.ks }
p.q[j].t := 2 if { some j in input.js }
a := p.q.r.u
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[],"js":[]}"#, r#"undefined"#),
                (r#"{"ks":["q"],"js":[]}"#, r#"9; interpreter=undefined; eval_query=undefined; rvm=undefined"#),
                (r#"{"ks":[],"js":["r"]}"#, r#"undefined"#),
            ]),
        ],
    },
    // `data.q.all` for `ks` without "r" is omitted: there the RVM puts an
    // Undefined `a` into the object, with or without the default.
    Case {
        name: "virtual_doc_dynamic_lookup", v0: false, twin: Some(&[]),
        modules: &[
            r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
a := p.r
"#,
            r#"package q
all := data.probe
y := data.probe[input.n]
"#,
        ],
        queries: &[
            ("data.q.y", &[
                (r#"{"ks":[],"n":"p"}"#, r#"{}"#),
                (r#"{"ks":["a"],"n":"p"}"#, r#"{"a":1}; rvm suspendable=undefined"#),
                (r#"{"ks":["r"],"n":"p"}"#, r#"{"r":1}; rvm suspendable=undefined"#),
            ]),
            ("data.q.all", &[
                (r#"{"ks":["r"],"n":"p"}"#, r#"{"a":1,"p":{"r":1}}; rvm suspendable=undefined"#),
            ]),
        ],
    },
    // A virtual-document lookup that matches a shadowed default no rule can
    // produce (`p.r.u`) reads the documents as without the default.
    Case {
        name: "virtual_doc_no_producing_rule", v0: false, twin: Some(&[]),
        modules: &[
            r#"package probe
p[x].t := 2 if { some x in input.xs }
default p.r.u := 0
z := 5
"#,
            r#"package q
all := data.probe
y := data.probe[input.n]
w := data.probe.p[input.n]
"#,
        ],
        queries: &[
            ("data.q.all", &[
                (r#"{"xs":[],"n":"z"}"#, r#"{"p":{},"z":5}; interpreter={"z":5}; eval_query={"z":5}; rvm=error"#),
                (r#"{"xs":[],"n":"p"}"#, r#"{"p":{},"z":5}; interpreter={"z":5}; eval_query={"z":5}; rvm=error"#),
                (r#"{"xs":["r"],"n":"r"}"#, r#"{"p":{"r":{"t":2}},"z":5}; rvm=error"#),
            ]),
            ("data.q.y", &[
                (r#"{"xs":[],"n":"z"}"#, r#"5; rvm=error"#),
                (r#"{"xs":[],"n":"p"}"#, r#"{}; interpreter=undefined; eval_query=undefined; rvm=error"#),
                (r#"{"xs":["r"],"n":"r"}"#, r#"undefined; rvm=error"#),
            ]),
            ("data.q.w", &[
                (r#"{"xs":[],"n":"z"}"#, r#"undefined"#),
                (r#"{"xs":[],"n":"p"}"#, r#"undefined"#),
                (r#"{"xs":["r"],"n":"r"}"#, r#"{"t":2}; rvm=undefined"#),
            ]),
        ],
    },
    // `- 1` (unlike `-1`) parses as a negation, which is still a constant key.
    // The default applies (no twin).
    Case {
        name: "negated_number_key", v0: false, twin: None,
        modules: &[r#"package probe
p[- 1] := 1
default p.r := 0
child := p.r
n := count(p)
"#],
        queries: &[
            ("data.probe.child", &[(r#"{}"#, r#"0"#)]),
            ("data.probe.p.r", &[(r#"{}"#, r#"0"#)]),
            ("data.probe.n", &[(r#"{}"#, r#"2; rvm=error"#)]),
        ],
    },
    // An array key is not a constant key.
    Case {
        name: "array_key_owner", v0: false, twin: Some(&["data.probe.child"]),
        modules: &[r#"package probe
p[[1]] := 1 if { input.x }
default p.r := 0
child := p.r
n := count(p)
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"x":false}"#, r#"undefined"#),
                (r#"{"x":true}"#, r#"undefined"#),
            ]),
            ("data.probe.n", &[
                (r#"{"x":false}"#, r#"0"#),
                (r#"{"x":true}"#, r#"1"#),
            ]),
        ],
    },
    // OPA rejects this policy (`default p` conflicts with `p[k]`); the
    // expected values are those without the default, like regorus gives.
    Case {
        name: "default_at_owner_path", v0: false, twin: Some(&[]),
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p := 0
parent := p
"#],
        queries: &[
            ("data.probe.parent", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
            ]),
            ("data.probe.p", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
            ]),
        ],
    },
    // OPA rejects this policy (`default p.q["r"]` conflicts with `p.q.r[k]`);
    // the expected values are those without the default, like regorus gives.
    Case {
        name: "default_bracket_at_owner_path", v0: false, twin: Some(&[]),
        modules: &[r#"package probe
p.q.r[k] := 1 if { some k in input.ks }
default p.q["r"] := 0
y := p.q.r
x := p.q
"#],
        queries: &[
            ("data.probe.y", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
            ]),
            ("data.probe.x", &[
                (r#"{"ks":[]}"#, r#"{"r":{}}; rvm={}"#),
                (r#"{"ks":["a"]}"#, r#"{"r":{"a":1}}; rvm={"a":1}"#),
            ]),
            ("data.probe.p.q.r", &[
                (r#"{"ks":[]}"#, r#"{}"#),
                (r#"{"ks":["a"]}"#, r#"{"a":1}"#),
            ]),
        ],
    },
    // OPA rejects a reference in a default's value even if the default is
    // shadowed. The RVM drops a default whose value fails to evaluate (also
    // when it is not shadowed), so it reads `p[k]`. No twin: OPA's error comes
    // from the default.
    Case {
        name: "shadowed_default_invalid_value", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := input.x
child := p.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":["r"],"x":3}"#, r#"error; rvm=1"#),
            ]),
        ],
    },
    // The bracket form is registered at the owner `p`, beside `p[k]`.
    Case {
        name: "shadowed_default_invalid_value_bracket", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p["r"] := input.x
child := p.r
"#],
        queries: &[
            ("data.probe.child", &[
                (r#"{"ks":["r"],"x":3}"#, r#"error; rvm=1"#),
                (r#"{"ks":[],"x":3}"#, r#"error; rvm=undefined"#),
            ]),
            ("data.probe.p", &[
                (r#"{"ks":["r"],"x":3}"#, r#"error; rvm={"r":1}"#),
            ]),
        ],
    },
    // No head of the owner can produce `p.r.u`, although the value of `p[x].t`
    // contains `r.u`. No twin: see the next case.
    Case {
        name: "no_rule_produces_path_nested_value", v0: false, twin: None,
        modules: &[r#"package probe
p[x].t := {"r": {"u": 1}} if { x := input.x }
default p.r.u := 0
a := p.r.u
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"x":"a"}"#, r#"undefined"#),
                (r#"{"x":"r"}"#, r#"undefined"#),
            ]),
            ("data.probe.p.r.u", &[
                (r#"{"x":"a"}"#, r#"undefined"#),
                (r#"{"x":"r"}"#, r#"undefined"#),
            ]),
        ],
    },
    // Twin of no_rule_produces_path_nested_value without the default, where
    // the RVM reads `p.r.u` from `p[x].t` (nested dynamic keys).
    Case {
        name: "no_rule_produces_path_nested_value_no_default", v0: false, twin: None,
        modules: &[r#"package probe
p[x].t := {"r": {"u": 1}} if { x := input.x }
a := p.r.u
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"x":"a"}"#, r#"undefined; rvm=1"#),
                (r#"{"x":"r"}"#, r#"undefined; rvm=1"#),
            ]),
        ],
    },
    // Reads of `p.a` and `p.b` share the rule of `p`; see
    // `shadowed_default_reads_share_the_owner_rule`.
    Case {
        name: "reads_share_owner_rule", v0: false, twin: Some(&[]),
        modules: &[SHARED_OWNER_RULE],
        queries: &[
            ("data.probe.x", &[
                (r#"{"ks":["a"]}"#, r#"[{"a":1},[1],[]]"#),
                (r#"{"ks":[]}"#, r#"[{},[],[]]"#),
            ]),
        ],
    },
    // OPA rejects a default function at a dynamically keyed rule's path as a
    // conflict. A function's default is not shadowed, so the interpreter
    // still applies it, as before; the RVM reads `p` itself, as before.
    Case {
        name: "default_function_at_owner", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := 1 if { k := input.k }
default p(_) := 2
answer := p(0)
q[k] := 1 if { k := input.k }
default q() := 2
zero := q()
r[k] := 1 if { k := input.k }
default r # A comment before `()`.
() := 2
commented := r()
"#],
        queries: &[
            ("data.probe.answer", &[
                (r#"{"k":"a"}"#, r#"error; interpreter=2; eval_query=2; rvm={"a":1}"#),
                (r#"{}"#, r#"error; interpreter=2; eval_query=2; rvm={}"#),
            ]),
            ("data.probe.zero", &[
                (r#"{"k":"a"}"#, r#"error; interpreter=2; eval_query=2; rvm={"a":1}"#),
                (r#"{}"#, r#"error; interpreter=2; eval_query=2; rvm={}"#),
            ]),
            ("data.probe.commented", &[
                (r#"{"k":"a"}"#, r#"error; interpreter=2; eval_query=2; rvm={"a":1}"#),
                (r#"{}"#, r#"error; interpreter=2; eval_query=2; rvm={}"#),
            ]),
        ],
    },
    // OPA rejects a `with` that replaces part of a virtual document. The
    // interpreter reads the replacement, as before, rather than also
    // evaluating `p[k]`, whose `r` would conflict with it. The RVM does not
    // support `with`.
    Case {
        name: "with_replaces_shadowed_default", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
t if { p.r == 7 with data.probe.p.r as 7 }
u := x if { x := p.r with data.probe.p.r as 7 }
w := x if { x := p.r.s with data.probe.p.r.s as 7 }
"#],
        queries: &[
            ("data.probe.t", &[
                (r#"{"ks":["r"]}"#, r#"error; interpreter=true; eval_query=true"#),
                (r#"{"ks":[]}"#, r#"error; interpreter=true; eval_query=true"#),
            ]),
            ("data.probe.u", &[
                (r#"{"ks":["r"]}"#, r#"error; interpreter=7; eval_query=7"#),
            ]),
            ("data.probe.w", &[
                (r#"{"ks":["r"]}"#, r#"error; interpreter=7; eval_query=7"#),
            ]),
        ],
    },
    // A `with` that replaces the owner replaces the shadowed default's
    // producers; one on an unrelated path does not. The RVM does not support
    // `with`.
    Case {
        name: "with_beside_shadowed_default", v0: false, twin: None,
        modules: &[r#"package probe
p[k] := 1 if { some k in input.ks }
default p.r := 0
ancestor := x if { x := p.r with data.probe.p as {"r": 7} }
omitted := x if { x := p.r with data.probe.p as {"s": 7} }
unrelated := x if { x := p.r with data.probe.other as 7 }
"#],
        queries: &[
            ("data.probe.ancestor", &[(r#"{"ks":["r"]}"#, r#"7; rvm=error"#)]),
            ("data.probe.omitted", &[(r#"{"ks":["r"]}"#, r#"undefined; rvm=error"#)]),
            ("data.probe.unrelated", &[(r#"{"ks":["r"]}"#, r#"1; rvm=error"#)]),
        ],
    },
    // `p["true"]` selects a string key, not the boolean of `default p[true].s`.
    Case {
        name: "bool_and_null_key_default", v0: false, twin: Some(&[]),
        modules: &[r#"package probe
p[k] := {"s": 9} if { some k in input.ks }
default p[true].s := 0
default p[null].s := 0
a := p["true"].s
b := p[true].s
c := p["null"].s
d := p[null].s
"#],
        queries: &[
            ("data.probe.a", &[
                (r#"{"ks":[true]}"#, r#"undefined"#),
                (r#"{"ks":["true"]}"#, r#"9"#),
            ]),
            ("data.probe.b", &[
                (r#"{"ks":[true]}"#, r#"9"#),
                (r#"{"ks":["true"]}"#, r#"undefined"#),
            ]),
            ("data.probe.c", &[
                (r#"{"ks":[null]}"#, r#"undefined"#),
                (r#"{"ks":["null"]}"#, r#"9"#),
            ]),
            ("data.probe.d", &[
                (r#"{"ks":[null]}"#, r#"9"#),
                (r#"{"ks":["null"]}"#, r#"undefined"#),
            ]),
        ],
    },
    // Producers are matched by key and key type beneath the owner. The RVM
    // does not support the nested dynamic key in `p["1"][j].t`.
    Case {
        name: "number_key_beside_string_key_rule", v0: false, twin: Some(&[]),
        modules: &[r#"package probe
p[k] := {"s": 9} if { some k in input.ks }
p["1"][j].t := 2 if { some j in input.js }
default p[1].s := 0
answer := p[1].s
"#],
        queries: &[
            ("data.probe.answer", &[(r#"{"ks":[1],"js":["s"]}"#, r#"9; rvm=error"#)]),
        ],
    },
];

const SHARED_OWNER_RULE: &str = r#"package probe
p[k] := 1 if { some k in input.ks }
default p.a := 0
default p.b := 0
x := [p, [v | v := p.a], [v | v := p.b]]
"#;

fn expected(text: &str, engine: &str) -> Result<Option<Value>> {
    let mut parts = text.split("; ");
    let mut text = parts.next().unwrap_or_default();
    for pin in parts {
        let (prefix, value) = pin.split_once('=').unwrap_or_default();
        assert!(
            ["interpreter", "eval_query", "rvm", "rvm suspendable"].contains(&prefix),
            "unknown pin {pin:?}"
        );
        if engine.starts_with(prefix) {
            text = value;
        }
    }
    Ok(match text {
        "error" => None,
        "undefined" => Some(Value::Undefined),
        _ => Some(Value::from_json_str(text)?),
    })
}

fn eval_all(
    case: &Case,
    modules: &[String],
    query: &str,
    input: &Value,
) -> Result<Vec<(&'static str, Result<Value>)>> {
    let mut engine = Engine::new();
    engine.set_rego_v0(case.v0);
    for (i, module) in modules.iter().enumerate() {
        engine.add_policy(format!("m{i}.rego"), module.clone())?;
    }
    engine.set_input(input.clone());
    let mut results = vec![("interpreter", engine.eval_rule(query.into()))];
    let query_result = engine.eval_query(query.into(), false).map(|results| {
        assert!(results.result.len() <= 1, "{query}: {results:?}");
        let result = results.result.first();
        if let Some(result) = result {
            assert!(result.expressions.len() == 1, "{query}: {result:?}");
            assert!(
                result.bindings == Value::new_object(),
                "{query}: {result:?}"
            );
        }
        let expression = result.and_then(|result| result.expressions.first());
        expression.map_or(Value::Undefined, |expression| expression.value.clone())
    });
    results.push(("eval_query", query_result));
    for (label, mode) in [
        ("rvm run-to-completion", ExecutionMode::RunToCompletion),
        ("rvm suspendable", ExecutionMode::Suspendable),
    ] {
        let result = (|| -> Result<Value> {
            let compiled = engine.compile_with_entrypoint(&query.into())?;
            let program = Compiler::compile_from_policy(&compiled, &[query])?;
            let mut vm = RegoVM::new();
            vm.load_program(program);
            vm.set_input(input.clone());
            vm.set_execution_mode(mode);
            Ok(vm.execute()?)
        })();
        results.push((label, result));
    }
    Ok(results)
}

#[test]
fn default_beneath_dynamic_key_matches_opa() -> Result<()> {
    let mut failures = Vec::new();
    for case in CASES {
        let modules: Vec<String> = case.modules.iter().map(|m| m.to_string()).collect();
        let mut variants = vec![(case.name.to_string(), modules, &[][..])];
        if let Some(skip) = case.twin {
            let stripped = |line: &&str| line.starts_with("default ") && !line.ends_with("# kept");
            let strip = |module: &&str| {
                let lines = module.lines().filter(|line| !stripped(line));
                lines.map(|line| format!("{line}\n")).collect::<String>()
            };
            let name = case.name;
            assert!(
                case.modules.iter().any(|m| m.lines().any(|l| stripped(&l))),
                "{name}: the twin strips no default"
            );
            for query in skip {
                assert!(
                    case.queries.iter().any(|(q, _)| q == query),
                    "{name}: unknown twin skip {query}"
                );
            }
            let modules = case.modules.iter().map(strip).collect();
            variants.push((format!("{} (no default)", case.name), modules, skip));
        }
        for (name, modules, skip) in &variants {
            for (query, rows) in case.queries.iter().filter(|(q, _)| !skip.contains(q)) {
                for (input, want) in *rows {
                    let input_value = Value::from_json_str(input)?;
                    let results = match eval_all(case, modules, query, &input_value) {
                        Ok(results) => results,
                        Err(e) => {
                            failures.push(format!("{name} {query} input={input}: {e:#}"));
                            continue;
                        }
                    };
                    for (engine, got) in results {
                        let ok = match (expected(want, engine)?, &got) {
                            (Some(want), Ok(got)) => *got == want,
                            (None, Err(_)) => true,
                            _ => false,
                        };
                        if !ok {
                            let got =
                                got.map_or_else(|e| format!("error {e:#}"), |v| v.to_string());
                            failures.push(format!(
                                "{name} {query} input={input} {engine}: got {got}, want {want}"
                            ));
                        }
                    }
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    Ok(())
}

/// Reads of shadowed defaults whose producers are all of their base's rules
/// call the base's rule, like reads without the defaults, rather than
/// compiling and evaluating those rules once per path.
#[test]
fn shadowed_default_reads_share_the_owner_rule() -> Result<()> {
    let twin: String = SHARED_OWNER_RULE
        .lines()
        .filter(|line| !line.starts_with("default "))
        .map(|line| format!("{line}\n"))
        .collect();
    let mut rule_counts = vec![];
    for module in [SHARED_OWNER_RULE.to_string(), twin] {
        let mut engine = Engine::new();
        engine.add_policy("m0.rego".into(), module)?;
        let query = "data.probe.x";
        let compiled = engine.compile_with_entrypoint(&query.into())?;
        let program = Compiler::compile_from_policy(&compiled, &[query])?;
        rule_counts.push(program.rule_infos.len());
    }
    assert_eq!(rule_counts[0], rule_counts[1]);
    Ok(())
}

/// Entry points at shadowed defaults index their owner's value in place, so
/// that each uses as many registers as an entry point at a rule path.
#[test]
fn shadowed_default_entry_points_fit_the_register_window() -> Result<()> {
    let mut module = "package probe\np[k] := 1 if { some k in input.ks }\n".to_string();
    let entry_points: Vec<String> = (0..128).map(|i| format!("data.probe.p.r{i}")).collect();
    for i in 0..128 {
        module.push_str(&format!("default p.r{i} := 0\n"));
    }
    let mut engine = Engine::new();
    engine.add_policy("m0.rego".into(), module)?;
    let compiled = engine.compile_with_entrypoint(&entry_points[0].as_str().into())?;
    let entry_points: Vec<&str> = entry_points.iter().map(String::as_str).collect();
    let program = Compiler::compile_from_policy(&compiled, &entry_points)?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_input(Value::from_json_str(r#"{"ks":["r5"]}"#)?);
    assert_eq!(
        vm.execute_entry_point_by_name("data.probe.p.r5")?,
        Value::from(1)
    );
    assert_eq!(
        vm.execute_entry_point_by_name("data.probe.p.r6")?,
        Value::Undefined
    );
    Ok(())
}

/// Each shadowed default is matched only against the rules whose head can
/// produce it, not against every rule of its base, so many constant-keyed
/// rules beside many shadowed defaults, also one key further down, take
/// linear, not quadratic, time.
#[test]
#[cfg_attr(miri, ignore = "large fixture with a wall-clock bound")]
fn shadowed_defaults_scale_with_many_sibling_rules() -> Result<()> {
    const N: usize = 20_000;
    let start = std::time::Instant::now();
    let mut engine = Engine::new();
    let owner = "package probe\np[k] := 1 if { some k in input.ks }\n";
    engine.add_policy("owner.rego".into(), owner.into())?;
    // Spread over modules to stay within the line limit of a policy file.
    for m in 0..N / 2_500 {
        let mut module = "package probe\n".to_string();
        for i in m * 2_500..(m + 1) * 2_500 {
            module.push_str(&format!("p.s{i} := 1\ndefault p.r{i} := 0\n"));
            module.push_str(&format!("p.t.s{i} := 1\ndefault p.t.r{i} := 0\n"));
        }
        engine.add_policy(format!("m{m}.rego"), module)?;
    }
    engine.set_input(Value::from_json_str(r#"{"ks":["r5"]}"#)?);
    assert_eq!(engine.eval_rule("data.probe.p.r5".into())?, Value::from(1));
    let elapsed = start.elapsed();
    // Quadratic matching takes minutes here; linear takes seconds.
    assert!(elapsed.as_secs() < 30, "took {elapsed:?}");
    Ok(())
}
