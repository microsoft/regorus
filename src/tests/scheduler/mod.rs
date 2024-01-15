// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::scheduler::*;
use anyhow::{bail, Result};

mod analyzer;

fn make_info(definitions: &[(&'static str, &[&'static str])]) -> StmtInfo<&'static str> {
    StmtInfo {
        definitions: definitions
            .iter()
            .map(|d| Definition {
                var: d.0,
                used_vars: d.1.to_vec(),
            })
            .collect(),
    }
}

fn print_stmts(stmts: &[&str], order: &[u16]) {
    for idx in order.iter().cloned() {
        println!("{}", stmts[idx as usize]);
    }
}

fn check_result(stmts: &[&str], expected: &[&str], r: SortResult) -> Result<()> {
    match r {
        SortResult::Order(order) => {
            print_stmts(stmts, &order);
            for (i, o) in order.iter().cloned().enumerate() {
                println!("{:30}{}", stmts[o as usize], expected[i]);
            }
            for (i, o) in order.iter().cloned().enumerate() {
                assert_eq!(stmts[o as usize], expected[i]);
            }
            Ok(())
        }
        _ => bail!("scheduling failed"),
    }
}

#[test]
fn case1() -> Result<()> {
    let stmts = [
        "v = x",
        "y = [1, 2, 4][_]",
        "x > 10",
        "x = y + z",
        "z = [4, 8][_]",
        "x = 5",
        "v = 1",
    ];

    let expected = [
        "v = 1",
        "v = x",
        "x = 5",
        "x > 10",
        "y = [1, 2, 4][_]",
        "z = [4, 8][_]",
        "x = y + z",
    ];

    let mut infos = vec![
        make_info(&[("v", &["x"]), ("x", &["v"])]),
        make_info(&[("y", &[])]),
        make_info(&[("", &["x"])]),
        make_info(&[("x", &["y", "z"])]),
        make_info(&[("z", &[])]),
        make_info(&[("x", &[])]),
        make_info(&[("v", &[])]),
    ];
    check_result(&stmts[..], &expected[..], schedule(&mut infos, &"")?)
}

#[test]
//#[ignore = "destructing needs more thought. Hoist exprs and introduce new assignments?"]
fn case2() -> Result<()> {
    #[rustfmt::skip]
    let stmts = ["[x, y+1] = [y, p]",
	"value = x + p",
	"y = 5"];

    #[rustfmt::skip]
    let expected = ["y = 5",
	"[x, y+1] = [y, p]",
	"value = x + p"];

    let mut infos = vec![
        make_info(&[("x", &["y"]), ("y", &["x"]), ("p", &["y"])]),
        make_info(&[("value", &["x", "p"])]),
        make_info(&[("y", &[])]),
    ];

    check_result(&stmts[..], &expected[..], schedule(&mut infos, &"")?)
}

#[test]
fn case2_rewritten() -> Result<()> {
    #[rustfmt::skip]
    let stmts = ["y+1 = p",
	"x = y",
	"value = x + p", "y = 5"];

    #[rustfmt::skip]
    let expected = ["y = 5",
	"y+1 = p",
	"x = y",
	"value = x + p"];

    let mut infos = vec![
        make_info(&[("p", &["y"])]),
        make_info(&[("x", &["y"])]),
        make_info(&[("value", &["x", "p"])]),
        make_info(&[("y", &[])]),
    ];

    check_result(&stmts[..], &expected[..], schedule(&mut infos, &"")?)
}

#[test]
fn case3() -> Result<()> {
    #[rustfmt::skip]
    let stmts = [r#"[x, {"p":p}] = [y, t]"#,
	r#"t = {"p":8, "p":6}"#,
	"value = x + y + p",
	"y = 5"];

    #[rustfmt::skip]
    let expected = [r#"t = {"p":8, "p":6}"#,
	"y = 5",
	r#"[x, {"p":p}] = [y, t]"#,
	"value = x + y + p"];

    let mut infos = vec![
        make_info(&[("x", &["y"]), ("p", &["t"])]),
        make_info(&[("t", &[])]),
        make_info(&[("value", &["x", "y", "p"])]),
        make_info(&[("y", &[])]),
    ];

    check_result(&stmts[..], &expected[..], schedule(&mut infos, &"")?)
}

#[test]
#[ignore = "cycle needs to be detected"]
fn case4_cycle() -> Result<()> {
    #[rustfmt::skip]
    let stmts = [r#"[x, {"p":p}] = [y, t]"#,
	r#"t = {"p":x}"#,
	"value = x + y + p",
	"y = 5"];

    // Rest of the statements cannot be processed due to cycle.
    #[rustfmt::skip]
    let expected = ["y = 5"];

    let mut infos = vec![
        make_info(&[("x", &["y"]), ("p", &["t"])]),
        make_info(&[("t", &["x"])]),
        make_info(&[("value", &["x", "y", "p"])]),
        make_info(&[("y", &[])]),
    ];

    // TODO: check cycle
    check_result(&stmts[..], &expected[..], schedule(&mut infos, &"")?)
}

#[test]
fn case4_no_cycle() -> Result<()> {
    #[rustfmt::skip]
    let stmts = [r#"[x, {"p":p}] = [y, {"p":x}]"#,
	"value = x + y + p",
	"y = 5"];

    // Rest of the statements cannot be processed due to cycle.
    #[rustfmt::skip]
    let expected = ["y = 5",
	r#"[x, {"p":p}] = [y, {"p":x}]"#,
	"value = x + y + p"];

    let mut infos = vec![
        make_info(&[("x", &["y"]), ("p", &["x"])]),
        make_info(&[("value", &["x", "y", "p"])]),
        make_info(&[("y", &[])]),
    ];

    // TODO: check cycle
    check_result(&stmts[..], &expected[..], schedule(&mut infos, &"")?)
}

#[test]
fn case4_cycle_removed_via_split_multi_assign() -> Result<()> {
    #[rustfmt::skip]
    let stmts = [r#"x = y"#,
	r#"{"p":p} = t"#,
	r#"t = {"p":x}"#,
	"value = x + y + p",
	"y = 5"];

    // Rest of the statements cannot be processed due to cycle.
    #[rustfmt::skip]
    let expected = ["y = 5",
	r#"x = y"#,
	r#"t = {"p":x}"#,
	r#"{"p":p} = t"#,
	"value = x + y + p"];

    let mut infos = vec![
        make_info(&[("x", &["y"])]),
        make_info(&[("p", &["t"])]),
        make_info(&[("t", &["x"])]),
        make_info(&[("value", &["x", "y", "p"])]),
        make_info(&[("y", &[])]),
    ];

    // TODO: check cycle
    check_result(&stmts[..], &expected[..], schedule(&mut infos, &"")?)
}
