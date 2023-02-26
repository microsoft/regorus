// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{bail, Result};

use regorus::scheduler::*;

fn make_info<'a>(definitions: &[(&'a str, &[&'a str])]) -> StmtInfo<'a> {
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

fn print_stmts(stmts: &[&str], order: &[usize]) {
    for idx in order.iter().cloned() {
        println!("{}", stmts[idx]);
    }
}

fn check_result(stmts: &[&str], expected: &[&str], r: SortResult) -> Result<()> {
    match r {
        SortResult::Order(order) => {
            print_stmts(stmts, &order);
            for (i, o) in order.iter().cloned().enumerate() {
                assert_eq!(stmts[o], expected[i]);
            }
            Ok(())
        }
        _ => bail!("scheduling failed"),
    }
}

#[test]
fn case1() -> Result<()> {
    let stmts = vec![
        "v = x",
        "x > 10",
        "x = y + z",
        "y = [1, 2, 4][_]",
        "z = [4, 8][_]",
        "x = 5",
        "v = 1",
    ];

    let expected = vec![
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
        make_info(&[("", &["x"])]),
        make_info(&[("x", &["y", "z"])]),
        make_info(&[("y", &[])]),
        make_info(&[("z", &[])]),
        make_info(&[("x", &[])]),
        make_info(&[("v", &[])]),
    ];

    check_result(&stmts[..], &expected[..], schedule(&mut infos)?)
}

#[test]
#[ignore = "destructing needs more thought. Hoist exprs and introduce new assignments?"]
fn case2() -> Result<()> {
    let stmts = vec!["[x, y+1] = [y, p]", "value = x + p", "y = 5"];

    let expected = vec!["y = 5", "[x, y+1] = [y, p]", "value = x + p"];

    let mut infos = vec![
        make_info(&[("y", &[])]),
        make_info(&[("value", &["x", "p"])]),
        make_info(&[("x", &["y"]), ("y", &["x"]), ("p", &["y"])]),
    ];

    check_result(&stmts[..], &expected[..], schedule(&mut infos)?)
}

#[test]
fn case2_rewritten() -> Result<()> {
    let stmts = vec!["y+1 = p", "x = y", "value = x + p", "y = 5"];

    let expected = vec!["y = 5", "y+1 = p", "x = y", "value = x + p"];

    let mut infos = vec![
        make_info(&[("p", &["y"])]),
        make_info(&[("x", &["y"])]),
        make_info(&[("value", &["x", "p"])]),
        make_info(&[("y", &[])]),
    ];

    check_result(&stmts[..], &expected[..], schedule(&mut infos)?)
}
