// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use std::collections::{BTreeMap, BTreeSet};

use anyhow::Result;

#[derive(Debug)]
pub struct Definition<'a> {
    // The variable being defined.
    // This can be an empty string to indicate that
    // no variable is being defined.
    pub var: &'a str,

    // Other variables in the same scope used to compute
    // the value of this variable.
    pub used_vars: Vec<&'a str>,
}

#[derive(Debug)]
pub struct StmtInfo<'a> {
    // A statement can define multiple variables.
    // A variable can also be defined by multiple statement.
    pub definitions: Vec<Definition<'a>>,
}

#[derive(Debug)]
pub enum SortResult {
    // The order in which statements must be executed.
    Order(Vec<usize>),
    // List of statements comprising a cycle for a given var.
    Cycle(String, Vec<usize>),
}

pub fn schedule<'a>(infos: &mut [StmtInfo<'a>]) -> Result<SortResult> {
    // Mapping from each var to the list of statements that define it.
    let mut defining_stmts: BTreeMap<&'a str, Vec<usize>> = BTreeMap::new();

    // For each statement, interate through its definitions and add the
    // statement (index) to the var's defining-statements list.
    for (idx, info) in infos.iter().enumerate() {
        for defn in &info.definitions {
            defining_stmts.entry(defn.var).or_default().push(idx);
        }
    }

    // Order of execution for statements.
    let mut order = vec![];
    order.reserve(infos.len());

    // Keep track of whether a var has been defined or not.
    let mut defined_vars = BTreeSet::new();

    // Keep track of whether a statement has been scheduled or not.
    let mut scheduled = vec![false; infos.len()];

    // List of vars to be processed.
    let mut vars_to_process: Vec<&'a str> = defining_stmts.keys().cloned().collect();
    let mut tmp = vec![];

    let mut process_var = |var| {
        let mut stmt_scheduled = false;
        let mut reprocess_var = false;
        // Loop through each statement that defines the var.
        for stmt_idx in defining_stmts.entry(var).or_default().iter().cloned() {
            // If the statement has already been scheduled, skip it.
            if scheduled[stmt_idx] {
                continue;
            }

            // In the statement, find the defn for the var.
            for defn in &infos[stmt_idx].definitions {
                if defn.var != var {
                    continue;
                }

                // If all the vars used by the definition are defined,
                // then the statement can be scheduled.
                if defn.used_vars.iter().all(|v| defined_vars.contains(v)) {
                    // Schedule the statement.
                    order.push(stmt_idx);
                    scheduled[stmt_idx] = true;

                    // Mark the var as defined.
                    defined_vars.insert(var);
                    stmt_scheduled = true;
                } else {
                    reprocess_var = true;
                }
            }
        }

        (stmt_scheduled, reprocess_var)
    };

    let mut done = false;
    while !done {
        done = true;

        // Swap with temporary vec.
        std::mem::swap(&mut vars_to_process, &mut tmp);

        // Loop through each unscheduled var.
        for var in tmp.iter().cloned() {
            let (stmt_scheduled, reprocess_var) = process_var(var);

            if stmt_scheduled {
                done = false;

                // If a statement has been scheduled, it means that the
                // var has been defined. Process "" (statements that don't define any var)
                // to see if any statements that depend on var can be scheduled.
                // Doing so allows statements like `x > 10` to be scheduled immediately after x has been defined.
                // TODO: Also schedule statements like `y = x > 10` immediately.
                process_var("");
            }

            if reprocess_var {
                vars_to_process.push(var);
            }
        }
    }

    // TODO: determine cycles.
    Ok(SortResult::Order(order))
}
