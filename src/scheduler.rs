// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use std::collections::{BTreeMap, BTreeSet, VecDeque};

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

    let mut queue = VecDeque::new();
    let mut schedule_stmt = |stmt_idx: usize| {
        // Check if the statement has already been scheduled.
        if scheduled[stmt_idx] {
            return None;
        }

        let definitions = &infos[stmt_idx].definitions;

        let can_be_scheduled = if definitions.len() == 1 {
            // Handle the more common case of single definition statements optimally.
            // Check if all the vars used by the definition are previously assigned.
            definitions[0]
                .used_vars
                .iter()
                .all(|uv| defined_vars.contains(uv))
        } else {
            // Set of vars that can be defined in this statement.
            let mut defined_in_stmt = BTreeSet::new();

            // Add each definition to processing queue.
            queue.clear();
            for defn in definitions {
                queue.push_back(defn);
            }

            while !queue.is_empty() {
                let n = queue.len();
                for _ in 0..n {
                    let defn = queue.pop_front().unwrap();
                    // Check if the vars used by this definition are
                    //  1) defined via prior assignments (or)
                    //  2) defined in current statement
                    if defn
                        .used_vars
                        .iter()
                        .all(|uv| defined_vars.contains(uv) || defined_in_stmt.contains(uv))
                    {
                        defined_in_stmt.insert(defn.var);
                    } else {
                        // The definiton must be processed again.
                        queue.push_back(defn);
                    }
                }
                // If no definition became defined, then there is a cycle between
                // the definitions in this statement. The cycle cannot be broken yet.
                if n == queue.len() {
                    break;
                }
            }

            // If the vars used by all the definitions are already defined or
            // can be defined by scheduling this statement, return true.
            queue.is_empty()
        };

        // Schedule the var if possible.
        if can_be_scheduled {
            order.push(stmt_idx);
            scheduled[stmt_idx] = true;

            // For each definition in the statement, mark its var as defined.
            for defn in &infos[stmt_idx].definitions {
                defined_vars.insert(defn.var);
            }
            Some(true)
        } else {
            Some(false)
        }
    };

    let mut process_var = |var| {
        let mut stmt_scheduled = false;
        let mut reprocess_var = false;
        // Loop through each statement that defines the var.
        for stmt_idx in defining_stmts.entry(var).or_default().iter().cloned() {
            match schedule_stmt(stmt_idx) {
                Some(true) => {
                    stmt_scheduled = true;
                }
                Some(false) => {
                    reprocess_var = true;
                }
                None => {
                    // Statement has already been scheduled.
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
