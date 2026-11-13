// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::*;
use crate::languages::rego::compiler::Compiler;
use crate::Engine;
use alloc::borrow::ToOwned;
use alloc::sync::Arc;
use alloc::vec;

fn compile(modules: &[(&str, &str)], entry_points: &[&str]) -> anyhow::Result<Arc<Program>> {
    let mut engine = Engine::new();
    for &(name, rego) in modules {
        engine.add_policy(name.into(), rego.into())?;
    }
    let first = entry_points.first().copied().unwrap_or_default();
    let compiled = engine.compile_with_entrypoint(&first.into())?;
    Ok(Compiler::compile_from_policy(&compiled, entry_points)?)
}

fn provenance(rego: &str, entry_points: &[&str]) -> anyhow::Result<Provenance> {
    let program = compile(&[("p.rego", rego)], entry_points)?;
    Ok(Provenance::new(&program))
}

/// (owner rule name, body, text, kind, operator, left path, right path)
type Row = (
    String,
    Option<usize>,
    String,
    ConditionKind,
    Option<Operator>,
    Option<String>,
    Option<String>,
);

fn rows(provenance: &Provenance) -> Vec<Row> {
    provenance
        .sites()
        .iter()
        .map(|site| {
            (
                provenance
                    .rule(site.owner.rule)
                    .map(|rule| rule.name.clone())
                    .unwrap_or_default(),
                site.owner.body,
                site.text.clone(),
                site.kind,
                site.operator,
                site.left_path.clone(),
                site.right_path.clone(),
            )
        })
        .collect()
}

fn row(
    rule: &str,
    body: Option<usize>,
    text: &str,
    kind: ConditionKind,
    operator: Option<Operator>,
    left: Option<&str>,
    right: Option<&str>,
) -> Row {
    (
        rule.to_owned(),
        body,
        text.to_owned(),
        kind,
        operator,
        left.map(ToOwned::to_owned),
        right.map(ToOwned::to_owned),
    )
}

fn texts(provenance: &Provenance) -> Vec<&str> {
    provenance
        .sites()
        .iter()
        .map(|site| site.text.as_str())
        .collect()
}

fn at(site: &CheckSite) -> Option<(&str, usize, usize)> {
    site.location
        .as_ref()
        .map(|at| (at.file.as_str(), at.line, at.column))
}

const POLICY: &str = r#"package test
import rego.v1

allow if {
	input.role == "admin"
	some item in input.items
	item.size >= 10
	not is_public
	"read" in input.actions
	input.user.token == data.tokens[input.user.name]
}

is_public if input.public == true
"#;

#[test]
fn complete_rule_and_helper() -> anyhow::Result<()> {
    use ConditionKind::*;
    let provenance = provenance(POLICY, &["data.test.allow"])?;
    let allow = "data.test.allow";
    let body = Some(0);
    assert_eq!(
        rows(&provenance),
        vec![
            row(
                allow,
                body,
                r#"input.role == "admin""#,
                Comparison,
                Some(Operator::Eq),
                Some("input.role"),
                None
            ),
            row(
                allow,
                body,
                "input.items",
                Iteration,
                None,
                Some("input.items"),
                None
            ),
            row(
                allow,
                body,
                "item.size >= 10",
                Comparison,
                Some(Operator::Ge),
                Some("item.size"),
                None
            ),
            row(
                allow,
                body,
                "not is_public",
                Negation,
                None,
                Some("is_public"),
                None
            ),
            row(
                allow,
                body,
                r#""read" in input.actions"#,
                Membership,
                Some(Operator::In),
                None,
                Some("input.actions")
            ),
            row(
                allow,
                body,
                "input.user.token == data.tokens[input.user.name]",
                Comparison,
                Some(Operator::Eq),
                Some("input.user.token"),
                Some("data.tokens[input.user.name]"),
            ),
            row(
                "data.test.is_public",
                body,
                "input.public == true",
                Comparison,
                Some(Operator::Eq),
                Some("input.public"),
                None
            ),
        ]
    );
    let sites = provenance.sites();
    // Tabs count as 4 columns.
    assert_eq!(sites.first().and_then(at), Some(("p.rego", 5, 5)));
    assert_eq!(sites.get(1).and_then(at), Some(("p.rego", 6, 18)));
    assert_eq!(sites.get(6).and_then(at), Some(("p.rego", 13, 14)));
    let ordinals: Vec<usize> = sites.iter().map(|site| site.ordinal).collect();
    assert_eq!(ordinals, vec![0, 1, 2, 3, 4, 5, 0]);
    assert_eq!(
        provenance.rule(0),
        Some(&RuleOwner {
            name: allow.to_owned(),
            kind: RuleKind::Complete
        })
    );
    Ok(())
}

#[test]
fn partial_rules_and_loop_values() -> anyhow::Result<()> {
    use ConditionKind::*;
    let provenance = provenance(
        r#"package test
import rego.v1

deny contains msg if { some r in input.resources; r.public; msg := r.name }

limits[k] := v if { some k, v in input.limits; v > 3 }

names contains n if { n := input.names[_]; n != "root" }
"#,
        &["data.test.deny", "data.test.limits", "data.test.names"],
    )?;
    assert_eq!(
        rows(&provenance),
        vec![
            row(
                "data.test.deny",
                Some(0),
                "input.resources",
                Iteration,
                None,
                Some("input.resources"),
                None
            ),
            row(
                "data.test.deny",
                Some(0),
                "r.public",
                Truthiness,
                None,
                Some("r.public"),
                None
            ),
            row(
                "data.test.limits",
                Some(0),
                "input.limits",
                Iteration,
                None,
                Some("input.limits"),
                None
            ),
            row(
                "data.test.limits",
                Some(0),
                "v > 3",
                Comparison,
                Some(Operator::Gt),
                Some("input.limits[_]"),
                None
            ),
            row(
                "data.test.names",
                Some(0),
                "input.names",
                Iteration,
                None,
                Some("input.names"),
                None
            ),
            row(
                "data.test.names",
                Some(0),
                r#"n != "root""#,
                Comparison,
                Some(Operator::Ne),
                Some("input.names[_]"),
                None
            ),
        ]
    );
    let kinds: Vec<RuleKind> = (0..3)
        .filter_map(|index| provenance.rule(index).map(|rule| rule.kind))
        .collect();
    assert_eq!(
        kinds,
        vec![
            RuleKind::PartialSet,
            RuleKind::PartialObject,
            RuleKind::PartialSet
        ]
    );
    Ok(())
}

#[test]
fn functions_else_and_default() -> anyhow::Result<()> {
    use ConditionKind::*;
    let provenance = provenance(
        r#"package test
import rego.v1

level := 1 if { input.a == `raw é` } else := 2 if { input.b
  == "multi" }

default ok := false
ok if { input.c > 0 }

f(x) := y if { y := x + 1; y > 2 }
g(1) := 2

uses if { f(input.n) > 3; g(1) == 2 }
"#,
        &["data.test.level", "data.test.ok", "data.test.uses"],
    )?;
    let rows = rows(&provenance);
    assert_eq!(
        rows,
        vec![
            row(
                "data.test.level",
                Some(0),
                "input.a == `raw é`",
                Comparison,
                Some(Operator::Eq),
                Some("input.a"),
                None
            ),
            row(
                "data.test.level",
                Some(1),
                "input.b\n  == \"multi\"",
                Comparison,
                Some(Operator::Eq),
                Some("input.b"),
                None
            ),
            row(
                "data.test.ok",
                Some(0),
                "input.c > 0",
                Comparison,
                Some(Operator::Gt),
                Some("input.c"),
                None
            ),
            row(
                "data.test.uses",
                Some(0),
                "f(input.n) > 3",
                Comparison,
                Some(Operator::Gt),
                None,
                None
            ),
            row(
                "data.test.uses",
                Some(0),
                "g(1) == 2",
                Comparison,
                Some(Operator::Eq),
                None,
                None
            ),
            row(
                "data.test.f",
                Some(0),
                "y > 2",
                Comparison,
                Some(Operator::Gt),
                None,
                None
            ),
            // Matching the argument of `g(1)`.
            row(
                "data.test.g",
                None,
                "1",
                Comparison,
                Some(Operator::Eq),
                None,
                None
            ),
        ]
    );
    let f = provenance.sites().get(5).map(|site| site.owner.rule);
    assert_eq!(
        f.and_then(|rule| provenance.rule(rule))
            .map(|rule| rule.kind),
        Some(RuleKind::Function)
    );
    Ok(())
}

#[test]
fn modules_in_several_packages() -> anyhow::Result<()> {
    let program = compile(
        &[
            ("lib.rego", "package lib\nimport rego.v1\n\nadmin if input.role == \"admin\"\n"),
            (
                "main.rego",
                "package main\nimport rego.v1\n\nallow if {\n  data.lib.admin\n  input.ok != false\n}\n",
            ),
        ],
        &["data.main.allow"],
    )?;
    let provenance = Provenance::new(&program);
    assert_eq!(
        texts(&provenance),
        vec![
            "data.lib.admin",
            "input.ok != false",
            r#"input.role == "admin""#
        ]
    );
    let sites = provenance.sites();
    assert_eq!(sites.first().and_then(at), Some(("main.rego", 5, 3)));
    assert_eq!(sites.get(1).and_then(at), Some(("main.rego", 6, 3)));
    assert_eq!(sites.get(2).and_then(at), Some(("lib.rego", 4, 10)));
    assert_eq!(
        sites.first().and_then(|site| site.left_path.as_deref()),
        Some("data.lib.admin")
    );
    Ok(())
}

#[test]
fn string_tokens_and_unicode() -> anyhow::Result<()> {
    let provenance = provenance(
        "package test\nimport rego.v1\n\n# a \"quote in a comment\nallow if {\n  input.name == \"é\"; input.n == 1\n  \"a\\\"b\" == input.s\n  input.m[\"k]\"] == \"#\"\n  input.p == `x\"y`; `é` == input.q\n}\n",
        &["data.test.allow"],
    )?;
    assert_eq!(
        texts(&provenance),
        vec![
            "input.name == \"é\"",
            "input.n == 1",
            "\"a\\\"b\" == input.s",
            "input.m[\"k]\"] == \"#\"",
            "input.p == `x\"y`",
            "`é` == input.q",
        ]
    );
    let paths: Vec<Option<&str>> = provenance
        .sites()
        .iter()
        .map(|site| site.left_path.as_deref().or(site.right_path.as_deref()))
        .collect();
    assert_eq!(
        paths,
        vec![
            Some("input.name"),
            Some("input.n"),
            Some("input.s"),
            Some("input.m[\"k]\"]"),
            Some("input.p"),
            Some("input.q"),
        ]
    );
    let columns: Vec<Option<(&str, usize, usize)>> = provenance.sites().iter().map(at).collect();
    assert_eq!(
        columns,
        vec![
            Some(("p.rego", 6, 3)),
            // "é" is 2 bytes and the lexer counts bytes.
            Some(("p.rego", 6, 23)),
            Some(("p.rego", 7, 3)),
            Some(("p.rego", 8, 3)),
            Some(("p.rego", 9, 3)),
            // A character of a raw string is one column.
            Some(("p.rego", 9, 21)),
        ]
    );
    Ok(())
}

#[test]
fn references_across_lines() -> anyhow::Result<()> {
    let provenance = provenance(
        "package test\nimport rego.v1\n\nallow if {\n  data.roles[\n    input.user\n  ] == \"x\"\n  count(input.items) > 0\n}\n",
        &["data.test.allow"],
    )?;
    assert_eq!(
        rows(&provenance),
        vec![
            row(
                "data.test.allow",
                Some(0),
                "data.roles[\n    input.user\n  ] == \"x\"",
                ConditionKind::Comparison,
                Some(Operator::Eq),
                Some("data.roles[\n    input.user\n  ]"),
                None,
            ),
            row(
                "data.test.allow",
                Some(0),
                "count(input.items) > 0",
                ConditionKind::Comparison,
                Some(Operator::Gt),
                None,
                None,
            ),
        ]
    );
    Ok(())
}

#[test]
fn binding_guards_are_not_checks() -> anyhow::Result<()> {
    let program = compile(
        &[(
            "p.rego",
            "package test\nimport rego.v1\n\nallow if {\n  some [a, b] in input.pairs\n  a == b\n  [x, 1] := input.t\n  x > 0\n}\n",
        )],
        &["data.test.allow"],
    )?;
    let provenance = Provenance::new(&program);
    let mut guards = 0;
    for (pc, instruction) in program.instructions.iter().enumerate() {
        if matches!(
            instruction,
            Instruction::Guard {
                mode: GuardMode::NotUndefined,
                ..
            }
        ) {
            guards += 1;
            assert_eq!(provenance.site_at(pc), None);
        }
    }
    assert!(guards > 0);
    for site in provenance.sites() {
        assert_eq!(provenance.site_at(site.pc), Some(site));
        assert_eq!(provenance.site(site.id), Some(site));
    }
    assert!(texts(&provenance).contains(&"a == b"));
    assert!(texts(&provenance).contains(&"x > 0"));
    Ok(())
}

#[test]
fn ids_are_stable() -> anyhow::Result<()> {
    let entry_points = ["data.test.allow", "data.test.is_public"];
    let first = provenance(POLICY, &entry_points)?;
    let second = provenance(POLICY, &entry_points)?;
    assert_eq!(first, second);
    for (index, site) in first.sites().iter().enumerate() {
        assert_eq!(usize::try_from(site.id.0)?, index);
    }

    // The owner and ordinal of a check do not depend on the other entry
    // points.
    let key = |provenance: &Provenance, site: &CheckSite| {
        (
            provenance
                .rule(site.owner.rule)
                .map(|rule| rule.name.clone()),
            site.owner.definition,
            site.owner.body,
            site.ordinal,
            site.text.clone(),
        )
    };
    let alone = provenance(POLICY, &["data.test.is_public"])?;
    let helper = alone.sites().first().map(|site| key(&alone, site));
    let in_first = first
        .sites()
        .iter()
        .map(|site| key(&first, site))
        .find(|key| key.0.as_deref() == Some("data.test.is_public"));
    assert!(helper.is_some());
    assert_eq!(helper, in_first);
    Ok(())
}

#[test]
fn only_check_instructions_are_sites() -> anyhow::Result<()> {
    let program = compile(&[("p.rego", POLICY)], &["data.test.allow"])?;
    let provenance = Provenance::new(&program);
    // The entry dispatch at pc 0 is not a check, nor is any pc past the end.
    assert_eq!(provenance.site_at(0), None);
    assert_eq!(provenance.site_at(program.instructions.len()), None);
    assert_eq!(provenance.site(SiteId(u32::MAX)), None);
    let first = provenance.sites().first();
    assert!(first.is_some());
    assert_eq!(first.and_then(|site| provenance.site_at(site.pc)), first);
    Ok(())
}

#[test]
fn loop_values_without_keys() -> anyhow::Result<()> {
    use ConditionKind::*;
    let provenance = provenance(
        "package test\nimport rego.v1\n\nall if {\n  every x in input.xs { x > 0 }\n}\n\nany if {\n  some y in input.ys\n  y < 0\n}\n\nkeys if {\n  some k, _ in input.zs\n  k == \"a\"\n}\n",
        &["data.test.all", "data.test.any", "data.test.keys"],
    )?;
    let every = "every x in input.xs { x > 0 }";
    assert_eq!(
        rows(&provenance),
        vec![
            row(
                "data.test.all",
                Some(0),
                every,
                Iteration,
                None,
                Some("input.xs"),
                None
            ),
            row(
                "data.test.all",
                Some(0),
                "x > 0",
                Comparison,
                Some(Operator::Gt),
                Some("input.xs[_]"),
                None
            ),
            // The result of the `every` must be true.
            row(
                "data.test.all",
                Some(0),
                every,
                Truthiness,
                None,
                None,
                None
            ),
            row(
                "data.test.any",
                Some(0),
                "input.ys",
                Iteration,
                None,
                Some("input.ys"),
                None
            ),
            row(
                "data.test.any",
                Some(0),
                "y < 0",
                Comparison,
                Some(Operator::Lt),
                Some("input.ys[_]"),
                None
            ),
            row(
                "data.test.keys",
                Some(0),
                "input.zs",
                Iteration,
                None,
                Some("input.zs"),
                None
            ),
            // A key is not a value read from the collection.
            row(
                "data.test.keys",
                Some(0),
                "k == \"a\"",
                Comparison,
                Some(Operator::Eq),
                None,
                None
            ),
        ]
    );
    Ok(())
}

/// Azure Policy programs have no rule information, so their conditions are
/// not decoded. Reads of the `context` root, such as
/// `[resourceGroup().name]`, therefore never produce a site or a path.
#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_programs_have_no_sites() -> anyhow::Result<()> {
    use crate::languages::azure_policy::{compiler, parser};
    let json = r#"{
  "if": {
    "allOf": [
      { "field": "location", "notEquals": "[resourceGroup().location]" },
      { "value": "[resourceGroup().name]", "like": "rg-prod-*" },
      { "value": "[subscription().subscriptionId]", "equals": "s" }
    ]
  },
  "then": { "effect": "deny" }
}"#;
    let source = crate::lexer::Source::from_contents("policy.json".into(), json.into())?;
    let rule = parser::parse_policy_rule(&source).map_err(|e| anyhow::anyhow!("{e}"))?;
    let program = compiler::compile_policy_rule(&rule)?;
    assert!(program
        .instructions
        .iter()
        .any(|i| matches!(i, Instruction::LoadContext { .. })));
    assert!(program
        .instructions
        .iter()
        .any(|i| matches!(i, Instruction::PolicyCondition { .. })));
    let provenance = Provenance::new(&program);
    assert_eq!(provenance.sites(), &[]);
    assert_eq!(provenance.rule(0), None);
    Ok(())
}

/// Sites are decoded only for Rego programs. A program from another
/// language gets no sites, even when it carries rule information, rather
/// than being read as Rego.
#[test]
fn only_rego_programs_are_decoded() -> anyhow::Result<()> {
    let rego = "package test\nimport rego.v1\n\nallow if input.x == 1\n";
    let program = compile(&[("p.rego", rego)], &["data.test.allow"])?;
    assert_eq!(program.metadata.language, "");
    assert_eq!(Provenance::new(&program).sites().len(), 1);
    for (language, sites) in [("rego", 1), ("cedar", 0), ("azure_policy", 0)] {
        let mut program = (*program).clone();
        program.metadata.language = language.to_owned();
        let provenance = Provenance::new(&program);
        assert_eq!(provenance.sites().len(), sites, "{language}");
        assert_eq!(provenance.rule(0).is_some(), sites > 0, "{language}");
    }
    Ok(())
}

fn allow(body: &str) -> anyhow::Result<Provenance> {
    provenance(
        &alloc::format!("package test\nimport rego.v1\n\nallow if {{\n{body}}}\n"),
        &["data.test.allow"],
    )
}

#[test]
fn statements_that_start_with_brackets() -> anyhow::Result<()> {
    use ConditionKind::*;
    let provenance = allow(
        "  x := 1\n  (input.x + 1) > 2\n  [1] == input.y\n  [a, b] := input.pair\n  a == b\n",
    )?;
    let allow = "data.test.allow";
    assert_eq!(
        rows(&provenance),
        vec![
            row(
                allow,
                Some(0),
                "(input.x + 1) > 2",
                Comparison,
                Some(Operator::Gt),
                None,
                None
            ),
            row(
                allow,
                Some(0),
                "[1] == input.y",
                Comparison,
                Some(Operator::Eq),
                None,
                Some("input.y")
            ),
            // The length check of the destructuring.
            row(
                allow,
                Some(0),
                "[a, b] := input.pair",
                Comparison,
                Some(Operator::Eq),
                None,
                None
            ),
            // The values come from the destructuring, not a reference.
            row(
                allow,
                Some(0),
                "a == b",
                Comparison,
                Some(Operator::Eq),
                None,
                None
            ),
        ]
    );
    let columns: Vec<_> = provenance.sites().iter().map(at).collect();
    assert_eq!(
        columns,
        vec![
            Some(("p.rego", 6, 3)),
            Some(("p.rego", 7, 3)),
            Some(("p.rego", 8, 3)),
            Some(("p.rego", 9, 3)),
        ]
    );
    Ok(())
}

#[test]
fn operations_as_collections() -> anyhow::Result<()> {
    use ConditionKind::*;
    let provenance =
        allow("  some x in input.a | input.b\n  x == 1\n  some y in input.c\n  y == 2\n")?;
    let allow = "data.test.allow";
    assert_eq!(
        rows(&provenance),
        vec![
            row(
                allow,
                Some(0),
                "input.a | input.b",
                Iteration,
                None,
                None,
                None
            ),
            row(
                allow,
                Some(0),
                "x == 1",
                Comparison,
                Some(Operator::Eq),
                None,
                None
            ),
            row(
                allow,
                Some(0),
                "input.c",
                Iteration,
                None,
                Some("input.c"),
                None
            ),
            row(
                allow,
                Some(0),
                "y == 2",
                Comparison,
                Some(Operator::Eq),
                Some("input.c[_]"),
                None
            ),
        ]
    );
    assert_eq!(
        provenance.sites().first().and_then(at),
        Some(("p.rego", 5, 13))
    );
    Ok(())
}

#[test]
fn roots_read_as_their_names() -> anyhow::Result<()> {
    use ConditionKind::*;
    let provenance = allow("  input.expected == input\n  some r in input\n  r == 1\n")?;
    let allow = "data.test.allow";
    assert_eq!(
        rows(&provenance),
        vec![
            row(
                allow,
                Some(0),
                "input.expected == input",
                Comparison,
                Some(Operator::Eq),
                Some("input.expected"),
                Some("input")
            ),
            row(
                allow,
                Some(0),
                "input",
                Iteration,
                None,
                Some("input"),
                None
            ),
            row(
                allow,
                Some(0),
                "r == 1",
                Comparison,
                Some(Operator::Eq),
                Some("input[_]"),
                None
            ),
        ]
    );
    Ok(())
}

#[test]
fn destructured_values_are_not_references() -> anyhow::Result<()> {
    use ConditionKind::*;
    let provenance = allow(
        "  {\"role\": role} := input.user\n  role == \"admin\"\n  some [x, 1] in input.pairs\n  x > 0\n  some k, v in input.m\n  k == v\n",
    )?;
    let allow = "data.test.allow";
    let eq = Some(Operator::Eq);
    assert_eq!(
        rows(&provenance),
        vec![
            row(
                allow,
                Some(0),
                "role == \"admin\"",
                Comparison,
                eq,
                None,
                None
            ),
            row(
                allow,
                Some(0),
                "input.pairs",
                Iteration,
                None,
                Some("input.pairs"),
                None
            ),
            // The length and element checks of the pattern.
            row(allow, Some(0), "[x, 1]", Comparison, eq, None, None),
            row(allow, Some(0), "[x, 1]", Comparison, eq, None, None),
            row(
                allow,
                Some(0),
                "x > 0",
                Comparison,
                Some(Operator::Gt),
                None,
                None
            ),
            row(
                allow,
                Some(0),
                "input.m",
                Iteration,
                None,
                Some("input.m"),
                None
            ),
            row(
                allow,
                Some(0),
                "k == v",
                Comparison,
                eq,
                None,
                Some("input.m[_]")
            ),
        ]
    );
    let columns: Vec<_> = provenance.sites().iter().skip(2).take(2).map(at).collect();
    assert_eq!(
        columns,
        vec![Some(("p.rego", 7, 8)), Some(("p.rego", 7, 8))]
    );
    Ok(())
}

#[test]
fn long_chains_of_bindings() -> anyhow::Result<()> {
    let mut body = String::from("  a0 := input.role\n");
    for i in 1..40 {
        body.push_str(&alloc::format!("  a{i} := a{}\n", i - 1));
    }
    body.push_str("  a39 == \"admin\"\n");
    let provenance = allow(&body)?;
    let paths: Vec<_> = provenance
        .sites()
        .iter()
        .map(|site| (site.left_path.as_deref(), site.right_path.as_deref()))
        .collect();
    assert_eq!(paths, vec![(Some("input.role"), None)]);
    Ok(())
}

#[test]
fn several_definitions_and_clauses() -> anyhow::Result<()> {
    use ConditionKind::*;
    let program = compile(
        &[
            (
                "p.rego",
                "package test\nimport rego.v1\nimport data.lib as l\n\nallow if input.a == 1\nallow if input.b == 2\nallow if {\n  l.x == input.y\n  count([v | some v in input.vs; v > 1]) > 0\n}\nf(1) := 1\nf(x) := 2 if x > 3\ng if f(input.n) == 2\n",
            ),
            ("lib.rego", "package lib\nx := 3\n"),
        ],
        &["data.test.allow", "data.test.g"],
    )?;
    let provenance = Provenance::new(&program);
    let gt = Some(Operator::Gt);
    let eq = Some(Operator::Eq);
    assert_eq!(
        rows(&provenance),
        vec![
            row(
                "data.test.allow",
                Some(0),
                "input.a == 1",
                Comparison,
                eq,
                Some("input.a"),
                None
            ),
            row(
                "data.test.allow",
                Some(0),
                "input.b == 2",
                Comparison,
                eq,
                Some("input.b"),
                None
            ),
            row(
                "data.test.allow",
                Some(0),
                "l.x == input.y",
                Comparison,
                eq,
                Some("l.x"),
                Some("input.y")
            ),
            row(
                "data.test.allow",
                Some(0),
                "input.vs",
                Iteration,
                None,
                Some("input.vs"),
                None
            ),
            row(
                "data.test.allow",
                Some(0),
                "v > 1",
                Comparison,
                gt,
                Some("input.vs[_]"),
                None
            ),
            row(
                "data.test.allow",
                Some(0),
                "count([v | some v in input.vs; v > 1]) > 0",
                Comparison,
                gt,
                None,
                None
            ),
            row(
                "data.test.g",
                Some(0),
                "f(input.n) == 2",
                Comparison,
                eq,
                None,
                None
            ),
            // Matching the argument of `f(1)`.
            row("data.test.f", None, "1", Comparison, eq, None, None),
            row("data.test.f", Some(0), "x > 3", Comparison, gt, None, None),
        ]
    );
    let owners: Vec<_> = provenance
        .sites()
        .iter()
        .map(|site| (site.owner.definition, site.owner.body, site.ordinal))
        .collect();
    assert_eq!(
        owners,
        vec![
            (0, Some(0), 0),
            (1, Some(0), 0),
            (2, Some(0), 0),
            (2, Some(0), 1),
            (2, Some(0), 2),
            (2, Some(0), 3),
            (0, Some(0), 0),
            (0, None, 0),
            (1, Some(0), 0),
        ]
    );
    Ok(())
}

#[test]
fn carriage_returns_and_tabs() -> anyhow::Result<()> {
    let provenance = provenance(
        "package test\r\nimport rego.v1\r\n\r\nallow if {\r\n\tinput.a == 1\r\n\t\tinput.b ==\t2\r\n}\r\n",
        &["data.test.allow"],
    )?;
    assert_eq!(texts(&provenance), vec!["input.a == 1", "input.b ==\t2"]);
    let columns: Vec<_> = provenance.sites().iter().map(at).collect();
    // The lexer counts a tab as 4 columns.
    assert_eq!(
        columns,
        vec![Some(("p.rego", 5, 5)), Some(("p.rego", 6, 9))]
    );
    Ok(())
}

#[test]
fn operations_beside_names_of_the_same_length() -> anyhow::Result<()> {
    // `in input.a | input.` and `x in input.x | input` have the length of
    // the collection too, but do not start and end between operands.
    let provenance = allow(
        "  some x in input.a | input.abc\n  some y in input.a & input.abc\n  some z in input.x | input.ab.c\n",
    )?;
    let loops: Vec<_> = provenance
        .sites()
        .iter()
        .filter(|site| site.kind == ConditionKind::Iteration)
        .map(|site| (site.text.as_str(), at(site)))
        .collect();
    assert_eq!(
        loops,
        vec![
            ("input.a | input.abc", Some(("p.rego", 5, 13))),
            ("input.a & input.abc", Some(("p.rego", 6, 13))),
            ("input.x | input.ab.c", Some(("p.rego", 7, 13))),
        ]
    );
    Ok(())
}

#[test]
fn empty_sets_objects_and_spaced_calls() -> anyhow::Result<()> {
    let provenance = allow(
        "  input.s == set()\n  some {\"a\": 1, \"b\": x} in input.items\n  some y in sort (input.ys)\n  y == x\n",
    )?;
    let sites: Vec<_> = provenance
        .sites()
        .iter()
        .map(|site| (site.text.as_str(), at(site)))
        .collect();
    let pattern = ("{\"a\": 1, \"b\": x}", Some(("p.rego", 6, 8)));
    assert_eq!(
        sites,
        vec![
            ("input.s == set()", Some(("p.rego", 5, 3))),
            ("input.items", Some(("p.rego", 6, 28))),
            // The check of the `"a": 1` field of the pattern.
            pattern,
            ("sort (input.ys)", Some(("p.rego", 7, 13))),
            ("y == x", Some(("p.rego", 8, 3))),
        ]
    );
    Ok(())
}

#[test]
fn spaced_calls_beside_operations_and_statements() -> anyhow::Result<()> {
    // `some x in input.a | sort` and `(input.ys);true` have the length of
    // the collection too.
    let provenance =
        allow("  some x in input.a | sort (input.a)\n  some y in sort (input.ys);true\n")?;
    let loops: Vec<_> = provenance
        .sites()
        .iter()
        .filter(|site| site.kind == ConditionKind::Iteration)
        .map(|site| (site.text.as_str(), at(site)))
        .collect();
    assert_eq!(
        loops,
        vec![
            ("input.a | sort (input.a)", Some(("p.rego", 5, 13))),
            ("sort (input.ys)", Some(("p.rego", 6, 13))),
        ]
    );
    Ok(())
}

#[test]
fn keyed_membership_is_not_reported_as_negation() -> anyhow::Result<()> {
    let provenance = allow(r#"input.subject, "admin" in data.roles"#)?;
    let site = provenance
        .sites()
        .first()
        .ok_or_else(|| anyhow::anyhow!("keyed membership check was not decoded"))?;
    assert_eq!(site.kind, ConditionKind::Membership);
    assert_eq!(site.operator, Some(Operator::In));
    assert_eq!(site.left_path.as_deref(), Some("input.subject"));
    assert_eq!(site.right_path.as_deref(), Some("data.roles"));
    Ok(())
}

#[test]
fn grouped_condition_keeps_its_reference_path() -> anyhow::Result<()> {
    let provenance = allow("(input.flag)")?;
    let site = provenance
        .sites()
        .first()
        .ok_or_else(|| anyhow::anyhow!("grouped condition was not decoded"))?;
    assert_eq!(site.text, "(input.flag)");
    assert_eq!(site.left_path.as_deref(), Some("input.flag"));
    Ok(())
}

#[test]
fn iteration_text_stops_at_statement_and_grouping_delimiters() -> anyhow::Result<()> {
    let provenance = allow("some x in input.a | input.b; x == 1\nsome y in (input.a | input.b)\n")?;
    let loops: Vec<_> = provenance
        .sites()
        .iter()
        .filter(|site| site.kind == ConditionKind::Iteration)
        .map(|site| (site.text.as_str(), at(site)))
        .collect();
    assert_eq!(
        loops,
        vec![
            ("input.a | input.b", Some(("p.rego", 5, 11))),
            ("(input.a | input.b)", Some(("p.rego", 6, 11))),
        ]
    );
    Ok(())
}

#[test]
fn empty_set_iteration_text_excludes_following_statement() -> anyhow::Result<()> {
    let provenance = allow("some x in set(); true")?;
    let site = provenance
        .sites()
        .iter()
        .find(|site| site.kind == ConditionKind::Iteration)
        .ok_or_else(|| anyhow::anyhow!("empty-set iteration was not decoded"))?;
    assert_eq!(site.text, "set()");
    Ok(())
}

#[test]
fn computed_builtin_results_are_not_reference_paths() -> anyhow::Result<()> {
    let provenance = allow(
        "json.verify_schema(input)[0] == true\ninput.values[json.verify_schema(input)[0]] == true",
    )?;
    let sites: Vec<_> = provenance
        .sites()
        .iter()
        .filter(|site| site.kind == ConditionKind::Comparison)
        .collect();
    let computed = sites
        .first()
        .copied()
        .ok_or_else(|| anyhow::anyhow!("first comparison site was not decoded"))?;
    let indexed_reference = sites
        .get(1)
        .copied()
        .ok_or_else(|| anyhow::anyhow!("second comparison site was not decoded"))?;
    assert_eq!(computed.left_path, None);
    assert_eq!(
        indexed_reference.left_path.as_deref(),
        Some("input.values[json.verify_schema(input)[0]]")
    );
    Ok(())
}
