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

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_conditions_keep_json_and_context_paths() -> anyhow::Result<()> {
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
    let sites = provenance.sites();
    assert_eq!(sites.len(), 3);
    let first = sites
        .first()
        .ok_or_else(|| anyhow::anyhow!("first condition"))?;
    assert_eq!(
        first.text,
        r#"{ "field": "location", "notEquals": "[resourceGroup().location]" }"#
    );
    assert_eq!(at(first), Some(("policy.json", 4, 7)));
    assert_eq!(
        first.left_path.as_deref(),
        Some(r#"input["resource"]["location"]"#)
    );
    assert_eq!(
        first.right_path.as_deref(),
        Some(r#"context["resourceGroup"]["location"]"#)
    );
    assert_eq!(first.operator, None);
    assert_eq!(
        first.azure_policy,
        Some(AzurePolicySite {
            operator: Some(crate::rvm::instructions::PolicyOp::NotEquals),
            source_operator: Some(crate::rvm::instructions::PolicyOp::NotEquals),
            field: Some("location".into()),
        })
    );
    let paths: Vec<_> = sites
        .iter()
        .map(|s| (s.left_path.as_deref(), s.right_path.as_deref()))
        .collect();
    assert_eq!(
        paths,
        vec![
            (
                Some(r#"input["resource"]["location"]"#),
                Some(r#"context["resourceGroup"]["location"]"#)
            ),
            (Some(r#"context["resourceGroup"]["name"]"#), None),
            (Some(r#"context["subscription"]["subscriptionId"]"#), None),
        ]
    );
    assert_eq!(
        provenance.rule(0).map(|r| (r.name.as_str(), r.kind)),
        Some(("main", RuleKind::Complete))
    );
    for (index, site) in sites.iter().enumerate() {
        assert_eq!(site.id, SiteId(u32::try_from(index)?));
        assert_eq!(site.ordinal, index);
        assert_eq!(
            site.owner,
            SiteOwner {
                rule: 0,
                definition: 0,
                body: Some(0)
            }
        );
        assert_eq!(provenance.site_at(site.pc), Some(site));
    }
    Ok(())
}

/// A language's instructions must not be interpreted as another language's
/// checks, even when the program carries Rego rule information.
#[test]
fn languages_have_separate_decoders() -> anyhow::Result<()> {
    let rego = "package test\nimport rego.v1\n\nallow if input.x == 1\n";
    let program = compile(&[("p.rego", rego)], &["data.test.allow"])?;
    assert_eq!(program.metadata.language, "");
    assert_eq!(Provenance::new(&program).sites().len(), 1);
    for (language, sites, owner) in [
        ("rego", 1, true),
        ("cedar", 0, false),
        ("azure_policy", 0, true),
    ] {
        let mut program = (*program).clone();
        program.metadata.language = language.to_owned();
        let provenance = Provenance::new(&program);
        assert_eq!(provenance.sites().len(), sites, "{language}");
        assert_eq!(provenance.rule(0).is_some(), owner, "{language}");
    }
    Ok(())
}

#[cfg(feature = "azure_policy")]
fn compile_azure(json: &str) -> anyhow::Result<crate::Rc<Program>> {
    use crate::languages::azure_policy::{compiler, parser};
    let source = crate::lexer::Source::from_contents("policy.json".into(), json.into())?;
    let rule = parser::parse_policy_rule(&source).map_err(|e| anyhow::anyhow!("{e}"))?;
    compiler::compile_policy_rule(&rule)
}

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_count_where_tracks_elements_not_counts() -> anyhow::Result<()> {
    use crate::rvm::instructions::PolicyOp;
    for comparison in [r#""greater": 1"#, r#""greater": 0"#] {
        let condition = alloc::format!(
            r#"{{
    "count": {{
      "field": "items[*]",
      "where": {{ "field": "items[*].state", "equals": "open" }}
    }},
    {comparison}
}}"#
        );
        let json = alloc::format!(r#"{{"if": {condition}, "then": {{ "effect": "deny" }} }}"#);
        let program = compile_azure(&json)?;
        let provenance = Provenance::new(&program);
        let loop_site = provenance
            .sites()
            .iter()
            .find(|s| s.kind == ConditionKind::Iteration)
            .ok_or_else(|| anyhow::anyhow!("count loop"))?;
        assert_eq!(
            loop_site.left_path.as_deref(),
            Some(r#"input["resource"]["items"]"#)
        );
        let predicate = provenance
            .sites()
            .iter()
            .find(|s| s.azure_policy.as_ref().and_then(|p| p.operator) == Some(PolicyOp::Equals))
            .ok_or_else(|| anyhow::anyhow!("where predicate"))?;
        assert_eq!(
            predicate.left_path.as_deref(),
            Some(r#"input["resource"]["items"][_]["state"]"#)
        );
        assert_eq!(
            predicate.text,
            r#"{ "field": "items[*].state", "equals": "open" }"#
        );
        assert_eq!(
            predicate
                .azure_policy
                .as_ref()
                .and_then(|p| p.field.as_deref()),
            Some("items[*].state")
        );
        let comparisons: Vec<_> = provenance
            .sites()
            .iter()
            .filter(|s| s.azure_policy.as_ref().and_then(|p| p.operator) == Some(PolicyOp::Greater))
            .collect();
        assert_eq!(
            comparisons.len(),
            usize::from(comparison == r#""greater": 1"#)
        );
        for site in comparisons {
            assert_eq!(
                site.left_path, None,
                "a computed count is not its collection"
            );
            assert_eq!(site.text, condition);
        }
    }
    Ok(())
}

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_templates_and_reused_registers_do_not_invent_origins() -> anyhow::Result<()> {
    use crate::rvm::instructions::PolicyOp;
    let program = compile_azure(
        r#"{
  "if": {
    "allOf": [
      { "value": "[concat(resourceGroup().name, '-prod')]", "equals": "rg-prod" },
      { "field": "[if(true, 'type', 'name')]", "notEquals": "vm" },
      { "not": { "field": "location", "in": ["eastus"] } },
      { "field": "name", "exists": true }
    ]
  },
  "then": { "effect": "deny" }
}"#,
    )?;
    let provenance = Provenance::new(&program);
    let sites = provenance.sites();
    assert_eq!(
        sites.len(),
        5,
        "no synthetic value guard or logical-block checks"
    );
    let operators: Vec<_> = sites
        .iter()
        .map(|s| s.azure_policy.as_ref().and_then(|p| p.operator))
        .collect();
    assert_eq!(
        operators,
        vec![
            Some(PolicyOp::Equals),
            Some(PolicyOp::NotEquals),
            Some(PolicyOp::In),
            Some(PolicyOp::Not),
            Some(PolicyOp::Exists)
        ]
    );
    let first = sites
        .first()
        .ok_or_else(|| anyhow::anyhow!("computed check"))?;
    assert_eq!(first.left_path, None);
    let second = sites
        .get(1)
        .ok_or_else(|| anyhow::anyhow!("dynamic field"))?;
    assert_eq!(second.left_path, None);
    assert_eq!(
        second
            .azure_policy
            .as_ref()
            .and_then(|p| p.field.as_deref()),
        Some("[if(true, 'type', 'name')]")
    );
    let negation = sites.get(3).ok_or_else(|| anyhow::anyhow!("negation"))?;
    assert_eq!(negation.kind, ConditionKind::Negation);
    assert_eq!(
        negation.right_path, None,
        "register zero is unused by PolicyOp::Not"
    );
    assert_eq!(
        negation.text,
        r#"{ "not": { "field": "location", "in": ["eastus"] } }"#
    );
    Ok(())
}

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_quoted_paths_and_missing_sources() -> anyhow::Result<()> {
    let json = r#"{
	"if": { "field": "tags['a.b[0]\"é']", "equals": "[resourceGroup()['0']]" },
	"then": { "effect": "deny" }
}"#
    .replace('\n', "\r\n");
    let program = compile_azure(&json)?;
    let provenance = Provenance::new(&program);
    let site = provenance
        .sites()
        .first()
        .ok_or_else(|| anyhow::anyhow!("quoted check"))?;
    assert_eq!(at(site), Some(("policy.json", 2, 11)));
    assert_eq!(
        site.left_path.as_deref(),
        Some(r#"input["resource"]["tags"]["a.b[0]\"é"]"#)
    );
    assert_eq!(
        site.right_path.as_deref(),
        Some(r#"context["resourceGroup"]["0"]"#)
    );
    assert_eq!(
        site.azure_policy.as_ref().and_then(|p| p.field.as_deref()),
        Some("tags['a.b[0]\"é']")
    );

    let mut stripped = (*program).clone();
    stripped.sources.clear();
    stripped.instruction_spans.clear();
    let without_sources = Provenance::new(&stripped);
    let stripped_site = without_sources
        .sites()
        .first()
        .ok_or_else(|| anyhow::anyhow!("stripped check"))?;
    assert!(stripped_site.text.is_empty());
    assert_eq!(stripped_site.location, None);
    assert_eq!(stripped_site.left_path, site.left_path);
    assert_eq!(stripped_site.right_path, site.right_path);
    assert_eq!(
        stripped_site.azure_policy.as_ref().and_then(|p| p.operator),
        site.azure_policy.as_ref().and_then(|p| p.operator)
    );
    assert_eq!(
        stripped_site
            .azure_policy
            .as_ref()
            .and_then(|p| p.source_operator),
        None
    );
    let numeric = compile_azure(
        r#"{"if":{"value":"[resourceGroup().names[0]]","equals":"x"},"then":{"effect":"deny"}}"#,
    )?;
    let numeric = Provenance::new(&numeric);
    assert_eq!(
        numeric.sites().first().and_then(|s| s.left_path.as_deref()),
        Some(r#"context["resourceGroup"]["names"][0]"#)
    );
    Ok(())
}

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_aliases_keep_declared_and_normalized_names() -> anyhow::Result<()> {
    use crate::languages::azure_policy::{aliases::AliasRegistry, compiler, parser};
    let mut aliases = AliasRegistry::new();
    aliases.load_from_json(
        r#"[{
        "namespace":"Contoso",
        "resourceTypes":[{"resourceType":"widgets","aliases":[{
            "name":"Contoso/widgets/skuAlias",
            "defaultPath":"properties.sku.name"
        }]}]
    }]"#,
    )?;
    let json = r#"{"if":{"field":"Contoso/widgets/skuAlias","equals":"premium"},"then":{"effect":"deny"}}"#;
    let source = crate::lexer::Source::from_contents("alias.json".into(), json.into())?;
    let rule = parser::parse_policy_rule(&source).map_err(|e| anyhow::anyhow!("{e}"))?;
    let program = compiler::compile_policy_rule_with_aliases(&rule, crate::Rc::new(aliases))?;
    let provenance = Provenance::new(&program);
    let site = provenance
        .sites()
        .first()
        .ok_or_else(|| anyhow::anyhow!("alias site"))?;
    assert_eq!(
        site.left_path.as_deref(),
        Some(r#"input["resource"]["skualias"]"#)
    );
    assert_eq!(
        site.azure_policy.as_ref().and_then(|p| p.field.as_deref()),
        Some("Contoso/widgets/skuAlias")
    );
    Ok(())
}

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_native_template_checks_keep_their_json_owner() -> anyhow::Result<()> {
    use crate::rvm::instructions::PolicyOp;
    let first = r#"{ "field": "[if(equals(resourceGroup().name, 'rg'), 'type', 'name')]", "equals": "vm" }"#;
    let second =
        r#"{ "field": "name", "notEquals": "[if(equals(resourceGroup().name, 'rg'), 'x', 'y')]" }"#;
    let json = alloc::format!(
        r#"{{
  "if": {{ "allOf": [
    {first},
    {second}
  ] }},
  "then": {{ "effect": "deny" }}
}}"#
    );
    let program = compile_azure(&json)?;
    let provenance = Provenance::new(&program);
    assert_eq!(provenance.sites().len(), 4);
    for (index, site) in provenance.sites().iter().enumerate() {
        let (expected, line) = if index < 2 { (first, 3) } else { (second, 4) };
        assert_eq!(site.text, expected, "native template check {index}");
        assert_eq!(at(site), Some(("policy.json", line, 5)));
    }
    let associations: Vec<_> = provenance
        .sites()
        .iter()
        .skip(2)
        .map(|site| {
            (
                site.azure_policy.as_ref().and_then(|p| p.operator),
                site.azure_policy.as_ref().and_then(|p| p.source_operator),
                site.left_path.as_deref(),
                site.right_path.as_deref(),
            )
        })
        .collect();
    assert_eq!(
        associations,
        vec![
            (
                Some(PolicyOp::Equals),
                Some(PolicyOp::NotEquals),
                Some(r#"context["resourceGroup"]["name"]"#),
                None
            ),
            (
                Some(PolicyOp::NotEquals),
                Some(PolicyOp::NotEquals),
                Some(r#"input["resource"]["name"]"#),
                None
            ),
        ]
    );
    Ok(())
}

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_count_restores_its_parent_template_owner() -> anyhow::Result<()> {
    use crate::rvm::instructions::PolicyOp;
    let inner = r#"{"field":"items[*].state","equals":"open"}"#;
    let outer = alloc::format!(
        r#"{{"count":{{"field":"items[*]","where":{inner}}},"greater":"[if(equals(resourceGroup().name, 'rg'), 1, 2)]"}}"#
    );
    let json = alloc::format!(r#"{{"if":{outer},"then":{{"effect":"deny"}}}}"#);
    let program = compile_azure(&json)?;
    let provenance = Provenance::new(&program);
    let comparisons: Vec<_> = provenance
        .sites()
        .iter()
        .filter(|s| s.azure_policy.as_ref().and_then(|p| p.operator) == Some(PolicyOp::Equals))
        .collect();
    assert_eq!(comparisons.len(), 2);
    assert_eq!(comparisons.first().map(|s| s.text.as_str()), Some(inner));
    let restored = comparisons
        .get(1)
        .ok_or_else(|| anyhow::anyhow!("parent template"))?;
    assert_eq!(restored.text, outer);
    assert_eq!(
        restored
            .azure_policy
            .as_ref()
            .and_then(|p| p.source_operator),
        Some(PolicyOp::Greater)
    );
    assert_eq!(
        restored.left_path.as_deref(),
        Some(r#"context["resourceGroup"]["name"]"#)
    );
    Ok(())
}

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_effect_templates_keep_their_json_owner() -> anyhow::Result<()> {
    use crate::rvm::instructions::PolicyOp;
    let then = r#"{"effect":"[if(equals(resourceGroup().location, 'eastus'), 'deny', 'audit')]"}"#;
    let json = alloc::format!(r#"{{"if":{{"field":"type","equals":"vm"}},"then":{then}}}"#);
    let program = compile_azure(&json)?;
    let provenance = Provenance::new(&program);
    let site = provenance
        .sites()
        .iter()
        .find(|s| s.left_path.as_deref() == Some(r#"context["resourceGroup"]["location"]"#))
        .ok_or_else(|| anyhow::anyhow!("effect template"))?;
    assert_eq!(site.text, then);
    assert_eq!(
        site.azure_policy.as_ref().and_then(|p| p.operator),
        Some(PolicyOp::Equals)
    );
    assert_eq!(
        site.azure_policy.as_ref().and_then(|p| p.source_operator),
        None
    );
    assert_eq!(
        site.azure_policy.as_ref().and_then(|p| p.field.as_deref()),
        None
    );
    Ok(())
}

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_optimized_counts_preserve_authored_operators() -> anyhow::Result<()> {
    use crate::rvm::instructions::PolicyOp;
    for (operator, expected) in [("greater", PolicyOp::Greater), ("equals", PolicyOp::Equals)] {
        let condition = alloc::format!(r#"{{"count":{{"field":"items[*]"}},"{operator}":0}}"#);
        let json = alloc::format!(r#"{{"if":{condition},"then":{{"effect":"deny"}}}}"#);
        let program = compile_azure(&json)?;
        let provenance = Provenance::new(&program);
        let site = provenance
            .sites()
            .iter()
            .find(|s| s.kind == ConditionKind::Iteration)
            .ok_or_else(|| anyhow::anyhow!("optimized count"))?;
        assert_eq!(site.text, condition);
        assert_eq!(
            site.azure_policy.as_ref().and_then(|p| p.source_operator),
            Some(expected)
        );
    }
    Ok(())
}

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_nested_counts_keep_inner_collection_sites() -> anyhow::Result<()> {
    let program = compile_azure(
        r#"{"if":{"count":{"field":"a[*].b[*]"},"greater":1},"then":{"effect":"deny"}}"#,
    )?;
    let provenance = Provenance::new(&program);
    let collections: Vec<_> = provenance
        .sites()
        .iter()
        .filter(|s| s.kind == ConditionKind::Iteration)
        .map(|s| s.left_path.as_deref())
        .collect();
    assert_eq!(
        collections,
        vec![
            Some(r#"input["resource"]["a"]"#),
            Some(r#"input["resource"]["a"][_]["b"]"#)
        ]
    );
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
fn operation_iteration_text_respects_root_boundaries() -> anyhow::Result<()> {
    for (body, expected) in [
        ("a|b&cccc", "a|b&cccc"),
        ("a|b&cc", "a|b&cc"),
        ("a&b|cccc", "a&b|cccc"),
        ("(a|b&cccc)", "(a|b&cccc)"),
        ("a|b&cccc; x == 1", "a|b&cccc"),
        ("input.in|input.some", "input.in|input.some"),
        ("a|{input.x in input.xs}", "a|{input.x in input.xs}"),
    ] {
        let provenance = allow(&alloc::format!(
            "a := input.a\nb := input.b\ncc := input.cc\ncccc := input.cccc\n  some x in {body}\n"
        ))?;
        let loops: Vec<_> = provenance
            .sites()
            .iter()
            .filter(|site| site.kind == ConditionKind::Iteration)
            .map(|site| (site.text.as_str(), at(site)))
            .collect();
        assert_eq!(loops, vec![(expected, Some(("p.rego", 9, 13)))], "{body}");
    }
    Ok(())
}

#[test]
fn operation_iteration_text_keeps_contains_identifiers() -> anyhow::Result<()> {
    for expression in [
        "contains|input.b",
        "input.b|contains",
        "input.a|contains&input.b",
        "(contains|input.b)",
        "input.contains|input.b",
        "contains.values|input.b",
        "contains[0]|input.b",
        "input.b|contains[0]",
    ] {
        let provenance = allow(&alloc::format!(
            "  contains := input.a\n  some x in {expression}\n"
        ))?;
        let loops: Vec<_> = provenance
            .sites()
            .iter()
            .filter(|site| site.kind == ConditionKind::Iteration)
            .map(|site| (site.text.as_str(), at(site)))
            .collect();
        assert_eq!(
            loops,
            vec![(expression, Some(("p.rego", 6, 13)))],
            "{expression}"
        );
    }
    Ok(())
}

fn check_operation_iteration_boundary(body: &str, expected: &str) -> anyhow::Result<()> {
    let provenance = allow(&alloc::format!(
        "aa := input.aa\naaa := input.aaa\nb := input.b\nc := input.c\nd := input.d\n  {body}\n"
    ))?;
    let loops: Vec<_> = provenance
        .sites()
        .iter()
        .filter(|site| site.kind == ConditionKind::Iteration)
        .map(|site| (site.text.as_str(), at(site)))
        .collect();
    assert_eq!(loops, vec![(expected, Some(("p.rego", 10, 13)))], "{body}");
    Ok(())
}

#[test]
fn operation_iteration_text_stops_at_semicolons() -> anyhow::Result<()> {
    check_operation_iteration_boundary("some x in aa&b|c; d", "aa&b|c")
}

#[test]
fn operation_iteration_text_stops_at_adjacent_operands() -> anyhow::Result<()> {
    check_operation_iteration_boundary("some x in aaa&b|c\n  d", "aaa&b|c")
}

#[test]
fn operation_iteration_text_keeps_negative_number_boundaries() -> anyhow::Result<()> {
    check_operation_iteration_boundary("some x in aaa&b|c\n  d-1", "aaa&b|c")
}

#[test]
fn operation_iteration_text_stops_at_bracketed_statements() -> anyhow::Result<()> {
    for following in ["[d]", "{d}"] {
        check_operation_iteration_boundary(
            &alloc::format!("some x in aaa&b|c\n{following}"),
            "aaa&b|c",
        )?;
    }
    Ok(())
}

#[test]
fn operation_iteration_boundary_controls() -> anyhow::Result<()> {
    for (body, expected) in [
        ("some x in aaa&b|c\n  d - 1", "aaa&b|c"),
        ("some x in (aa&b|c); d", "(aa&b|c)"),
        ("some x in (aaa&b|c)\n  d", "(aaa&b|c)"),
    ] {
        check_operation_iteration_boundary(body, expected)?;
    }
    Ok(())
}

#[test]
fn operation_candidates_do_not_stop_before_an_operator() {
    for suffix in ["&c", "+c", "- c", "-1", "==c", "[0]", "(c)"] {
        let content = alloc::format!("a|b{suffix}");
        let source = SourceIndex::new("p.rego", &content);
        assert!(!source.bounded(0, 2), "{content}");
        assert!(source.bounded(0, source.tokens.len() - 1), "{content}");
    }
}

#[test]
fn operation_iteration_text_keeps_contains_calls() -> anyhow::Result<()> {
    for expression in ["contains(input.a)|input.b", "contains (input.a)|input.b"] {
        let provenance = provenance(
            &alloc::format!("package test\nimport rego.v1\ncontains(x) := {{x}}\nallow if {{\n  some x in {expression}\n}}\n"),
            &["data.test.allow"],
        )?;
        let loops: Vec<_> = provenance
            .sites()
            .iter()
            .filter(|site| site.kind == ConditionKind::Iteration)
            .map(|site| (site.text.as_str(), at(site)))
            .collect();
        assert_eq!(
            loops,
            vec![(expression, Some(("p.rego", 5, 13)))],
            "{expression}"
        );
    }
    Ok(())
}

#[test]
fn operation_iteration_text_keeps_indirect_and_multiline_calls() -> anyhow::Result<()> {
    for expression in ["input.a|f\n(input.b)", "input.a|data.test[\"f\"] (input.b)"] {
        let provenance = provenance(
            &alloc::format!("package test\nimport rego.v1\nf(x) := {{x}}\nallow if {{\n  some x in {expression}\n}}\n"),
            &["data.test.allow"],
        )?;
        let loops: Vec<_> = provenance
            .sites()
            .iter()
            .filter(|site| site.kind == ConditionKind::Iteration)
            .map(|site| (site.text.as_str(), at(site)))
            .collect();
        assert_eq!(
            loops,
            vec![(expression, Some(("p.rego", 5, 13)))],
            "{expression}"
        );
    }
    Ok(())
}

#[test]
fn operation_text_keeps_rego_v0_future_keyword_identifiers() -> anyhow::Result<()> {
    for identifier in ["contains", "every", "if", "in"] {
        for expression in [
            alloc::format!("{identifier}|input.b"),
            alloc::format!("input.a|{identifier}&input.b"),
        ] {
            let mut engine = Engine::new();
            engine.set_rego_v0(true);
            engine.add_policy(
                "p.rego".into(),
                alloc::format!(
                    "package test\nallow {{\n  {identifier} := input.a\n  {expression}\n}}\n"
                ),
            )?;
            let entry_points = ["data.test.allow"];
            let compiled = engine.compile_with_entrypoint(&entry_points[0].into())?;
            let program = Compiler::compile_from_policy(&compiled, &entry_points)?;
            let provenance = Provenance::new(&program);
            let sites: Vec<_> = provenance
                .sites()
                .iter()
                .map(|site| (site.text.as_str(), at(site)))
                .collect();
            assert_eq!(
                sites,
                vec![(expression.as_str(), Some(("p.rego", 4, 3)))],
                "{expression}"
            );
        }
    }
    Ok(())
}

#[test]
fn operation_text_does_not_end_before_a_binary_operator() -> anyhow::Result<()> {
    // `aaa; a|b` has the same length as `a|b&cccc`, but stops before `&`.
    for expression in ["a|b&cccc", "(a|b)&cccc"] {
        let provenance = allow(&alloc::format!(
            "a := input.a\nb := input.b\ncccc := input.cccc\naaa := input.aaa\n  aaa; {expression}\n"
        ))?;
        let sites: Vec<_> = provenance
            .sites()
            .iter()
            .map(|site| (site.text.as_str(), at(site)))
            .collect();
        assert_eq!(
            sites,
            vec![
                ("aaa", Some(("p.rego", 9, 3))),
                (expression, Some(("p.rego", 9, 8))),
            ],
            "{expression}"
        );
    }
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
fn comparisons_with_aliased_results_are_truthiness_checks() -> anyhow::Result<()> {
    for (symbol, operator) in [
        ("==", Operator::Eq),
        ("!=", Operator::Ne),
        ("<", Operator::Lt),
        ("<=", Operator::Le),
        (">", Operator::Gt),
        (">=", Operator::Ge),
        ("in", Operator::In),
    ] {
        let source =
            alloc::format!("package test\nallow if {{\n  input.left {symbol} input.right\n}}\n");
        let program = compile(&[("p.rego", &source)], &["data.test.allow"])?;
        let site = Provenance::new(&program)
            .sites()
            .first()
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("{symbol}: check was not decoded"))?;
        let kind = if operator == Operator::In {
            ConditionKind::Membership
        } else {
            ConditionKind::Comparison
        };
        assert_eq!((site.kind, site.operator), (kind, Some(operator)));
        assert_eq!(site.left_path.as_deref(), Some("input.left"));
        assert_eq!(site.right_path.as_deref(), Some("input.right"));
        let writer_pc = site
            .pc
            .checked_sub(1)
            .ok_or_else(|| anyhow::anyhow!("{symbol}: check starts at pc 0"))?;
        let (dest, left, right) = match program.instructions.get(writer_pc).copied() {
            Some(Instruction::Eq { dest, left, right })
            | Some(Instruction::Ne { dest, left, right })
            | Some(Instruction::Lt { dest, left, right })
            | Some(Instruction::Le { dest, left, right })
            | Some(Instruction::Gt { dest, left, right })
            | Some(Instruction::Ge { dest, left, right }) => (dest, left, right),
            Some(Instruction::Contains {
                dest,
                collection,
                value,
            }) => (dest, value, collection),
            _ => anyhow::bail!("{symbol}: unexpected comparison lowering"),
        };
        assert!(dest != left && dest != right && left != right);
        // Operand-to-operand aliasing is safe; overwriting either operand is not.
        for (lhs, rhs, overwritten, left_path, right_path) in [
            (left, right, false, Some("input.left"), Some("input.right")),
            (left, left, false, Some("input.left"), Some("input.left")),
            (
                right,
                right,
                false,
                Some("input.right"),
                Some("input.right"),
            ),
            (dest, right, true, None, None),
            (left, dest, true, None, None),
            (dest, dest, true, None, None),
        ] {
            let mut altered = (*program).clone();
            let slot = altered
                .instructions
                .get_mut(writer_pc)
                .ok_or_else(|| anyhow::anyhow!("{symbol}: comparison instruction missing"))?;
            *slot = match operator {
                Operator::Eq => Instruction::Eq {
                    dest,
                    left: lhs,
                    right: rhs,
                },
                Operator::Ne => Instruction::Ne {
                    dest,
                    left: lhs,
                    right: rhs,
                },
                Operator::Lt => Instruction::Lt {
                    dest,
                    left: lhs,
                    right: rhs,
                },
                Operator::Le => Instruction::Le {
                    dest,
                    left: lhs,
                    right: rhs,
                },
                Operator::Gt => Instruction::Gt {
                    dest,
                    left: lhs,
                    right: rhs,
                },
                Operator::Ge => Instruction::Ge {
                    dest,
                    left: lhs,
                    right: rhs,
                },
                Operator::In => Instruction::Contains {
                    dest,
                    collection: rhs,
                    value: lhs,
                },
            };
            let provenance = Provenance::new(&altered);
            let actual = provenance
                .site_at(site.pc)
                .ok_or_else(|| anyhow::anyhow!("{symbol}: altered check was not decoded"))?;
            let expected = if overwritten {
                (ConditionKind::Truthiness, None, None, None)
            } else {
                (kind, Some(operator), left_path, right_path)
            };
            assert_eq!(
                (
                    actual.kind,
                    actual.operator,
                    actual.left_path.as_deref(),
                    actual.right_path.as_deref(),
                ),
                expected,
                "{symbol}: dest={dest}, left={lhs}, right={rhs}"
            );
        }
    }
    Ok(())
}

/// A keyed membership whose registers alias each other is decoded as the
/// negation it is lowered to, as in the VM.
#[test]
fn keyed_membership_with_aliased_registers_is_not_a_membership() -> anyhow::Result<()> {
    let program = compile(
        &[(
            "p.rego",
            "package test\nallow if {\n  input.subject, \"admin\" in data.roles\n}\n",
        )],
        &["data.test.allow"],
    )?;
    let site = Provenance::new(&program)
        .sites()
        .first()
        .cloned()
        .ok_or_else(|| anyhow::anyhow!("keyed membership check was not decoded"))?;
    assert_eq!(site.kind, ConditionKind::Membership);
    let at = |offset: usize| {
        site.pc
            .checked_sub(offset)
            .ok_or_else(|| anyhow::anyhow!("membership starts before pc 0"))
    };
    let (eq_pc, index_pc) = (at(3)?, at(4)?);
    let (
        Some(&Instruction::Eq {
            dest,
            left,
            right: value,
        }),
        Some(&Instruction::Index { container, key, .. }),
    ) = (
        program.instructions.get(eq_pc),
        program.instructions.get(index_pc),
    )
    else {
        anyhow::bail!("unexpected keyed membership lowering");
    };
    let registers = [dest, left, container, key, value];
    for (i, register) in registers.iter().enumerate() {
        assert!(
            !registers.iter().skip(i + 1).any(|other| other == register),
            "{registers:?}"
        );
    }
    // (Index dest = Eq left, Index container, Index key, Eq right)
    let aliases = [
        (key, container, key, value),
        (container, container, key, value),
        (left, container, dest, value),
        (left, dest, key, value),
        (left, container, key, dest),
        (left, container, key, left),
    ];
    for (indexed, collection, member, compared) in aliases {
        let mut altered = (*program).clone();
        if let Some(slot) = altered.instructions.get_mut(index_pc) {
            *slot = Instruction::Index {
                dest: indexed,
                container: collection,
                key: member,
            };
        }
        if let Some(slot) = altered.instructions.get_mut(eq_pc) {
            *slot = Instruction::Eq {
                dest,
                left: indexed,
                right: compared,
            };
        }
        let shape = Provenance::new(&altered)
            .site_at(site.pc)
            .map(|site| (site.kind, site.operator));
        assert_eq!(
            shape,
            Some((ConditionKind::Negation, None)),
            "{indexed} {collection} {member} {compared}"
        );
    }
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
        "array.concat(input.a, input.b)[0] == true\ninput.values[array.concat(input.a, input.b)[0]] == true",
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
        Some("input.values[array.concat(input.a, input.b)[0]]")
    );
    Ok(())
}

/// Only the guard of the loop's own result register is dropped: a guard on
/// another register after the same `LoopNext`, or one whose `LoopNext` doesn't
/// lead back to a `LoopStart`, keeps its Truthiness site.
#[test]
fn only_the_loop_result_guard_is_not_a_site() -> anyhow::Result<()> {
    let program = compile(
        &[(
            "p.rego",
            "package test\nall if {\n  every x in input.xs { x > 0 }\n}\n",
        )],
        &["data.test.all"],
    )?;
    let guard = program
        .instructions
        .windows(2)
        .zip(1_usize..)
        .find_map(|(pair, pc)| match *pair {
            [Instruction::LoopNext {
                body_start,
                loop_end,
            }, Instruction::Guard { register, .. }]
                if usize::from(loop_end) == pc =>
            {
                Some((pc, body_start, register))
            }
            _ => None,
        });
    let Some((pc, body_start, register)) = guard else {
        anyhow::bail!("no loop result guard");
    };
    assert_eq!(loop_result(&program, body_start), Some(register));
    assert_eq!(Provenance::new(&program).site_at(pc), None);

    let mut other = (*program).clone();
    let Some(slot) = other.instructions.get_mut(pc) else {
        anyhow::bail!("guard pc out of range");
    };
    *slot = Instruction::Guard {
        register: register.wrapping_add(1),
        mode: GuardMode::Condition,
    };
    let other_kind = Provenance::new(&other).site_at(pc).map(|site| site.kind);
    assert_eq!(other_kind, Some(ConditionKind::Truthiness));

    let loop_next = pc
        .checked_sub(1)
        .ok_or_else(|| anyhow::anyhow!("guard at pc 0"))?;
    for bad_start in [0, u16::MAX] {
        let mut malformed = (*program).clone();
        let Some(next) = malformed.instructions.get_mut(loop_next) else {
            anyhow::bail!("loop next pc out of range");
        };
        *next = Instruction::LoopNext {
            body_start: bad_start,
            loop_end: u16::try_from(pc)?,
        };
        let malformed_kind = Provenance::new(&malformed)
            .site_at(pc)
            .map(|site| site.kind);
        assert_eq!(
            malformed_kind,
            Some(ConditionKind::Truthiness),
            "body_start {bad_start}"
        );
    }
    Ok(())
}
