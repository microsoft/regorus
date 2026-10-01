// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::{Engine, InvalidRuleRootError, LimitError, PolicyLengthConfig, Source, Value};
use alloc::boxed::Box;
use alloc::format;
use alloc::string::ToString as _;
use alloc::sync::Arc;
use anyhow::Result;
use core::num::{NonZeroU32, NonZeroUsize};
use core::sync::atomic::{AtomicUsize, Ordering};

fn is_invalid_root(error: &anyhow::Error) -> bool {
    error.downcast_ref::<InvalidRuleRootError>().is_some()
}

#[test]
fn has_declared_rule_rooted_at_checks_authored_heads_in_the_exact_module() -> Result<()> {
    let declarations = [
        (
            "conditional.rego",
            "package customer\nmetadata if { false }",
        ),
        ("complete.rego", "package customer\nmetadata := false"),
        (
            "descendant.rego",
            "package customer\nmetadata.parameters.child := null",
        ),
        (
            "default.rego",
            "package customer\ndefault metadata.parameters = false",
        ),
        (
            "default_child.rego",
            "package customer\ndefault metadata.parameters.child = null",
        ),
        (
            "function.rego",
            "package customer\nmetadata.lookup(value) := value",
        ),
        ("set.rego", "package customer\nmetadata contains \"item\""),
        (
            "other_descendant.rego",
            "package customer\nmetadata.other := true",
        ),
    ];

    let mut engine = Engine::new();
    for (path, policy) in declarations {
        engine.add_policy(path.to_string(), policy.to_string())?;
        anyhow::ensure!(
            engine.has_declared_rule_rooted_at(path, "metadata")?,
            "expected metadata declaration in {path}"
        );
    }

    engine.add_policy(
        "lookalike.rego".to_string(),
        "package customer\nmetadataExtra := true".to_string(),
    )?;
    anyhow::ensure!(
        !engine.has_declared_rule_rooted_at("lookalike.rego", "metadata")?,
        "metadata must not match the metadataExtra root"
    );
    anyhow::ensure!(
        !engine.has_declared_rule_rooted_at("lookalike.rego", "meta")?,
        "matching must use exact root components"
    );

    for path in [
        "conditional.rego",
        "complete.rego",
        "descendant.rego",
        "default.rego",
        "default_child.rego",
        "function.rego",
        "set.rego",
        "other_descendant.rego",
    ] {
        anyhow::ensure!(
            !engine.has_declared_rule_rooted_at(path, "params")?,
            "metadata declarations must not count as params in {path}"
        );
    }

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_accepts_exact_dotted_prefixes() -> Result<()> {
    let declarations = [
        (
            "exact.rego",
            "package customer\nmetadata.parameters := false",
            "metadata.parameters",
            true,
        ),
        (
            "descendant.rego",
            "package customer\nmetadata.parameters.child := false",
            "metadata.parameters",
            true,
        ),
        (
            "default.rego",
            "package customer\ndefault metadata.parameters = false",
            "metadata.parameters",
            true,
        ),
        (
            "function.rego",
            "package customer\nmetadata.parameters.lookup(value) := value",
            "metadata.parameters",
            true,
        ),
        (
            "set.rego",
            "package customer\nmetadata.parameters contains \"item\"",
            "metadata.parameters",
            true,
        ),
        (
            "sibling.rego",
            "package customer\nmetadata.other := true",
            "metadata.parameters",
            false,
        ),
        (
            "lookalike.rego",
            "package customer\nmetadata.parametersX := true",
            "metadata.parameters",
            false,
        ),
        (
            "shorter.rego",
            "package customer\nmetadata := true",
            "metadata.parameters",
            false,
        ),
        (
            "body_key.rego",
            "package customer\nmetadata := {\"parameters\": true}",
            "metadata.parameters",
            false,
        ),
        (
            "escaped_string_key.rego",
            r#"package customer
metadata["param\u0065ters"] := true"#,
            "metadata.parameters",
            true,
        ),
        (
            "quoted_dotted_key.rego",
            r#"package customer
metadata["parameters.child"] := true"#,
            "metadata.parameters.child",
            false,
        ),
        (
            "boolean_key.rego",
            "package customer\nmetadata[true] := true",
            "metadata.true",
            false,
        ),
        (
            "null_key.rego",
            "package customer\nmetadata[null] := true",
            "metadata.null",
            false,
        ),
        (
            "number_key.rego",
            "package customer\nmetadata[1] := true",
            "metadata.parameters",
            false,
        ),
        (
            "keyword_field.rego",
            "package customer\nmetadata.if := true",
            "metadata.if",
            true,
        ),
        (
            "boolean_word_field.rego",
            "package customer\nmetadata.true := true",
            "metadata.true",
            true,
        ),
    ];

    let mut engine = Engine::new();
    for (path, policy, _, _) in declarations {
        engine.add_policy(path.to_string(), policy.to_string())?;
    }
    for (path, _, selector, expected) in declarations {
        anyhow::ensure!(
            engine.has_declared_rule_rooted_at(path, selector)? == expected,
            "unexpected dotted-prefix result for {path}"
        );
    }

    engine.add_policy(
        "other_module.rego".to_string(),
        "package customer\nmetadata.parameters.child := true".to_string(),
    )?;
    engine.add_policy(
        "selected_module.rego".to_string(),
        "package customer\nallow := true".to_string(),
    )?;
    anyhow::ensure!(
        !engine.has_declared_rule_rooted_at("selected_module.rego", "metadata.parameters")?,
        "declarations from another module in the same package must not match"
    );

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_preserves_params_behavior_and_excludes_references() -> Result<()> {
    let params_declarations = [
        ("conditional.rego", "package customer\nparams if { false }"),
        ("complete.rego", "package customer\nparams := false"),
        (
            "descendant.rego",
            "package customer\nparams.child.nested := null",
        ),
        ("default.rego", "package customer\ndefault params = false"),
        (
            "default_child.rego",
            "package customer\ndefault params.child = null",
        ),
        (
            "function.rego",
            "package customer\nparams.lookup(value) := value",
        ),
        ("set.rego", "package customer\nparams contains \"item\""),
    ];

    let mut engine = Engine::new();
    for (path, policy) in params_declarations {
        engine.add_policy(path.to_string(), policy.to_string())?;
        anyhow::ensure!(
            engine.has_declared_rule_rooted_at(path, "params")?,
            "expected params declaration in {path}"
        );
        anyhow::ensure!(
            !engine.has_declared_rule_rooted_at(path, "metadata")?,
            "expected no metadata declaration in {path}"
        );
    }

    engine.add_policy(
        "references.rego".to_string(),
        r#"package customer
           import data.shared as metadata
           # metadata.comment := true
           note := "metadata.parameters"
           config := {"metadata": true}
           use := metadata.value
        "#
        .to_string(),
    )?;
    anyhow::ensure!(
        !engine.has_declared_rule_rooted_at("references.rego", "metadata")?,
        "imports, references, comments, strings and object keys are not declarations"
    );

    engine.add_policy(
        "same_package.rego".to_string(),
        "package customer\nmetadata.child := true".to_string(),
    )?;
    anyhow::ensure!(
        !engine.has_declared_rule_rooted_at("references.rego", "metadata")?,
        "same-package rules must not change another module's result"
    );
    anyhow::ensure!(
        engine.has_declared_rule_rooted_at("same_package.rego", "metadata")?,
        "expected the selected same_package.rego declaration"
    );

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_validates_native_root_grammar_after_source_selection() -> Result<()>
{
    let mut engine = Engine::new();
    engine.add_policy(
        "unique.rego".to_string(),
        "package customer\nmetadata := true".to_string(),
    )?;

    for invalid_root in [
        "",
        " ",
        "\tmetadata",
        "metadata ",
        "metadata # trailing comment",
        ".metadata",
        "metadata.",
        "metadata..parameters",
        "metadata .parameters",
        "metadata. parameters",
        "metadata[\"parameters\"]",
        "metadata; other()",
        "metadata := true",
        "true",
        "if",
        "input",
        "data",
    ] {
        let error = engine
            .has_declared_rule_rooted_at("unique.rego", invalid_root)
            .err()
            .ok_or_else(|| anyhow::anyhow!("invalid root selector must fail"))?;
        anyhow::ensure!(
            is_invalid_root(&error),
            "expected InvalidRuleRootError for {invalid_root:?}, got {error:#}"
        );
    }

    for native_identifier in ["contains", "_", "__target__"] {
        anyhow::ensure!(
            !engine.has_declared_rule_rooted_at("unique.rego", native_identifier)?,
            "expected {native_identifier} to follow native rule-reference grammar"
        );
    }

    let missing_source = engine
        .has_declared_rule_rooted_at("missing.rego", "metadata..parameters")
        .err()
        .ok_or_else(|| anyhow::anyhow!("missing source must fail before selector validation"))?;
    anyhow::ensure!(
        !is_invalid_root(&missing_source),
        "missing source must retain source-selection error precedence"
    );

    engine.add_policy(
        "duplicate.rego".to_string(),
        "package customer\nx := true".to_string(),
    )?;
    engine.add_policy(
        "duplicate.rego".to_string(),
        "package customer\nmetadata := true".to_string(),
    )?;
    let duplicate_source = engine
        .has_declared_rule_rooted_at("duplicate.rego", "metadata..parameters")
        .err()
        .ok_or_else(|| anyhow::anyhow!("duplicate source must fail before selector validation"))?;
    anyhow::ensure!(
        !is_invalid_root(&duplicate_source),
        "duplicate source must retain source-selection error precedence"
    );

    anyhow::ensure!(
        Engine::new()
            .add_policy("malformed.rego".to_string(), "package".to_string())
            .is_err(),
        "malformed policy must fail to load"
    );

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_checks_every_head_even_after_a_match() -> Result<()> {
    for (path, policy) in [
        (
            "unclassifiable_before.rego",
            "package customer\nbroken[lookup()] := true\nmetadata := true",
        ),
        (
            "unclassifiable_after.rego",
            "package customer\nmetadata := true\nbroken[lookup()] := true",
        ),
    ] {
        let mut engine = Engine::new();
        engine.add_policy(path.to_string(), policy.to_string())?;
        let error = engine
            .has_declared_rule_rooted_at(path, "metadata")
            .err()
            .ok_or_else(|| {
                anyhow::anyhow!("unclassifiable heads must fail even when another head matches")
            })?;
        anyhow::ensure!(
            !is_invalid_root(&error),
            "head-classification failure must not be classified as an invalid selector"
        );
    }

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_classifies_unresolved_bracket_components() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "dynamic.rego".to_string(),
        "package customer\nmetadata[key] := true".to_string(),
    )?;
    anyhow::ensure!(
        engine.has_declared_rule_rooted_at("dynamic.rego", "metadata")?,
        "a bare root remains decidable before an unresolved bracket component"
    );
    let dynamic_error = engine
        .has_declared_rule_rooted_at("dynamic.rego", "metadata.parameters")
        .err()
        .ok_or_else(|| {
            anyhow::anyhow!("an unresolved bracket component must not be treated as a field")
        })?;
    anyhow::ensure!(
        !is_invalid_root(&dynamic_error),
        "a dynamic head component is a classification error, not a selector error"
    );

    engine.add_policy(
        "dynamic_after_mismatch.rego".to_string(),
        "package customer\nmetadata.other[key] := true".to_string(),
    )?;
    anyhow::ensure!(
        !engine
            .has_declared_rule_rooted_at("dynamic_after_mismatch.rego", "metadata.parameters")?,
        "a known sibling mismatch must be decided before a later dynamic component"
    );

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_checks_unclassifiable_heads_after_dotted_matches() -> Result<()> {
    for (path, policy) in [
        (
            "dotted_unclassifiable_before.rego",
            "package customer\nbroken[lookup()] := true\nmetadata.parameters := true",
        ),
        (
            "dotted_unclassifiable_after.rego",
            "package customer\nmetadata.parameters := true\nbroken[lookup()] := true",
        ),
    ] {
        let mut engine = Engine::new();
        engine.add_policy(path.to_string(), policy.to_string())?;
        let error = engine
            .has_declared_rule_rooted_at(path, "metadata.parameters")
            .err()
            .ok_or_else(|| {
                anyhow::anyhow!("all rule heads must be classified around a dotted match")
            })?;
        anyhow::ensure!(
            !is_invalid_root(&error),
            "head-classification failure must not be classified as an invalid selector"
        );
    }

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_uses_immutable_load_time_parser_context() -> Result<()> {
    let mut engine = Engine::new();
    engine.set_rego_v0(true);
    engine.add_policy(
        "v0.rego".to_string(),
        "package customer\nif := true".to_string(),
    )?;
    engine.add_policy(
        "v0_dotted.rego".to_string(),
        "package customer\nif.child := true".to_string(),
    )?;
    engine.set_rego_v0(false);

    anyhow::ensure!(
        engine.has_declared_rule_rooted_at("v0.rego", "if")?,
        "a later Rego mode change must not alter the loaded module's grammar"
    );
    anyhow::ensure!(
        engine.has_declared_rule_rooted_at("v0_dotted.rego", "if.child")?,
        "dotted parsing must use the module's captured v0 rule-root grammar"
    );

    let clone = engine.clone();
    anyhow::ensure!(
        clone.has_declared_rule_rooted_at("v0.rego", "if")?,
        "cloned engines must share the immutable parser context"
    );
    anyhow::ensure!(
        clone.has_declared_rule_rooted_at("v0_dotted.rego", "if.child")?,
        "cloned engines must preserve dotted selector parsing context"
    );

    engine.set_policy_length_config(PolicyLengthConfig {
        max_col: NonZeroU32::new(1).ok_or_else(|| anyhow::anyhow!("max_col must be non-zero"))?,
        max_file_bytes: NonZeroUsize::new(1)
            .ok_or_else(|| anyhow::anyhow!("max_file_bytes must be non-zero"))?,
        max_lines: NonZeroUsize::new(1)
            .ok_or_else(|| anyhow::anyhow!("max_lines must be non-zero"))?,
    });
    anyhow::ensure!(
        engine.has_declared_rule_rooted_at("v0.rego", "if")?,
        "later policy length limits must not replace the load-time limits"
    );

    let mut imported = Engine::new();
    imported.set_rego_v0(true);
    imported.add_policy(
        "v0_future_keyword.rego".to_string(),
        "package customer\nimport future.keywords.if\nallow := true".to_string(),
    )?;
    imported.set_rego_v0(false);
    let error = imported
        .has_declared_rule_rooted_at("v0_future_keyword.rego", "if")
        .err()
        .ok_or_else(|| anyhow::anyhow!("an imported future keyword is not a valid root"))?;
    anyhow::ensure!(
        is_invalid_root(&error),
        "future-keyword membership must be captured independently of Module.rego_v1"
    );

    let mut imported_every = Engine::new();
    imported_every.set_rego_v0(true);
    imported_every.add_policy(
        "v0_every.rego".to_string(),
        "package customer\nimport future.keywords.every\nallow := true".to_string(),
    )?;
    let imported_every_error = imported_every
        .has_declared_rule_rooted_at("v0_every.rego", "in")
        .err()
        .ok_or_else(|| anyhow::anyhow!("importing every also makes in a future keyword"))?;
    anyhow::ensure!(
        is_invalid_root(&imported_every_error),
        "imported in must be disallowed"
    );

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_enforces_captured_policy_file_size_limit() -> Result<()> {
    const MAX_FILE_BYTES: usize = 32;

    let mut engine = Engine::new();
    engine.set_policy_length_config(PolicyLengthConfig {
        max_col: NonZeroU32::new(64).ok_or_else(|| anyhow::anyhow!("max_col must be non-zero"))?,
        max_file_bytes: NonZeroUsize::new(MAX_FILE_BYTES)
            .ok_or_else(|| anyhow::anyhow!("max_file_bytes must be non-zero"))?,
        max_lines: NonZeroUsize::new(4)
            .ok_or_else(|| anyhow::anyhow!("max_lines must be non-zero"))?,
    });
    engine.add_policy(
        "limits.rego".to_string(),
        "package customer\nx := true".to_string(),
    )?;

    engine.set_policy_length_config(PolicyLengthConfig {
        max_col: NonZeroU32::new(1).ok_or_else(|| anyhow::anyhow!("max_col must be non-zero"))?,
        max_file_bytes: NonZeroUsize::new(1)
            .ok_or_else(|| anyhow::anyhow!("max_file_bytes must be non-zero"))?,
        max_lines: NonZeroUsize::new(1)
            .ok_or_else(|| anyhow::anyhow!("max_lines must be non-zero"))?,
    });

    let below_limit = "a".repeat(31);
    anyhow::ensure!(
        !engine.has_declared_rule_rooted_at("limits.rego", &below_limit)?,
        "a selector one byte below the captured file-size limit should be accepted"
    );

    let at_limit = "a".repeat(MAX_FILE_BYTES);
    anyhow::ensure!(
        !engine.has_declared_rule_rooted_at("limits.rego", &at_limit)?,
        "a selector exactly at the captured file-size limit should be accepted"
    );

    let above_limit = "a".repeat(33);
    let too_many_lines = "a\nb\nc\nd\ne";
    let source_errors = [
        (
            "file-size",
            above_limit.as_str(),
            Source::from_contents_with_limits(
                "<rule-root>".to_string(),
                above_limit.clone(),
                NonZeroUsize::new(MAX_FILE_BYTES)
                    .ok_or_else(|| anyhow::anyhow!("max_file_bytes must be non-zero"))?,
                NonZeroUsize::new(4)
                    .ok_or_else(|| anyhow::anyhow!("max_lines must be non-zero"))?,
            )
            .err()
            .ok_or_else(|| anyhow::anyhow!("selector source should exceed the file-size limit"))?,
        ),
        (
            "line-count",
            too_many_lines,
            Source::from_contents_with_limits(
                "<rule-root>".to_string(),
                too_many_lines.to_string(),
                NonZeroUsize::new(MAX_FILE_BYTES)
                    .ok_or_else(|| anyhow::anyhow!("max_file_bytes must be non-zero"))?,
                NonZeroUsize::new(4)
                    .ok_or_else(|| anyhow::anyhow!("max_lines must be non-zero"))?,
            )
            .err()
            .ok_or_else(|| anyhow::anyhow!("selector source should exceed the line-count limit"))?,
        ),
    ];
    for (limit, selector, expected_error) in source_errors {
        let error = engine
            .has_declared_rule_rooted_at("limits.rego", selector)
            .err()
            .ok_or_else(|| {
                anyhow::anyhow!("a selector source over its captured limits must fail")
            })?;
        anyhow::ensure!(
            !is_invalid_root(&error) && error.downcast_ref::<LimitError>().is_none(),
            "{limit} source-construction failures must retain the operation-error category: {error:#}"
        );
        anyhow::ensure!(
            error.to_string() == expected_error.to_string(),
            "{limit} source-construction error changed: expected {expected_error:#}, got {error:#}"
        );
    }

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_enforces_captured_column_boundary() -> Result<()> {
    let mut engine = Engine::new();
    engine.set_policy_length_config(PolicyLengthConfig {
        max_col: NonZeroU32::new(32).ok_or_else(|| anyhow::anyhow!("max_col must be non-zero"))?,
        max_file_bytes: NonZeroUsize::new(2048)
            .ok_or_else(|| anyhow::anyhow!("max_file_bytes must be non-zero"))?,
        max_lines: NonZeroUsize::new(4)
            .ok_or_else(|| anyhow::anyhow!("max_lines must be non-zero"))?,
    });
    engine.add_policy(
        "columns.rego".to_string(),
        "package customer\nx := true".to_string(),
    )?;

    engine.set_policy_length_config(PolicyLengthConfig {
        max_col: NonZeroU32::new(1).ok_or_else(|| anyhow::anyhow!("max_col must be non-zero"))?,
        max_file_bytes: NonZeroUsize::new(1)
            .ok_or_else(|| anyhow::anyhow!("max_file_bytes must be non-zero"))?,
        max_lines: NonZeroUsize::new(1)
            .ok_or_else(|| anyhow::anyhow!("max_lines must be non-zero"))?,
    });

    for length in [30, 31] {
        let selector = "a".repeat(length);
        anyhow::ensure!(
            !engine.has_declared_rule_rooted_at("columns.rego", &selector)?,
            "an absent identifier ending at or before column 32 should be accepted"
        );
    }

    let selector = "a".repeat(32);
    let error = engine
        .has_declared_rule_rooted_at("columns.rego", &selector)
        .err()
        .ok_or_else(|| {
            anyhow::anyhow!(
                "an identifier advancing from column 1 to column 33 must exceed max_col 32"
            )
        })?;
    anyhow::ensure!(
        is_invalid_root(&error),
        "column-width parse errors should retain invalid-selector mapping: {error:#}"
    );

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_initializes_lexer_with_captured_column_limit() -> Result<()> {
    let mut engine = Engine::new();
    engine.set_policy_length_config(PolicyLengthConfig {
        max_col: NonZeroU32::new(2048)
            .ok_or_else(|| anyhow::anyhow!("max_col must be non-zero"))?,
        max_file_bytes: NonZeroUsize::new(2048)
            .ok_or_else(|| anyhow::anyhow!("max_file_bytes must be non-zero"))?,
        max_lines: NonZeroUsize::new(4)
            .ok_or_else(|| anyhow::anyhow!("max_lines must be non-zero"))?,
    });
    engine.add_policy(
        "wide_columns.rego".to_string(),
        "package customer\nx := true".to_string(),
    )?;

    engine.set_policy_length_config(PolicyLengthConfig {
        max_col: NonZeroU32::new(1).ok_or_else(|| anyhow::anyhow!("max_col must be non-zero"))?,
        max_file_bytes: NonZeroUsize::new(1)
            .ok_or_else(|| anyhow::anyhow!("max_file_bytes must be non-zero"))?,
        max_lines: NonZeroUsize::new(1)
            .ok_or_else(|| anyhow::anyhow!("max_lines must be non-zero"))?,
    });

    let selector = "a".repeat(1024);
    anyhow::ensure!(
        !engine.has_declared_rule_rooted_at("wide_columns.rego", &selector)?,
        "a 1024-character identifier should fit the captured 2048-column limit"
    );

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_preserves_target_effective_v1_without_future_keywords() -> Result<()>
{
    let mut engine = Engine::new();
    engine.set_rego_v0(true);
    engine.add_policy(
        "target_context.rego".to_string(),
        r#"package customer
__target__ := "target.tests.sample_test_target"
if.child := true"#
            .to_string(),
    )?;

    engine.set_rego_v0(false);
    engine.add_policy(
        "ordinary_v1.rego".to_string(),
        "package ordinary\nallow := true".to_string(),
    )?;

    anyhow::ensure!(
        engine.has_declared_rule_rooted_at("target_context.rego", "if.child")?,
        "the __target__ directive enables v1 root restrictions without importing future keywords"
    );
    for reserved_root in ["input", "data"] {
        let error = engine
            .has_declared_rule_rooted_at("target_context.rego", reserved_root)
            .err()
            .ok_or_else(|| {
                anyhow::anyhow!("target modules must retain v1 input/data shadow restrictions")
            })?;
        anyhow::ensure!(
            is_invalid_root(&error),
            "expected v1 root restriction for {reserved_root}, got {error:#}"
        );
    }

    let clone = engine.clone();
    anyhow::ensure!(
        clone.has_declared_rule_rooted_at("target_context.rego", "if.child")?,
        "clones must preserve the target module's actual future-keyword membership"
    );

    let ordinary_v1_error = engine
        .has_declared_rule_rooted_at("ordinary_v1.rego", "if")
        .err()
        .ok_or_else(|| anyhow::anyhow!("an ordinary v1 module imports if as a future keyword"))?;
    anyhow::ensure!(
        is_invalid_root(&ordinary_v1_error),
        "ordinary v1 parsing must continue to reject if as a root"
    );

    Ok(())
}

#[cfg(feature = "std")]
#[test]
fn has_declared_rule_rooted_at_captures_context_when_loading_from_file() -> Result<()> {
    struct TempPolicyFile(std::path::PathBuf);

    impl Drop for TempPolicyFile {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }

    let path = std::env::temp_dir().join(format!(
        "regorus-declared-rule-context-{}.rego",
        std::process::id()
    ));
    std::fs::write(&path, "package customer\nif := true")?;
    let _cleanup = TempPolicyFile(path.clone());
    let source_path = path.to_string_lossy().into_owned();

    let mut engine = Engine::new();
    engine.set_rego_v0(true);
    engine.add_policy_from_file(&path)?;
    engine.set_rego_v0(false);

    anyhow::ensure!(
        engine.has_declared_rule_rooted_at(&source_path, "if")?,
        "file-loaded modules must retain their effective load-time parser context"
    );

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_context_survives_compiled_policy_restoration() -> Result<()> {
    let mut engine = Engine::new();
    engine.set_rego_v0(true);
    engine.add_policy(
        "legacy.rego".to_string(),
        "package legacy\nif := true\nallow := true".to_string(),
    )?;
    engine.add_policy(
        "legacy_dotted.rego".to_string(),
        "package legacy_dotted\nif.child := true".to_string(),
    )?;
    engine.add_policy(
        "future.rego".to_string(),
        "package guarded\nimport future.keywords.if\nactive := true".to_string(),
    )?;

    let entrypoint = "data.legacy.allow".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let mut restored = Engine::new_from_compiled_policy(compiled.inner.clone());

    anyhow::ensure!(
        restored.has_declared_rule_rooted_at("legacy.rego", "if")?,
        "compiled-policy restoration must preserve a v0 module's parser context"
    );
    anyhow::ensure!(
        restored.has_declared_rule_rooted_at("legacy_dotted.rego", "if.child")?,
        "compiled-policy restoration must preserve dotted v0 selector context"
    );
    let error = restored
        .has_declared_rule_rooted_at("future.rego", "if")
        .err()
        .ok_or_else(|| {
            anyhow::anyhow!("compiled-policy restoration must preserve imported keywords")
        })?;
    anyhow::ensure!(is_invalid_root(&error), "future keyword context was lost");

    let interpreter_result = restored.eval_rule("data.legacy.allow".to_string())?;
    let compiled_result = compiled.eval_with_input(Value::new_object())?;
    anyhow::ensure!(
        interpreter_result == Value::Bool(true) && compiled_result == interpreter_result,
        "compiled-policy context transfer must not change interpreter evaluation"
    );

    #[cfg(feature = "rvm")]
    {
        let entry_points = ["data.legacy.allow"];
        let program = crate::languages::rego::compiler::Compiler::compile_from_policy(
            &compiled,
            &entry_points,
        )?;
        let mut vm = crate::rvm::vm::RegoVM::new_with_policy(compiled.clone());
        vm.load_program(program);
        vm.set_data(Value::new_object())?;
        vm.set_input(Value::new_object());
        let rvm_result = vm.execute_entry_point_by_name("data.legacy.allow")?;
        anyhow::ensure!(
            rvm_result == interpreter_result,
            "compiled-policy context transfer must not change RVM evaluation"
        );
    }

    Ok(())
}

#[test]
fn has_declared_rule_rooted_at_does_not_evaluate_rule_bodies() -> Result<()> {
    let calls = Arc::new(AtomicUsize::new(0));
    let extension_calls = calls.clone();
    let mut engine = Engine::new();
    engine.add_extension(
        "count".to_string(),
        0,
        Box::new(move |_| {
            extension_calls.fetch_add(1, Ordering::SeqCst);
            Ok(Value::Bool(true))
        }),
    )?;
    engine.add_policy(
        "extension.rego".to_string(),
        "package customer\nmetadata.parameters := count()".to_string(),
    )?;

    anyhow::ensure!(
        engine.has_declared_rule_rooted_at("extension.rego", "metadata")?,
        "expected metadata declaration"
    );
    anyhow::ensure!(
        engine.has_declared_rule_rooted_at("extension.rego", "metadata.parameters")?,
        "expected the dotted metadata declaration without evaluating its body"
    );
    anyhow::ensure!(
        calls.load(Ordering::SeqCst) == 0,
        "declaration detection must not invoke extensions"
    );

    Ok(())
}
