// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::*;
use crate::explain::UnknownPath;
use crate::languages::rego::compiler::Compiler;
use crate::rvm::program::{FunctionInfo, RuleInfo, RuleType};
use crate::rvm::vm::VmError;
use crate::rvm::{Instruction, Program};
use crate::Engine;
use alloc::string::ToString as _;
use alloc::vec;

fn vm(rego: &str) -> anyhow::Result<RegoVM> {
    let mut engine = Engine::new();
    engine.add_policy("p.rego".into(), rego.into())?;
    let compiled = engine.compile_with_entrypoint(&"data.test.allow".into())?;
    let mut vm = RegoVM::new();
    vm.load_program(Compiler::compile_from_policy(
        &compiled,
        &["data.test.allow"],
    )?);
    Ok(vm)
}

fn keys(paths: &[&str]) -> Vec<UnknownPath> {
    paths
        .iter()
        .map(|p| UnknownPath::input_keys(p.split('.')))
        .collect()
}

/// Partially evaluates `data.test.allow` with `input` and unknown
/// dotted `input` paths.
fn pe(rego: &str, input: &str, unknowns: &[&str]) -> anyhow::Result<PartialEvalResult> {
    let mut vm = vm(rego)?;
    vm.set_input(Value::from_json_str(input)?);
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = keys(unknowns);
    vm.set_partial_eval_settings(settings);
    Ok(vm.partial_eval("data.test.allow")?)
}

const TWO_CONDITIONS: &str = r#"package test
allow if {
  input.user.role == "admin"
  input.action == "delete"
}"#;

#[test]
fn reading_an_unknown_root_is_unsupported() -> anyhow::Result<()> {
    let run = |body: &str, root: UnknownRoot| -> anyhow::Result<PartialEvalResult> {
        let mut vm = vm(&format!("package test\nallow if {{ {body} }}"))?;
        vm.set_input(Value::from_json_str(r#"{"k": 1, "s": "xy"}"#)?);
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = vec![UnknownPath::new(root, [PathSegment::Key("u".into())])];
        vm.set_partial_eval_settings(settings);
        Ok(vm.partial_eval("data.test.allow")?)
    };
    let cases = [
        ("input.u", Value::Undefined),
        ("input.u + 1 > 2", Value::Undefined),
        ("input.k == 1", Value::from(true)),
        ("input.k == 2", Value::Undefined),
        (r#"startswith(input.s, "x")"#, Value::from(true)),
        ("count(input) == 2", Value::from(true)),
        ("not input.u", Value::from(true)),
        ("some x in [1, 2]; input.k == x", Value::from(true)),
    ];
    for (body, concrete) in cases {
        let result = run(body, UnknownRoot::Input)?;
        assert_eq!(result.status, ResidualStatus::Unsupported, "{body}");
        assert_eq!(result.result, Value::Undefined, "{body}");
        assert!(result.residual_queries.is_empty(), "{body}");
        let want =
            "partial evaluation unsupported: `input` has unknown paths and is read at p.rego:2:";
        assert!(
            result.warnings.len() == 1 && result.warnings[0].starts_with(want),
            "{body}: {:?}",
            result.warnings
        );
        // With the unknown under the other root, the concrete result is exact.
        let result = run(body, UnknownRoot::Context)?;
        assert_eq!(result.status, ResidualStatus::Exact, "{body}");
        assert_eq!(result.kind, RuleKind::Complete);
        assert_eq!(result.result, concrete, "{body}");
        assert!(result.residual_queries.is_empty(), "{body}");
        assert!(result.warnings.is_empty(), "{body}: {:?}", result.warnings);
    }
    Ok(())
}

#[test]
fn repeated_evaluations_are_isolated() -> anyhow::Result<()> {
    let mut vm = vm(TWO_CONDITIONS)?;
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = keys(&["user", "action"]);
    vm.set_partial_eval_settings(settings.clone());
    let first = vm.partial_eval("data.test.allow")?;
    assert_eq!(first.status, ResidualStatus::Unsupported);
    // An unsupported evaluation leaves nothing behind.
    vm.set_input(Value::from_json_str(
        r#"{"user": {"role": "admin"}, "action": "delete"}"#,
    )?);
    vm.set_partial_eval_settings(PartialEvalSettings::default());
    let concrete = vm.partial_eval("data.test.allow")?;
    assert_eq!(concrete.status, ResidualStatus::Exact);
    assert_eq!(concrete.result, Value::from(true));
    assert!(concrete.warnings.is_empty());
    assert_eq!(
        vm.execute_entry_point_by_name("data.test.allow")?,
        Value::from(true)
    );
    vm.set_input(Value::new_object());
    vm.set_partial_eval_settings(settings);
    assert_eq!(vm.partial_eval("data.test.allow")?, first);
    Ok(())
}

#[test]
fn whole_input_unknown() -> anyhow::Result<()> {
    let mut vm = vm("package test\nallow if input.role == \"admin\"")?;
    let mut settings = PartialEvalSettings::default();
    settings.unknowns = vec![UnknownPath::new(UnknownRoot::Input, [])];
    vm.set_partial_eval_settings(settings);
    // Comparisons with unknown input are not supported yet.
    let result = vm.partial_eval("data.test.allow")?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    vm.set_input(Value::new_object());
    assert!(matches!(
        vm.partial_eval("data.test.allow"),
        Err(ExplainError::UnknownValueSupplied { .. })
    ));
    Ok(())
}

#[test]
fn invalid_unknown_messages_render_paths() {
    let message = |unknowns: &[&str], input: &str| {
        pe(TWO_CONDITIONS, input, unknowns)
            .err()
            .map(|e| e.to_string())
    };
    assert_eq!(
        message(&["user", "user.role"], "{}").as_deref(),
        Some(r#"invalid unknown path `input["user"]["role"]`: overlaps `input["user"]`"#)
    );
    assert_eq!(
        message(&["a.b"], r#"{"a": {"b": 1}}"#).as_deref(),
        Some(r#"a value is supplied for unknown path `input["a"]["b"]`"#)
    );
    assert_eq!(message(&["a.b"], r#"{"a.b": 1}"#), None);
}

#[test]
fn calls_fail_closed() -> anyhow::Result<()> {
    let cases = [
        (
            "allow if f(input.u)\nf(x) if x == 1",
            ResidualStatus::Unsupported,
        ),
        // Any read of an input root with unknowns, until the shadow lands.
        (
            "allow if f(input.k)\nf(x) if x == 1",
            ResidualStatus::Unsupported,
        ),
        ("allow if h\nh if input.u == 1", ResidualStatus::Unsupported),
        // Helpers can't read an input root with unknowns.
        ("allow if h\nh if input.k == 1", ResidualStatus::Unsupported),
        ("allow if h\nh if data.x == null", ResidualStatus::Exact),
        ("allow if h\nh if true", ResidualStatus::Exact),
    ];
    for (rules, want) in cases {
        let rego = format!("package test\n{rules}");
        let r = pe(&rego, r#"{"k": 1}"#, &["u"])?;
        assert_eq!(r.status, want, "{rules}");
        let unsupported = want == ResidualStatus::Unsupported;
        assert_eq!(r.warnings.len(), usize::from(unsupported), "{rules}");
        if unsupported {
            assert_eq!(r.result, Value::Undefined, "{rules}");
        }
        // Warnings point at the policy, not at the entry stub.
        assert!(
            r.warnings
                .iter()
                .all(|w| w.contains(" at p.rego:") && !w.ends_with(":0:0")),
            "{rules}: {:?}",
            r.warnings
        );
    }
    Ok(())
}

#[test]
fn with_is_rejected_by_the_compiler() {
    let rego = "package test\nallow if { input.u == 1 with input as {} }";
    let err = vm(rego).err().map(|e| format!("{e:?}").to_lowercase());
    assert!(err.as_ref().is_some_and(|e| e.contains("with")), "{err:?}");
}

#[test]
fn invalid_unknowns_are_errors() -> anyhow::Result<()> {
    let cases: [(&[&str], &str, &str); 4] = [
        (&["user", "user.role"], "{}", "overlap"),
        (&["user.role", "user"], "{}", "overlap"),
        (&["a", "a"], "{}", "overlap"),
        (&["user.role"], r#"{"user": {"role": "x"}}"#, "supplied"),
    ];
    for (unknowns, input, want) in cases {
        let err = pe(TWO_CONDITIONS, input, unknowns);
        let err = err.err().and_then(|e| e.downcast::<ExplainError>().ok());
        let got = match err {
            Some(ExplainError::InvalidUnknownPath { .. }) => "overlap",
            Some(ExplainError::UnknownValueSupplied { .. }) => "supplied",
            _ => "other",
        };
        assert_eq!(got, want, "{unknowns:?}");
    }
    // Siblings and a supplied sibling value are fine.
    let input = r#"{"user": {"name": "x"}}"#;
    pe(TWO_CONDITIONS, input, &["user.role", "user.id", "action"])?;
    Ok(())
}

#[test]
fn suspendable_mode_is_an_error() -> anyhow::Result<()> {
    let mut vm = vm(TWO_CONDITIONS)?;
    vm.set_execution_mode(ExecutionMode::Suspendable);
    assert_eq!(
        vm.partial_eval("data.test.allow"),
        Err(ExplainError::PartialEvalSuspendable)
    );
    vm.set_execution_mode(ExecutionMode::RunToCompletion);
    vm.partial_eval("data.test.allow")?;
    Ok(())
}

#[cfg(feature = "azure_policy")]
#[test]
fn context_unknowns_fail_closed() -> anyhow::Result<()> {
    use crate::languages::azure_policy::{compiler, parser};
    let run = |condition: &str| -> anyhow::Result<PartialEvalResult> {
        let json = format!(r#"{{"if": {condition}, "then": {{"effect": "deny"}}}}"#);
        let source = crate::lexer::Source::from_contents("policy.json".into(), json)?;
        let rule = parser::parse_policy_rule(&source).map_err(|e| anyhow::anyhow!("{e}"))?;
        let program = compiler::compile_policy_rule(&rule)?;
        let mut vm = RegoVM::new();
        vm.load_program(alloc::sync::Arc::new((*program).clone()));
        vm.set_input(Value::from_json_str(
            r#"{"resource": {}, "parameters": {}}"#,
        )?);
        vm.set_context(Value::from_json_str(
            r#"{"resourceGroup": {"location": "eastus"}}"#,
        )?);
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = vec![UnknownPath::new(
            UnknownRoot::Context,
            [
                PathSegment::Key("resourceGroup".into()),
                PathSegment::Key("name".into()),
            ],
        )];
        vm.set_partial_eval_settings(settings);
        Ok(vm.partial_eval("main")?)
    };
    let name = r#"{"value": "[resourceGroup().name]", "equals": "rg"}"#;
    let result = run(name)?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    assert!(
        result.warnings.len() == 1 && result.warnings[0].contains("`context` has unknown paths"),
        "{:?}",
        result.warnings
    );
    // Any read of a context root with unknowns, until the shadow lands.
    let location = r#"{"value": "[resourceGroup().location]", "equals": "eastus"}"#;
    let result = run(location)?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    let field = r#"{"field": "type", "equals": "x"}"#;
    let result = run(field)?;
    assert_eq!(result.status, ResidualStatus::Exact);
    Ok(())
}

#[test]
fn a_recorder_cannot_be_installed() -> anyhow::Result<()> {
    struct Recorder;
    impl crate::explain::ExplanationRecorder for Recorder {}
    let mut vm = vm(TWO_CONDITIONS)?;
    vm.set_explanation_recorder(Box::new(Recorder));
    assert_eq!(
        vm.partial_eval("data.test.allow"),
        Err(ExplainError::PartialEvalWithRecorder)
    );
    assert!(vm.take_explanation_recorder().is_some());
    assert_eq!(
        vm.partial_eval("data.test.allow")?.status,
        ResidualStatus::Exact
    );
    Ok(())
}

#[test]
fn other_errors_after_a_read_are_unsupported() -> anyhow::Result<()> {
    // Compiled rule bodies absorb non-fatal errors, so the error is raised
    // outside a rule.
    let mut program = Program::new();
    program.add_instruction(Instruction::LoadInput { dest: 0 }, None);
    program.add_instruction(Instruction::LoadTrue { dest: 0 }, None);
    program.add_instruction(Instruction::LoadNull { dest: 1 }, None);
    program.add_instruction(
        Instruction::Lt {
            dest: 0,
            left: 0,
            right: 1,
        },
        None,
    );
    program.add_instruction(Instruction::Return { value: 0 }, None);
    program.add_entry_point("entry".into(), 0);
    let program = alloc::sync::Arc::new(program);
    let run = |unknowns: Vec<UnknownPath>| {
        let mut vm = RegoVM::new();
        vm.set_strict_builtin_errors(true);
        vm.load_program(program.clone());
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = unknowns;
        vm.set_partial_eval_settings(settings);
        vm.partial_eval("entry")
    };
    let result = run(keys(&["u"]))?;
    assert_eq!(result.status, ResidualStatus::Unsupported);
    assert_eq!(result.warnings.len(), 1);
    let context_u = UnknownPath::new(UnknownRoot::Context, [PathSegment::Key("u".into())]);
    for unknowns in [vec![], vec![context_u]] {
        let result = run(unknowns.clone());
        assert!(
            matches!(
                result,
                Err(ExplainError::Vm(VmError::ArithmeticError { .. }))
            ),
            "{unknowns:?}: {result:?}"
        );
    }
    Ok(())
}

#[test]
fn entry_points_returning_an_unknown_rule_kind_are_rejected() -> anyhow::Result<()> {
    let run = |entry_pc: usize, rule_type: RuleType, function: bool| {
        let mut program = Program::new();
        program.add_instruction(Instruction::LoadInput { dest: 0 }, None);
        program.add_instruction(Instruction::Return { value: 0 }, None);
        program.add_entry_point("entry".into(), entry_pc);
        let mut rule = RuleInfo::new(
            "data.test.r".into(),
            rule_type,
            crate::Rc::new(vec![]),
            0,
            1,
        );
        if function {
            rule.function_info = Some(FunctionInfo {
                param_names: vec![],
                num_params: 0,
            });
        }
        program.rule_infos.push(rule);
        let mut vm = RegoVM::new();
        vm.load_program(alloc::sync::Arc::new(program));
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = keys(&["u"]);
        vm.set_partial_eval_settings(settings);
        vm.partial_eval("entry")
    };
    assert_eq!(run(0, RuleType::Complete, false)?.kind, RuleKind::Complete);
    let unknown_kind = Err(ExplainError::PartialEvalUnknownRuleKind {
        entry: "entry".to_string(),
    });
    assert_eq!(run(0, RuleType::PartialSet, false), unknown_kind);
    assert_eq!(run(0, RuleType::Complete, true), unknown_kind);
    // A malformed entry point fails as the VM reports it.
    let result = run(9, RuleType::PartialSet, false);
    assert!(
        matches!(
            result,
            Err(ExplainError::Vm(VmError::EntryPointPcOutOfBounds { .. }))
        ),
        "{result:?}"
    );
    let mut program = Program::new();
    program.add_instruction(
        Instruction::CallRule {
            dest: 0,
            rule_index: 5,
        },
        None,
    );
    program.add_instruction(Instruction::Return { value: 0 }, None);
    program.add_entry_point("entry".into(), 0);
    program.rule_infos.push(RuleInfo::new(
        "data.test.r".into(),
        RuleType::PartialSet,
        crate::Rc::new(vec![]),
        0,
        1,
    ));
    let mut vm = RegoVM::new();
    vm.load_program(alloc::sync::Arc::new(program));
    let result = vm.partial_eval("entry");
    assert!(
        matches!(
            result,
            Err(ExplainError::Vm(VmError::RuleIndexOutOfBounds { .. }))
        ),
        "{result:?}"
    );
    Ok(())
}

#[test]
fn fatal_errors_are_not_unsupported() -> anyhow::Result<()> {
    let run = |rego: &str, unknown: &UnknownPath, max_instructions: Option<usize>| {
        let mut vm = vm(rego)?;
        vm.set_input(Value::from_json_str(
            r#"{"k": 1, "a": 1e308, "p": "([a-z]{1,64}){1,64}"}"#,
        )?);
        if let Some(max) = max_instructions {
            vm.set_max_instructions(max);
        }
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = vec![unknown.clone()];
        vm.set_partial_eval_settings(settings);
        anyhow::Ok(vm.partial_eval("data.test.allow"))
    };
    let looping = "package test\nallow if {\n  input.k == 1\n  some i in numbers.range(1, 100000)\n  i < 0\n}";
    #[cfg(feature = "regex")]
    let regex = "package test\nallow if regex.match(input.p, \"test\")";
    let overflow = "package test\nallow if {\n  input.k == 1\n  y := input.a + input.a\n  y > 0\n}";
    // Nothing is flagged with an unknown under `context`, so those cases
    // only check that the error isn't lost; with one under `input`, every
    // read of `input` is flagged, so the error must not become Unsupported.
    let context_u = UnknownPath::new(UnknownRoot::Context, [PathSegment::Key("u".into())]);
    for unknown in [context_u, UnknownPath::input_keys(["u"])] {
        let result = run(looping, &unknown, Some(1000))?;
        assert!(
            matches!(
                result,
                Err(ExplainError::Vm(VmError::InstructionLimitExceeded { .. }))
            ),
            "{unknown:?}: {result:?}"
        );
        #[cfg(feature = "regex")]
        {
            let result = run(regex, &unknown, None)?;
            assert!(
                matches!(
                    result,
                    Err(ExplainError::Vm(VmError::RegexSizeLimitExceeded { .. }))
                ),
                "{unknown:?}: {result:?}"
            );
        }
        let result = run(overflow, &unknown, None)?;
        assert!(
            matches!(
                result,
                Err(ExplainError::Vm(VmError::NumericOverflow { .. }))
            ),
            "{unknown:?}: {result:?}"
        );
    }
    Ok(())
}

#[test]
fn unknowns_index_values_as_rego_does() -> anyhow::Result<()> {
    use alloc::collections::{BTreeMap, BTreeSet};
    let run = |input: Value, segments: [PathSegment; 2]| {
        let mut vm = vm(TWO_CONDITIONS)?;
        vm.set_input(input);
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = vec![UnknownPath::new(UnknownRoot::Input, segments)];
        vm.set_partial_eval_settings(settings);
        anyhow::Ok(vm.partial_eval("data.test.allow").map(|_| ()))
    };
    let field =
        |name: &str, value: Value| Value::from(BTreeMap::from([(Value::from(name), value)]));
    let xs0 = || [PathSegment::Key("xs".into()), PathSegment::Index(0)];
    let supplied = |path: &str| Err(ExplainError::UnknownValueSupplied { path: path.into() });

    // Rego reads `input.xs[0]` from a number key and `input.s.a` from a set.
    let numbered = Value::from(BTreeMap::from([(Value::from(0), Value::from(1))]));
    assert_eq!(
        run(field("xs", numbered), xs0())?,
        supplied(r#"input["xs"][0]"#)
    );
    let set = Value::from(BTreeSet::from([Value::from("a")]));
    let s_a = [PathSegment::Key("s".into()), PathSegment::Key("a".into())];
    assert_eq!(run(field("s", set), s_a)?, supplied(r#"input["s"]["a"]"#));
    Ok(())
}

#[test]
fn context_and_index_unknowns_are_validated() -> anyhow::Result<()> {
    let run = |unknowns: Vec<UnknownPath>, input: &str, context: Option<&str>| {
        let mut vm = vm(TWO_CONDITIONS)?;
        vm.set_input(Value::from_json_str(input)?);
        if let Some(context) = context {
            vm.set_context(Value::from_json_str(context)?);
        }
        let mut settings = PartialEvalSettings::default();
        settings.unknowns = unknowns;
        vm.set_partial_eval_settings(settings);
        anyhow::Ok(
            vm.partial_eval("data.test.allow")
                .map_err(|e| e.to_string()),
        )
    };
    let context_u = || UnknownPath::new(UnknownRoot::Context, [PathSegment::Key("u".into())]);
    let xs0 = || {
        UnknownPath::new(
            UnknownRoot::Input,
            [PathSegment::Key("xs".into()), PathSegment::Index(0)],
        )
    };
    let whole = |root| UnknownPath::new(root, []);
    let supplied = |path: &str| Err(format!("a value is supplied for unknown path `{path}`"));

    assert_eq!(
        run(vec![context_u()], "{}", Some(r#"{"u": 1}"#))?.map(|_| ()),
        supplied(r#"context["u"]"#)
    );
    run(vec![context_u()], "{}", Some(r#"{"v": 1}"#))?.map_err(anyhow::Error::msg)?;
    // Unlike input, context is undefined until it is set, so null is a value.
    assert_eq!(
        run(vec![whole(UnknownRoot::Context)], "{}", Some("null"))?.map(|_| ()),
        supplied("context")
    );
    run(vec![whole(UnknownRoot::Context)], "{}", None)?.map_err(anyhow::Error::msg)?;

    assert_eq!(
        run(vec![xs0()], r#"{"xs": [5]}"#, None)?.map(|_| ()),
        supplied(r#"input["xs"][0]"#)
    );
    run(vec![xs0()], r#"{"xs": []}"#, None)?.map_err(anyhow::Error::msg)?;
    // A string key is not the number index.
    run(vec![xs0()], r#"{"xs": {"0": 1}}"#, None)?.map_err(anyhow::Error::msg)?;

    // Paths under different roots don't overlap; a whole root overlaps its paths.
    let input_u = UnknownPath::input_keys(["u"]);
    run(vec![input_u.clone(), context_u()], "{}", None)?.map_err(anyhow::Error::msg)?;
    assert_eq!(
        run(vec![whole(UnknownRoot::Input), input_u], "null", None)?.map(|_| ()),
        Err(r#"invalid unknown path `input["u"]`: overlaps `input`"#.into())
    );
    // Keys are quoted as JSON strings.
    let odd = UnknownPath::input_keys(["a\"b", ""]);
    assert_eq!(
        run(vec![odd.clone(), odd], "{}", None)?.map(|_| ()),
        Err(r#"invalid unknown path `input["a\"b"][""]`: overlaps `input["a\"b"][""]`"#.into())
    );
    Ok(())
}
