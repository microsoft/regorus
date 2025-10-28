use std::collections::BTreeMap;

use anyhow::{anyhow, bail, Result};
use regorus::type_analysis::model::{
    ConstantValue, PathSegment, SourceOrigin, SourceRoot, TypeDiagnosticSeverity, TypeFact,
    TypeProvenance,
};
use regorus::type_analysis::result::{
    DefinitionSummary, DependencyKind, RuleBodyKind, RuleBodySummary, RuleKind,
    RuleSpecializationRecord,
};
use regorus::type_analysis::{StructuralType, TypeAnalysisResult, TypeDescriptor};
use regorus::unstable::{
    ArithOp, AssignOp, BinOp, BoolOp, Expr, Literal, LiteralStmt, Query, Rule, RuleHead,
};
use regorus::{get_path_string, Schema};

use crate::add_policy_from_file;

#[allow(unused_variables)]
pub fn rego_type_analysis(
    bundles: &[String],
    files: &[String],
    input_schema: Option<String>,
    data_schema: Option<String>,
    entrypoints: Vec<String>,
    v0: bool,
    verbose: bool,
) -> Result<()> {
    // Create engine.
    let mut engine = regorus::Engine::new();
    engine.set_rego_v0(v0);

    // Load files from given bundles.
    for dir in bundles.iter() {
        let entries =
            std::fs::read_dir(dir).or_else(|e| bail!("failed to read bundle {dir}.\n{e}"))?;
        for entry in entries {
            let entry = entry.or_else(|e| bail!("failed to unwrap entry. {e}"))?;
            let path = entry.path();

            match (path.is_file(), path.extension()) {
                (true, Some(ext)) if ext == "rego" => {}
                _ => continue,
            }

            let _package = add_policy_from_file(&mut engine, entry.path().display().to_string())?;
        }
    }

    // Load given policy files.
    for file in files.iter() {
        if file.ends_with(".rego") {
            let _package = add_policy_from_file(&mut engine, file.clone())?;
        } else {
            bail!("Type analysis only accepts .rego files. Got: {file}");
        }
    }

    // Enable type checking on the engine
    engine.enable_type_checking();

    // Set entrypoints if provided
    if !entrypoints.is_empty() {
        if let Some(checker) = engine.get_type_checker_mut() {
            checker.set_entrypoints(entrypoints);
        }
    }

    // Load schemas if provided and set them on the type checker
    if let Some(path) = input_schema {
        let schema_str = std::fs::read_to_string(&path)
            .map_err(|e| anyhow!("failed to read input schema {path}: {e}"))?;
        let schema = Schema::from_json_str(&schema_str)
            .map_err(|e| anyhow!("failed to parse input schema: {:?}", e))?;

        if let Some(checker) = engine.get_type_checker_mut() {
            checker.set_input_schema(schema);
        }
    }

    if let Some(path) = data_schema {
        let schema_str = std::fs::read_to_string(&path)
            .map_err(|e| anyhow!("failed to read data schema {path}: {e}"))?;
        let schema = Schema::from_json_str(&schema_str)
            .map_err(|e| anyhow!("failed to parse data schema: {:?}", e))?;

        if let Some(checker) = engine.get_type_checker_mut() {
            checker.set_data_schema(schema);
        }
    }

    // Run type checking (this will automatically run loop hoisting)
    let _diagnostics = engine.type_check()?;

    // Get the type analysis result and clone it to avoid borrow conflicts
    let requested_entrypoints = {
        let checker = engine
            .get_type_checker()
            .ok_or_else(|| anyhow!("Type checker not available"))?;
        checker
            .get_entrypoints()
            .map(|eps| eps.to_vec())
            .unwrap_or_default()
    };

    let (result, modules) = {
        let checker = engine
            .get_type_checker()
            .ok_or_else(|| anyhow!("Type checker not available"))?;
        let result = checker
            .get_result()
            .ok_or_else(|| anyhow!("Type analysis results not available"))?
            .clone();
        let modules_ref = engine.get_modules();
        (result, modules_ref.clone())
    };

    // Print entrypoint filtering statistics if applicable
    if !requested_entrypoints.is_empty() {
        println!("\n=== Entrypoint Filtering ===\n");
        println!("📍 Requested entrypoints: {}", requested_entrypoints.len());
        for ep in &requested_entrypoints {
            println!("   • {}", ep);
        }

        // Get reachable rules from lookup
        let reachable_rules: Vec<String> = result
            .expressions
            .facts
            .reachable_rules()
            .cloned()
            .collect();
        if !reachable_rules.is_empty() {
            println!("\n🎯 Reachable rules: {}", reachable_rules.len());

            // Count total rules in all modules
            let total_rules: usize = modules.iter().map(|m| m.policy.len()).sum();
            let analyzed_percent = if total_rules > 0 {
                (reachable_rules.len() * 100) / total_rules
            } else {
                0
            };

            println!("📊 Total rules in policy: {}", total_rules);
            println!("⚡ Analysis coverage: {}%", analyzed_percent);

            if verbose {
                println!("\nReachable rules:");
                for rule_path in &reachable_rules {
                    println!("   • {}", rule_path);
                }
            }
        }
        println!("\n=== Type Analysis Results ===\n");
    }
    println!("\n=== Type Analysis Results ===\n");
    // Get reachable rules set for filtering (if entrypoint filtering is active)
    let reachable_rules: Option<std::collections::BTreeSet<String>> =
        if !requested_entrypoints.is_empty() {
            Some(
                result
                    .expressions
                    .facts
                    .reachable_rules()
                    .cloned()
                    .collect(),
            )
        } else {
            None
        };
    let reachable_rules = reachable_rules.as_ref();

    if !result.diagnostics.is_empty() {
        println!("⚠️  Diagnostics:");
        for diag in &result.diagnostics {
            let severity = match diag.severity {
                TypeDiagnosticSeverity::Error => "error",
                TypeDiagnosticSeverity::Warning => "warning",
            };
            println!(
                "  [{}] Line {}, Col {}: {}",
                severity, diag.line, diag.col, diag.message
            );
        }
        println!();
    }

    // Print rule information
    for (module_idx, module) in modules.iter().enumerate() {
        if module.policy.is_empty() {
            continue;
        }

        let module_path = get_path_string(module.package.refr.as_ref(), Some("data"))
            .unwrap_or_else(|_| "data".to_owned());

        println!("📦 Module: {}", module_path);
        println!("{}", "─".repeat(80));

        // Rule analysis info not yet available in TypeAnalysisResult
        // TODO: Populate rules field in TypeAnalysisResult.from_analysis_state
        for (rule_idx, rule) in module.policy.iter().enumerate() {
            // Check if this is a default rule
            let is_default = matches!(rule.as_ref(), Rule::Default { .. });

            // Check if this rule has bodies (depends on runtime evaluation)
            let has_bodies = match rule.as_ref() {
                Rule::Spec { bodies, .. } => !bodies.is_empty(),
                Rule::Default { .. } => false,
            };

            // Get rule head expression
            let refr = match rule.as_ref() {
                Rule::Spec { head, .. } => match head {
                    RuleHead::Compr { refr, .. }
                    | RuleHead::Set { refr, .. }
                    | RuleHead::Func { refr, .. } => Some(refr),
                },
                Rule::Default { refr, .. } => Some(refr),
            };

            if let Some(refr) = refr {
                let rule_path = get_path_string(refr.as_ref(), Some(&module_path))
                    .unwrap_or_else(|_| format!("rule_{}", rule_idx));

                // Skip if entrypoint filtering is active and this rule is not reachable
                if let Some(reachable) = reachable_rules {
                    if !reachable.contains(&rule_path) {
                        continue;
                    }
                }

                let rule_summary_ref = result
                    .rules
                    .modules
                    .get(module_idx)
                    .and_then(|module_summary| module_summary.rules.get(rule_idx));

                // Get rule kind icon
                let icon = if is_default {
                    "🔹"
                } else if matches!(
                    rule.as_ref(),
                    Rule::Spec {
                        head: RuleHead::Func { .. },
                        ..
                    }
                ) {
                    "ƒ"
                } else {
                    "•"
                };

                // Print rule header without location (only definitions have locations)
                print!("\n  {} {}", icon, rule_path);
                if is_default {
                    print!(" (default)");
                }
                println!();

                // In verbose mode, show aggregated info
                if verbose {
                    if let Some(rule_summary) = rule_summary_ref {
                        if let Some(agg) = &rule_summary.aggregated_head_fact {
                            println!("     Aggregated: {}", format_fact_summary(agg));
                        }
                    }
                }

                // Show definitions
                if let Some(rule_summary) = rule_summary_ref {
                    let is_function_rule = rule_summary.kind == RuleKind::Function;

                    for (def_idx, definition) in rule_summary.definitions.iter().enumerate() {
                        let def_location = definition
                            .span
                            .as_ref()
                            .map(|span| format!(" → {}", span.format()))
                            .unwrap_or_default();

                        // Show definition header with location (only for multiple definitions)
                        if rule_summary.definitions.len() > 1 {
                            println!("     Definition #{}{}", def_idx + 1, def_location);
                        }

                        // Show type and values
                        let bodies_available = has_bodies && !definition.bodies.is_empty();
                        let show_bodies = bodies_available && !is_function_rule;

                        if let Some(fact) = &definition.aggregated_head_fact {
                            print!("     Type: ");
                            print_type_descriptor(&fact.descriptor);
                            println!();

                            if show_bodies {
                                print_definition_bodies(
                                    module_idx,
                                    rule.as_ref(),
                                    definition,
                                    &result,
                                    verbose,
                                );
                            } else if bodies_available && is_function_rule {
                                if rule_summary.specializations.is_empty() {
                                    println!("     Bodies: <no specialization metadata available>");
                                }
                            } else if let ConstantValue::Known(value) = &fact.constant {
                                println!("     Constant: {}", serde_json::to_string(&value)?);
                            }
                        } else if show_bodies {
                            println!("     Type: <unknown>");
                            print_definition_bodies(
                                module_idx,
                                rule.as_ref(),
                                definition,
                                &result,
                                verbose,
                            );
                        } else if bodies_available && is_function_rule {
                            println!("     Type: <unknown>");
                            if rule_summary.specializations.is_empty() {
                                println!("     Bodies: <no specialization metadata available>");
                            }
                        } else {
                            println!("     Type: <unknown>");
                        }

                        // In verbose mode, show additional details
                        if verbose {
                            if let Some(fact) = &definition.aggregated_head_fact {
                                if !fact.origins.is_empty() {
                                    print!("     Origins: ");
                                    for (i, origin) in fact.origins.iter().enumerate() {
                                        if i > 0 {
                                            print!(", ");
                                        }
                                        print!("{:?}:{:?}", origin.root, origin.path);
                                    }
                                    println!();
                                }
                            }
                        }
                    }

                    // Show specializations for function rules
                    if !rule_summary.specializations.is_empty() {
                        if verbose
                            && !rule_summary.aggregated_parameter_facts.is_empty()
                            && rule_summary
                                .aggregated_parameter_facts
                                .iter()
                                .any(|fact| fact.is_some())
                        {
                            println!("     Parameter types (union):");
                            for (arg_idx, fact) in
                                rule_summary.aggregated_parameter_facts.iter().enumerate()
                            {
                                match fact {
                                    Some(fact) => println!(
                                        "       arg {}: {}",
                                        arg_idx + 1,
                                        format_fact_summary(fact)
                                    ),
                                    None => println!("       arg {}: <unknown>", arg_idx + 1),
                                }
                            }
                        }

                        println!(
                            "     Specializations: {}",
                            rule_summary.specializations.len()
                        );
                        for spec in &rule_summary.specializations {
                            let signature_display =
                                format_specialization_signature(&rule_path, spec);
                            let head_display = spec
                                .head_fact
                                .as_ref()
                                .map(|fact| format_fact_summary(fact))
                                .unwrap_or_else(|| "Unknown".to_owned());
                            println!("       - {} → {}", signature_display, head_display);

                            if let Some(constant) = &spec.constant_value {
                                println!("         Constant value: {}", constant);
                            }

                            let body_entries = collect_specialization_bodies(
                                rule.as_ref(),
                                &rule_summary.definitions,
                                spec,
                            );
                            if !body_entries.is_empty() {
                                println!("         Bodies:");
                                for entry in &body_entries {
                                    let location = entry
                                        .body
                                        .span
                                        .as_ref()
                                        .map(|span| format!(" ({})", span.format()))
                                        .unwrap_or_default();

                                    let fact = entry.specialized_fact.or(entry.fallback_fact);
                                    println!(
                                        "           - {}{}: {}",
                                        entry.label,
                                        location,
                                        render_body_value(fact, entry.body.is_constant)
                                    );
                                }
                            }

                            if !verbose {
                                continue;
                            }

                            let overlay = SpecializationFactOverlay::new(&result, &spec.expr_facts);

                            for entry in &body_entries {
                                if let Some(verbose_info) = collect_body_verbose_info(
                                    spec.signature.module_idx,
                                    entry.definition_rule,
                                    entry.body_idx,
                                    &overlay,
                                ) {
                                    print_body_verbose_details(
                                        9,
                                        entry.label.as_str(),
                                        &verbose_info,
                                    );
                                }
                            }

                            if !spec.expr_facts.is_empty() {
                                println!("         Expression facts:");
                                for (fact_module_idx, exprs) in &spec.expr_facts {
                                    let module_label = modules
                                        .get(*fact_module_idx as usize)
                                        .and_then(|m| {
                                            get_path_string(m.package.refr.as_ref(), Some("data"))
                                                .ok()
                                        })
                                        .unwrap_or_else(|| format!("module {}", fact_module_idx));
                                    println!("           [{}]", module_label);
                                    for (expr_idx, expr_fact) in exprs {
                                        println!(
                                            "             expr #{}: {}",
                                            expr_idx,
                                            format_fact_summary(expr_fact)
                                        );
                                    }
                                }
                            }
                        }
                    }

                    // Show dependencies in verbose mode
                    if verbose {
                        if !rule_summary.input_dependencies.is_empty() {
                            println!("     Input dependencies:");
                            for origin in &rule_summary.input_dependencies {
                                println!("       - {}", format_origin(origin));
                            }
                        }

                        if !rule_summary.rule_dependencies.is_empty() {
                            println!("     Rule dependencies:");
                            for dep in &rule_summary.rule_dependencies {
                                let kind_label = describe_dependency_kind(&dep.kind);
                                println!("       - {} ({})", dep.target, kind_label);

                                if let Some(target_summary) = result.rules.by_path.get(&dep.target)
                                {
                                    if !target_summary.specializations.is_empty() {
                                        println!(
                                            "         Specializations: {}",
                                            target_summary.specializations.len()
                                        );
                                        for spec in &target_summary.specializations {
                                            let sig_display =
                                                format_specialization_signature(&dep.target, spec);
                                            let head_display = spec
                                                .head_fact
                                                .as_ref()
                                                .map(|fact| format_fact_summary(fact))
                                                .unwrap_or_else(|| "Unknown".to_owned());
                                            println!(
                                                "           • {} → {}",
                                                sig_display, head_display
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        println!();
    }

    Ok(())
}

fn format_origin(origin: &SourceOrigin) -> String {
    let mut path = match origin.root {
        SourceRoot::Input => String::from("input"),
        SourceRoot::Data => String::from("data"),
    };

    for segment in &origin.path {
        match segment {
            PathSegment::Field(name) => {
                path.push('.');
                path.push_str(name);
            }
            PathSegment::Index(idx) => {
                path.push('[');
                path.push_str(&idx.to_string());
                path.push(']');
            }
            PathSegment::Any => path.push_str("[*]"),
        }
    }

    if origin.derived {
        path.push_str(" (derived)");
    }

    path
}

fn describe_dependency_kind(kind: &DependencyKind) -> &'static str {
    match kind {
        DependencyKind::StaticCall => "static",
        DependencyKind::DynamicCall => "dynamic",
        DependencyKind::DefaultLink => "default link",
    }
}

fn format_specialization_signature(rule_path: &str, spec: &RuleSpecializationRecord) -> String {
    let args: Vec<String> = spec
        .parameter_facts
        .iter()
        .map(|fact| format_fact_summary(fact))
        .collect();

    let joined = if args.is_empty() {
        String::new()
    } else {
        args.join(", ")
    };

    format!("{}({})", rule_path, joined)
}

fn describe_type_descriptor(descriptor: &TypeDescriptor) -> String {
    match descriptor {
        TypeDescriptor::Schema(schema) => describe_schema(schema),
        TypeDescriptor::Structural(st) => describe_structural_type(st),
    }
}

fn describe_schema(schema: &Schema) -> String {
    describe_schema_type(schema.as_type())
}

fn describe_schema_type(ty: &regorus::schema::Type) -> String {
    use regorus::schema::Type as SchemaType;

    match ty {
        SchemaType::Any { .. } => "Any".to_owned(),
        SchemaType::Integer { .. } => "Integer".to_owned(),
        SchemaType::Number { .. } => "Number".to_owned(),
        SchemaType::Boolean { .. } => "Boolean".to_owned(),
        SchemaType::Null { .. } => "Null".to_owned(),
        SchemaType::String { .. } => "String".to_owned(),
        SchemaType::Array { items, .. } => {
            format!("Array[{}]", describe_schema_type(items.as_type()))
        }
        SchemaType::Set { items, .. } => {
            format!("Set[{}]", describe_schema_type(items.as_type()))
        }
        SchemaType::Object {
            properties,
            required,
            additional_properties,
            ..
        } => {
            if properties.is_empty() && additional_properties.is_none() {
                return "Object".to_owned();
            }

            let mut parts: Vec<String> = Vec::new();
            for (name, schema) in properties.iter() {
                let is_required = required
                    .as_ref()
                    .map(|reqs| {
                        reqs.iter()
                            .any(|req_name| req_name.as_ref() == name.as_ref())
                    })
                    .unwrap_or(false);

                let optional_marker = if is_required { "" } else { "?" };
                parts.push(format!(
                    "{}{}: {}",
                    name,
                    optional_marker,
                    describe_schema_type(schema.as_type())
                ));
            }

            if let Some(additional) = additional_properties {
                if !matches!(additional.as_type(), SchemaType::Any { .. }) {
                    parts.push(format!(
                        "additional: {}",
                        describe_schema_type(additional.as_type())
                    ));
                }
            }

            format!("Object{{{}}}", parts.join(", "))
        }
        SchemaType::Const { value, .. } => value
            .to_json_str()
            .map(|s| format!("Const({s})"))
            .unwrap_or_else(|_| "Const".to_owned()),
        SchemaType::Enum { values, .. } => {
            let rendered: Vec<String> = values
                .iter()
                .map(|v| v.to_json_str().unwrap_or_else(|_| "?".to_owned()))
                .collect();
            format!("Enum[{}]", rendered.join(" | "))
        }
        SchemaType::AnyOf(variants) => {
            let rendered: Vec<String> = variants
                .iter()
                .map(|variant| describe_schema_type(variant.as_type()))
                .collect();
            format!("AnyOf[{}]", rendered.join(" | "))
        }
    }
}

fn describe_structural_type(st: &StructuralType) -> String {
    describe_structural_type_impl(st)
}

fn describe_structural_type_impl(st: &StructuralType) -> String {
    match st {
        StructuralType::Any => "Any".to_owned(),
        StructuralType::Boolean => "Boolean".to_owned(),
        StructuralType::Number => "Number".to_owned(),
        StructuralType::Integer => "Integer".to_owned(),
        StructuralType::String => "String".to_owned(),
        StructuralType::Null => "Null".to_owned(),
        StructuralType::Array(elem) => {
            format!("Array[{}]", describe_structural_type_impl(elem))
        }
        StructuralType::Set(elem) => {
            format!("Set[{}]", describe_structural_type_impl(elem))
        }
        StructuralType::Object(shape) => {
            if shape.fields.is_empty() {
                "Object".to_owned()
            } else {
                let mut parts: Vec<String> = Vec::new();
                for (name, ty) in &shape.fields {
                    parts.push(format!("{}: {}", name, describe_structural_type_impl(ty)));
                }
                format!("Object{{{}}}", parts.join(", "))
            }
        }
        StructuralType::Union(types) => {
            let rendered: Vec<String> = types
                .iter()
                .map(|ty| describe_structural_type_impl(ty))
                .collect();
            format!("Union[{}]", rendered.join(", "))
        }
        StructuralType::Enum(values) => {
            let rendered: Vec<String> = values
                .iter()
                .map(|value| {
                    serde_json::to_string(value).unwrap_or_else(|_| format!("{:?}", value))
                })
                .collect();
            format!("Enum[{}]", rendered.join(", "))
        }
        StructuralType::Unknown => "Unknown".to_owned(),
    }
}

fn print_type_descriptor(descriptor: &TypeDescriptor) {
    let rendered = describe_type_descriptor(descriptor);
    print!("{}", rendered);
}

#[allow(dead_code)]
fn print_structural_type(st: &StructuralType) {
    print_structural_type_impl(st);
}

fn print_structural_type_impl(st: &StructuralType) {
    match st {
        StructuralType::Any => print!("Any"),
        StructuralType::Boolean => print!("Boolean"),
        StructuralType::Number => print!("Number"),
        StructuralType::Integer => print!("Integer"),
        StructuralType::String => print!("String"),
        StructuralType::Null => print!("Null"),
        StructuralType::Array(elem) => {
            print!("Array[");
            print_structural_type_impl(elem);
            print!("]");
        }
        StructuralType::Set(elem) => {
            print!("Set[");
            print_structural_type_impl(elem);
            print!("]");
        }
        StructuralType::Object(shape) => {
            if shape.fields.is_empty() {
                print!("Object");
            } else {
                print!("Object{{");
                for (i, (name, ty)) in shape.fields.iter().enumerate() {
                    if i > 0 {
                        print!(", ");
                    }
                    print!("{}: ", name);
                    print_structural_type_impl(ty);
                }
                print!("}}");
            }
        }
        StructuralType::Union(types) => {
            print!("Union[");
            for (i, t) in types.iter().enumerate() {
                if i > 0 {
                    print!(", ");
                }
                print_structural_type_impl(t);
            }
            print!("]");
        }
        StructuralType::Enum(values) => {
            print!("Enum[");
            for (i, v) in values.iter().enumerate() {
                if i > 0 {
                    print!(", ");
                }
                if let Ok(s) = v.as_string() {
                    print!("{:?}", s.as_ref());
                } else {
                    print!(
                        "{}",
                        serde_json::to_string(v).unwrap_or_else(|_| "?".to_string())
                    );
                }
            }
            print!("]");
        }
        StructuralType::Unknown => print!("Unknown"),
    }
}

trait ExprFactSource {
    fn get_expr_fact(&self, module_idx: u32, expr_idx: u32) -> Option<TypeFact>;
}

impl ExprFactSource for TypeAnalysisResult {
    fn get_expr_fact(&self, module_idx: u32, expr_idx: u32) -> Option<TypeFact> {
        self.expressions
            .facts
            .get_expr(module_idx, expr_idx)
            .cloned()
    }
}

struct SpecializationFactOverlay<'a> {
    base: &'a TypeAnalysisResult,
    overrides: &'a BTreeMap<u32, BTreeMap<u32, TypeFact>>,
}

impl<'a> SpecializationFactOverlay<'a> {
    fn new(
        base: &'a TypeAnalysisResult,
        overrides: &'a BTreeMap<u32, BTreeMap<u32, TypeFact>>,
    ) -> Self {
        Self { base, overrides }
    }
}

impl<'a> ExprFactSource for SpecializationFactOverlay<'a> {
    fn get_expr_fact(&self, module_idx: u32, expr_idx: u32) -> Option<TypeFact> {
        if let Some(exprs) = self.overrides.get(&module_idx) {
            if let Some(fact) = exprs.get(&expr_idx) {
                return Some(fact.clone());
            }
        }

        self.base.get_expr_fact(module_idx, expr_idx)
    }
}

struct RuleVerboseInfo {
    locals: Vec<LocalDisplay>,
    statements: Vec<StatementDisplay>,
}

#[derive(Clone)]
struct LocalDisplay {
    name: String,
    fact: Option<TypeFact>,
}

struct StatementDisplay {
    summary: String,
    fact_lines: Vec<String>,
}

struct LocalCollector {
    order: Vec<String>,
    entries: BTreeMap<String, LocalDisplay>,
}

impl LocalCollector {
    fn new() -> Self {
        Self {
            order: Vec::new(),
            entries: BTreeMap::new(),
        }
    }

    fn note(&mut self, name: String, fact: Option<TypeFact>) {
        let entry = self.entries.entry(name.clone()).or_insert_with(|| {
            self.order.push(name.clone());
            LocalDisplay { name, fact: None }
        });

        if let Some(fact) = fact {
            entry.fact = Some(fact);
        }
    }

    fn into_vec(self) -> Vec<LocalDisplay> {
        let mut displays = Vec::new();
        let LocalCollector { order, entries } = self;
        for name in order {
            if let Some(entry) = entries.get(&name) {
                displays.push(entry.clone());
            }
        }
        displays
    }
}

fn process_query_statements(
    module_idx: u32,
    query: &Query,
    facts: &impl ExprFactSource,
    indent: usize,
    locals: &mut LocalCollector,
) -> Vec<StatementDisplay> {
    let mut out = Vec::new();
    for stmt in &query.stmts {
        out.extend(process_literal(module_idx, stmt, facts, indent, locals));
    }
    out
}

fn process_literal(
    module_idx: u32,
    stmt: &LiteralStmt,
    facts: &impl ExprFactSource,
    indent: usize,
    locals: &mut LocalCollector,
) -> Vec<StatementDisplay> {
    let mut displays = Vec::new();
    let indent_str = " ".repeat(indent);
    let summary = format!("{}{}", indent_str, summarize_literal(&stmt.literal));
    let mut fact_lines = Vec::new();

    match &stmt.literal {
        Literal::SomeVars { vars, .. } => {
            for span in vars {
                locals.note(span.text().to_owned(), None);
            }
        }
        Literal::SomeIn {
            key,
            value,
            collection,
            ..
        } => {
            if let Some(key_expr) = key {
                if let Some(name) = extract_var_name(key_expr.as_ref()) {
                    let fact = get_fact(facts, module_idx, key_expr.as_ref());
                    if let Some(fact) = fact.clone() {
                        fact_lines.push(format_fact_entry("key", &fact));
                    }
                    locals.note(name, fact);
                } else {
                    collect_expr_fact_lines(
                        module_idx,
                        key_expr.as_ref(),
                        facts,
                        &mut fact_lines,
                        locals,
                    );
                }
            }

            if let Some(name) = extract_var_name(value.as_ref()) {
                let fact = get_fact(facts, module_idx, value.as_ref());
                if let Some(fact) = fact.clone() {
                    fact_lines.push(format_fact_entry("value", &fact));
                }
                locals.note(name, fact);
            } else {
                collect_expr_fact_lines(module_idx, value.as_ref(), facts, &mut fact_lines, locals);
            }

            if let Some(fact) = get_fact(facts, module_idx, collection.as_ref()) {
                fact_lines.push(format_fact_entry("collection", &fact));
            }
        }
        Literal::Expr { expr, .. } => {
            collect_expr_fact_lines(module_idx, expr.as_ref(), facts, &mut fact_lines, locals);
        }
        Literal::NotExpr { expr, .. } => {
            collect_expr_fact_lines(module_idx, expr.as_ref(), facts, &mut fact_lines, locals);
        }
        Literal::Every {
            key,
            value,
            domain,
            query,
            ..
        } => {
            if let Some(key_span) = key {
                locals.note(key_span.text().to_owned(), None);
            }
            locals.note(value.text().to_owned(), None);

            if let Some(fact) = get_fact(facts, module_idx, domain.as_ref()) {
                fact_lines.push(format_fact_entry("domain", &fact));
            }

            let mut nested =
                process_query_statements(module_idx, query.as_ref(), facts, indent + 2, locals);
            displays.append(&mut nested);
        }
    }

    displays.push(StatementDisplay {
        summary,
        fact_lines,
    });
    displays
}

fn summarize_literal(literal: &Literal) -> String {
    match literal {
        Literal::SomeVars { vars, .. } => {
            let names: Vec<String> = vars.iter().map(|span| span.text().to_owned()).collect();
            format!("some {}", names.join(", "))
        }
        Literal::SomeIn {
            key,
            value,
            collection,
            ..
        } => {
            let value_part = format_expr(value.as_ref());
            let key_part = key
                .as_ref()
                .map(|expr| format_expr(expr.as_ref()))
                .map(|k| format!("{}, ", k))
                .unwrap_or_default();
            let collection_part = format_expr(collection.as_ref());
            format!("some {}{} in {}", key_part, value_part, collection_part)
        }
        Literal::Expr { expr, .. } => format_expr(expr.as_ref()),
        Literal::NotExpr { expr, .. } => format!("not {}", format_expr(expr.as_ref())),
        Literal::Every {
            key, value, domain, ..
        } => {
            let key_part = key
                .as_ref()
                .map(|span| format!("{}, ", span.text()))
                .unwrap_or_default();
            let value_part = value.text();
            let domain_part = format_expr(domain.as_ref());
            format!("every {}{} in {}", key_part, value_part, domain_part)
        }
    }
}

fn format_expr(expr: &Expr) -> String {
    match expr {
        Expr::Var { value, .. } => value
            .as_string()
            .map(|s| s.as_ref().to_owned())
            .unwrap_or_else(|_| "<var>".to_owned()),
        Expr::String { value, .. }
        | Expr::RawString { value, .. }
        | Expr::Number { value, .. }
        | Expr::Bool { value, .. }
        | Expr::Null { value, .. } => {
            serde_json::to_string(value).unwrap_or_else(|_| "<literal>".to_owned())
        }
        Expr::Array { items, .. } => {
            let parts: Vec<std::string::String> = items
                .iter()
                .map(|item| format_expr(item.as_ref()))
                .collect();
            format!("[{}]", parts.join(", "))
        }
        Expr::Set { items, .. } => {
            let parts: Vec<std::string::String> = items
                .iter()
                .map(|item| format_expr(item.as_ref()))
                .collect();
            format!("{{{}}}", parts.join(", "))
        }
        Expr::Object { fields, .. } => {
            let mut parts = Vec::new();
            for (name_span, key_expr, value_expr) in fields {
                let key_text = name_span.text();
                let key = if key_text.is_empty() {
                    format_expr(key_expr.as_ref())
                } else {
                    key_text.to_owned()
                };
                parts.push(format!("{}: {}", key, format_expr(value_expr.as_ref())));
            }
            format!("{{{}}}", parts.join(", "))
        }
        Expr::ArrayCompr { term, .. } => format!("[{} | ...]", format_expr(term.as_ref())),
        Expr::SetCompr { term, .. } => format!("{{{} | ...}}", format_expr(term.as_ref())),
        Expr::ObjectCompr { key, value, .. } => format!(
            "{{{}: {} | ...}}",
            format_expr(key.as_ref()),
            format_expr(value.as_ref())
        ),
        Expr::Call { fcn, params, .. } => {
            let args: Vec<std::string::String> =
                params.iter().map(|p| format_expr(p.as_ref())).collect();
            format!("{}({})", format_expr(fcn.as_ref()), args.join(", "))
        }
        Expr::UnaryExpr { expr, .. } => {
            format!("unary({})", format_expr(expr.as_ref()))
        }
        Expr::RefDot { refr, field, .. } => {
            let base = format_expr(refr.as_ref());
            let field_name = field
                .as_ref()
                .map(|(span, value)| {
                    value
                        .as_string()
                        .map(|s| s.as_ref().to_owned())
                        .unwrap_or_else(|_| {
                            let text = span.text();
                            if text.is_empty() {
                                "<field>".to_owned()
                            } else {
                                text.to_owned()
                            }
                        })
                })
                .unwrap_or_else(|| "<field>".to_owned());
            format!("{}.{}", base, field_name)
        }
        Expr::RefBrack { refr, index, .. } => {
            format!(
                "{}[{}]",
                format_expr(refr.as_ref()),
                format_expr(index.as_ref())
            )
        }
        Expr::BinExpr { op, lhs, rhs, .. } => format!(
            "{} {} {}",
            format_expr(lhs.as_ref()),
            format_bin_op(op),
            format_expr(rhs.as_ref())
        ),
        Expr::BoolExpr { op, lhs, rhs, .. } => format!(
            "{} {} {}",
            format_expr(lhs.as_ref()),
            format_bool_op(op),
            format_expr(rhs.as_ref())
        ),
        Expr::ArithExpr { op, lhs, rhs, .. } => format!(
            "{} {} {}",
            format_expr(lhs.as_ref()),
            format_arith_op(op),
            format_expr(rhs.as_ref())
        ),
        Expr::AssignExpr { lhs, op, rhs, .. } => format!(
            "{} {} {}",
            format_expr(lhs.as_ref()),
            format_assign_op(op),
            format_expr(rhs.as_ref())
        ),
        Expr::Membership {
            key,
            value,
            collection,
            ..
        } => {
            let collection_text = format_expr(collection.as_ref());
            let value_text = format_expr(value.as_ref());
            if let Some(key_expr) = key {
                format!(
                    "{}, {} in {}",
                    format_expr(key_expr.as_ref()),
                    value_text,
                    collection_text
                )
            } else {
                format!("{} in {}", value_text, collection_text)
            }
        }
        #[cfg(feature = "rego-extensions")]
        Expr::OrExpr { lhs, rhs, .. } => format!(
            "{} or {}",
            format_expr(lhs.as_ref()),
            format_expr(rhs.as_ref())
        ),
    }
}

fn format_bool_op(op: &BoolOp) -> &'static str {
    match op {
        BoolOp::Lt => "<",
        BoolOp::Le => "<=",
        BoolOp::Eq => "==",
        BoolOp::Ge => ">=",
        BoolOp::Gt => ">",
        BoolOp::Ne => "!=",
    }
}

fn format_arith_op(op: &ArithOp) -> &'static str {
    match op {
        ArithOp::Add => "+",
        ArithOp::Sub => "-",
        ArithOp::Mul => "*",
        ArithOp::Div => "/",
        ArithOp::Mod => "%",
    }
}

fn format_bin_op(op: &BinOp) -> &'static str {
    match op {
        BinOp::Intersection => "∩",
        BinOp::Union => "∪",
    }
}

fn format_assign_op(op: &AssignOp) -> &'static str {
    match op {
        AssignOp::Eq => ":=",
        AssignOp::ColEq => ":=",
    }
}

fn collect_expr_fact_lines(
    module_idx: u32,
    expr: &Expr,
    facts: &impl ExprFactSource,
    fact_lines: &mut Vec<String>,
    locals: &mut LocalCollector,
) {
    fn record_fact_line(
        label: &str,
        module_idx: u32,
        expr: &Expr,
        facts: &impl ExprFactSource,
        fact_lines: &mut Vec<String>,
        locals: &mut LocalCollector,
    ) -> Option<TypeFact> {
        if let Some(fact) = get_fact(facts, module_idx, expr) {
            if let Some(name) = extract_var_name(expr) {
                locals.note(name, Some(fact.clone()));
            }
            fact_lines.push(format_fact_entry(label, &fact));
            Some(fact)
        } else {
            if let Some(name) = extract_var_name(expr) {
                locals.note(name, None);
            }
            None
        }
    }

    match expr {
        Expr::Var { .. } => {
            let _ = record_fact_line("var", module_idx, expr, facts, fact_lines, locals);
        }
        Expr::AssignExpr { lhs, rhs, .. } => {
            let _ = record_fact_line("rhs", module_idx, rhs.as_ref(), facts, fact_lines, locals);
            let _ = record_fact_line("lhs", module_idx, lhs.as_ref(), facts, fact_lines, locals);
            let _ = record_fact_line("expr", module_idx, expr, facts, fact_lines, locals);
        }
        Expr::BoolExpr { lhs, rhs, .. }
        | Expr::BinExpr { lhs, rhs, .. }
        | Expr::ArithExpr { lhs, rhs, .. } => {
            let _ = record_fact_line("lhs", module_idx, lhs.as_ref(), facts, fact_lines, locals);
            let _ = record_fact_line("rhs", module_idx, rhs.as_ref(), facts, fact_lines, locals);
            let _ = record_fact_line("expr", module_idx, expr, facts, fact_lines, locals);
        }
        Expr::Call { params, .. } => {
            let _ = record_fact_line("call", module_idx, expr, facts, fact_lines, locals);
            for (idx, param) in params.iter().enumerate() {
                let _ = record_fact_line(
                    &format!("arg{}", idx),
                    module_idx,
                    param.as_ref(),
                    facts,
                    fact_lines,
                    locals,
                );
            }
        }
        Expr::RefDot { refr, .. } => {
            let _ = record_fact_line("expr", module_idx, expr, facts, fact_lines, locals);
            let _ = record_fact_line("base", module_idx, refr.as_ref(), facts, fact_lines, locals);
        }
        Expr::RefBrack { refr, index, .. } => {
            let _ = record_fact_line("expr", module_idx, expr, facts, fact_lines, locals);
            let base_fact =
                record_fact_line("base", module_idx, refr.as_ref(), facts, fact_lines, locals);
            let index_fact = record_fact_line(
                "index",
                module_idx,
                index.as_ref(),
                facts,
                fact_lines,
                locals,
            );
            if index_fact.is_none() {
                if let Some(name) = extract_var_name(index.as_ref()) {
                    if let Some(fallback) = derive_index_fact(base_fact.as_ref(), index.as_ref()) {
                        locals.note(name.clone(), Some(fallback.clone()));
                        fact_lines.push(format_fact_entry("index", &fallback));
                    } else {
                        locals.note(name, None);
                    }
                }
            }
        }
        _ => {
            let _ = record_fact_line("expr", module_idx, expr, facts, fact_lines, locals);
        }
    }
}

fn get_fact(facts: &impl ExprFactSource, module_idx: u32, expr: &Expr) -> Option<TypeFact> {
    facts.get_expr_fact(module_idx, expr.eidx())
}

fn derive_index_fact(base_fact: Option<&TypeFact>, index_expr: &Expr) -> Option<TypeFact> {
    if !matches!(index_expr, Expr::Var { .. }) {
        return None;
    }

    let base_fact = base_fact?;
    let structural_type = match &base_fact.descriptor {
        TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
        TypeDescriptor::Structural(st) => st.clone(),
    };

    let mut inferred = match structural_type {
        StructuralType::Array(_) | StructuralType::Set(_) => StructuralType::Integer,
        StructuralType::Object(_) => StructuralType::String,
        _ => StructuralType::Any,
    };

    if matches!(inferred, StructuralType::Any) {
        let has_field_segment = base_fact.origins.iter().any(|origin| {
            origin
                .path
                .iter()
                .any(|segment| matches!(segment, PathSegment::Field(_)))
        });
        inferred = if has_field_segment {
            StructuralType::String
        } else {
            StructuralType::Integer
        };
    }

    let mut fact = TypeFact {
        descriptor: TypeDescriptor::Structural(inferred),
        constant: ConstantValue::Unknown,
        provenance: TypeProvenance::Propagated,
        origins: mark_origins_derived(&base_fact.origins),
        specialization_hits: Vec::new(),
    };

    if fact.origins.is_empty() {
        fact.origins = base_fact.origins.clone();
    }

    Some(fact)
}

fn mark_origins_derived(origins: &[SourceOrigin]) -> Vec<SourceOrigin> {
    origins
        .iter()
        .map(|origin| {
            let mut updated = origin.clone();
            updated.derived = true;
            updated
        })
        .collect()
}

fn extract_var_name(expr: &Expr) -> Option<String> {
    if let Expr::Var { value, .. } = expr {
        value.as_string().map(|s| s.as_ref().to_owned()).ok()
    } else {
        None
    }
}

fn format_local_fact_suffix(fact: &Option<TypeFact>) -> String {
    match fact {
        Some(fact) => format!(" :: {}", format_fact_summary(fact)),
        None => " :: <unknown>".to_owned(),
    }
}

fn format_fact_entry(label: &str, fact: &TypeFact) -> String {
    format!("{}: {}", label, format_fact_summary(fact))
}

fn format_fact_summary(fact: &TypeFact) -> String {
    let mut parts = Vec::new();
    parts.push(format!(
        "type={}",
        describe_type_descriptor(&fact.descriptor)
    ));

    if let ConstantValue::Known(value) = &fact.constant {
        if let Ok(rendered) = serde_json::to_string(value) {
            parts.push(format!("const={}", rendered));
        }
    }

    parts.push(format!("prov={:?}", fact.provenance));

    if !fact.origins.is_empty() {
        let origin_texts: Vec<String> = fact.origins.iter().map(format_origin).collect();
        parts.push(format!("origins={}", origin_texts.join(" | ")));
    }

    parts.join(", ")
}

fn format_body_label(body: &RuleBodySummary) -> String {
    match body.kind {
        RuleBodyKind::Primary => format!("body #{}", body.body_idx + 1),
        RuleBodyKind::Else => format!("else body #{}", body.body_idx),
    }
}

fn render_body_value(fact: Option<&TypeFact>, is_constant: bool) -> String {
    let label = if is_constant { "Constant" } else { "Value" };

    match fact {
        Some(fact) => {
            if let ConstantValue::Known(value) = &fact.constant {
                if let Ok(rendered) = serde_json::to_string(value) {
                    return format!("{}: {}", label, rendered);
                }
            }

            format!("{}: {}", label, describe_type_descriptor(&fact.descriptor))
        }
        None => format!("{}: Unknown", label),
    }
}

struct SpecializationBodyEntry<'a> {
    label: String,
    body: &'a RuleBodySummary,
    specialized_fact: Option<&'a TypeFact>,
    fallback_fact: Option<&'a TypeFact>,
    definition_rule: &'a Rule,
    body_idx: usize,
}

fn collect_specialization_bodies<'a>(
    rule: &'a Rule,
    definitions: &'a [DefinitionSummary],
    spec: &'a RuleSpecializationRecord,
) -> Vec<SpecializationBodyEntry<'a>> {
    let module_facts = spec.expr_facts.get(&spec.signature.module_idx);
    let mut entries = Vec::new();

    for definition in definitions {
        if definition.bodies.is_empty() {
            continue;
        }

        for (idx, body) in definition.bodies.iter().enumerate() {
            let specialized_fact = body
                .value_expr_idx
                .and_then(|expr_idx| module_facts.and_then(|facts| facts.get(&expr_idx)));

            entries.push(SpecializationBodyEntry {
                label: format_body_label(body),
                body,
                specialized_fact,
                fallback_fact: body.value_fact.as_ref(),
                definition_rule: rule,
                body_idx: idx,
            });
        }
    }

    entries
}

fn collect_body_verbose_info(
    module_idx: u32,
    rule: &Rule,
    body_idx: usize,
    facts: &impl ExprFactSource,
) -> Option<RuleVerboseInfo> {
    match rule {
        Rule::Spec { bodies, .. } => bodies.get(body_idx).map(|body| {
            let mut locals = LocalCollector::new();
            let mut statements = Vec::new();

            if let Some(assign) = &body.assign {
                let expr = assign.value.as_ref();
                let mut fact_lines = Vec::new();
                collect_expr_fact_lines(module_idx, expr, facts, &mut fact_lines, &mut locals);
                statements.push(StatementDisplay {
                    summary: format!("assign {}", format_expr(expr)),
                    fact_lines,
                });
            }

            statements.extend(process_query_statements(
                module_idx,
                body.query.as_ref(),
                facts,
                0,
                &mut locals,
            ));

            RuleVerboseInfo {
                locals: locals.into_vec(),
                statements,
            }
        }),
        _ => None,
    }
}

fn print_definition_bodies(
    module_idx: usize,
    rule: &Rule,
    definition: &DefinitionSummary,
    result: &TypeAnalysisResult,
    verbose: bool,
) {
    if definition.bodies.is_empty() {
        return;
    }

    println!("     Bodies:");
    let module_idx = module_idx as u32;

    for body in &definition.bodies {
        let label = format_body_label(body);
        let location = body
            .span
            .as_ref()
            .map(|span| format!(" ({})", span.format()))
            .unwrap_or_default();
        println!(
            "       - {}{}: {}",
            label.as_str(),
            location,
            render_body_value(body.value_fact.as_ref(), body.is_constant)
        );

        if verbose {
            if let Some(verbose_info) =
                collect_body_verbose_info(module_idx, rule, body.body_idx, result)
            {
                print_body_verbose_details(7, label.as_str(), &verbose_info);
            }
        }
    }
}

fn print_body_verbose_details(indent: usize, label: &str, info: &RuleVerboseInfo) {
    if info.locals.is_empty() && info.statements.is_empty() {
        return;
    }

    let prefix = " ".repeat(indent);
    println!("{}{} details:", prefix, label);

    if !info.locals.is_empty() {
        let locals_prefix = " ".repeat(indent + 2);
        println!("{}Locals:", locals_prefix);
        let entry_prefix = " ".repeat(indent + 4);
        for local in &info.locals {
            println!(
                "{}- {}{}",
                entry_prefix,
                local.name,
                format_local_fact_suffix(&local.fact)
            );
        }
    }

    if !info.statements.is_empty() {
        let statements_prefix = " ".repeat(indent + 2);
        println!("{}Statements:", statements_prefix);
        let entry_prefix = " ".repeat(indent + 4);
        for statement in &info.statements {
            println!("{}- {}", entry_prefix, statement.summary);
            if !statement.fact_lines.is_empty() {
                let fact_prefix = " ".repeat(indent + 6);
                for fact_line in &statement.fact_lines {
                    println!("{}{}", fact_prefix, fact_line);
                }
            }
        }
    }
}
