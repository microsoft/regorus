// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::arithmetic_side_effects,
    clippy::shadow_unrelated,
    clippy::pattern_type_mismatch,
    clippy::as_conversions
)] // small arithmetic checks are intentional

pub mod limits;

use crate::ast::*;
use crate::builtins::*;
use crate::lexer::SourceStr;
use crate::number::Number;
use crate::parser::Parser;
use crate::*;

use alloc::collections::BTreeMap;

use anyhow::{bail, Result};
#[derive(Clone, Debug)]
pub(crate) enum PathComponent {
    String(String),
    Raw(String),
    Number { lexeme: String, value: Number },
}

impl PathComponent {
    pub(crate) fn value(&self) -> &str {
        match self {
            Self::String(value) | Self::Raw(value) => value,
            Self::Number { lexeme, .. } => lexeme,
        }
    }

    pub(crate) fn matches_path_component(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::String(left), Self::String(right)) => left == right,
            (Self::Raw(left), Self::Raw(right)) => left == right,
            (Self::Number { value: left, .. }, Self::Number { value: right, .. }) => left == right,
            _ => false,
        }
    }
}

fn is_identifier_component(component: &str) -> bool {
    let mut bytes = component.bytes();
    matches!(bytes.next(), Some(first) if first.is_ascii_alphabetic() || first == b'_')
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

pub(crate) fn append_path_component(path: &str, component: &str) -> Result<String> {
    let mut path = path.to_string();
    append_path_component_to(&mut path, component)?;
    Ok(path)
}

fn append_path_component_to(path: &mut String, component: &str) -> Result<()> {
    if is_identifier_component(component) {
        if !path.is_empty() {
            path.push('.');
        }
        path.push_str(component);
    } else {
        let literal = Value::from(component).to_json_str()?;
        path.push('[');
        path.push_str(&literal);
        path.push(']');
    }
    Ok(())
}

fn append_raw_path_component_to(path: &mut String, component: &str) {
    if !path.is_empty() {
        path.push('.');
    }
    path.push_str(component);
}

pub(crate) fn append_path_value_component(path: &str, component: &Value) -> Result<String> {
    match component {
        Value::String(value) => append_path_component(path, value.as_ref()),
        value => {
            if path.is_empty() {
                Ok(value.to_string())
            } else {
                Ok(format!("{path}.{value}"))
            }
        }
    }
}

pub(crate) fn format_path_components(components: &[PathComponent]) -> Result<String> {
    let mut path = String::new();
    for component in components {
        match component {
            PathComponent::String(value) => append_path_component_to(&mut path, value)?,
            PathComponent::Raw(value) => append_raw_path_component_to(&mut path, value),
            PathComponent::Number { lexeme, .. } => {
                append_raw_path_component_to(&mut path, lexeme);
            }
        }
    }
    Ok(path)
}

pub(crate) fn format_string_path(components: &[&str]) -> Result<String> {
    let mut path = String::new();
    for component in components {
        append_path_component_to(&mut path, component)?;
    }
    Ok(path)
}

pub(crate) fn split_canonical_path_root(path: &str) -> Option<(&str, &str)> {
    let root_end = path.find(['.', '[']).unwrap_or(path.len());
    if root_end == 0 {
        return None;
    }
    Some(path.split_at(root_end))
}

pub(crate) fn get_rule_path_components(refr: &Expr) -> Result<Vec<PathComponent>> {
    fn collect(refr: &Expr, components: &mut Vec<PathComponent>) -> Result<()> {
        match refr {
            Expr::Var { span, .. } => {
                components.push(PathComponent::String(span.text().to_string()));
            }
            Expr::RefDot { refr, field, .. } => {
                collect(refr, components)?;
                components.push(PathComponent::String(field.0.text().to_string()));
            }
            Expr::RefBrack { refr, index, .. } => {
                collect(refr, components)?;
                match index.as_ref() {
                    Expr::String { value, .. } => components.push(PathComponent::String(
                        value.as_string()?.as_ref().to_string(),
                    )),
                    Expr::Number { span, value, .. } => {
                        let Value::Number(number) = value else {
                            bail!("internal error: number expression has non-numeric value");
                        };
                        components.push(PathComponent::Number {
                            lexeme: span.text().to_string(),
                            value: number.clone(),
                        });
                    }
                    Expr::Bool { span, .. } | Expr::Null { span, .. } => {
                        components.push(PathComponent::Raw(span.text().to_string()));
                    }
                    _ => {
                        let index_components = Parser::get_path_ref_components(index)?;
                        components.extend(
                            index_components
                                .iter()
                                .map(|component| PathComponent::Raw(component.text().to_string())),
                        );
                    }
                }
            }
            _ => bail!("internal error: not a simple ref {refr:?}"),
        }
        Ok(())
    }

    let mut components = Vec::new();
    collect(refr, &mut components)?;
    Ok(components)
}

#[cfg(test)]
mod path_component_tests {
    use super::*;

    #[test]
    fn path_component_matching_preserves_scalar_identity_and_numeric_equality() {
        let integer = PathComponent::Number {
            lexeme: "1".to_string(),
            value: Number::from(1_i64),
        };
        let decimal = PathComponent::Number {
            lexeme: "1.0".to_string(),
            value: Number::from(1.0_f64),
        };
        let string = PathComponent::String("1".to_string());
        let boolean = PathComponent::Raw("true".to_string());
        let boolean_string = PathComponent::String("true".to_string());
        let null = PathComponent::Raw("null".to_string());
        let null_string = PathComponent::String("null".to_string());

        assert!(integer.matches_path_component(&decimal));
        assert!(!integer.matches_path_component(&string));
        assert!(!boolean.matches_path_component(&boolean_string));
        assert!(!null.matches_path_component(&null_string));
    }
}

pub fn get_path_string(refr: &Expr, document: Option<&str>) -> Result<String> {
    fn collect_simple(refr: &Expr, components: &mut Vec<PathComponent>) -> Result<()> {
        match refr {
            Expr::Var { span, .. } => {
                components.push(PathComponent::String(span.text().to_string()));
            }
            Expr::RefDot { refr, field, .. } => {
                collect_simple(refr, components)?;
                components.push(PathComponent::String(field.0.text().to_string()));
            }
            Expr::RefBrack { refr, index, .. } => {
                collect_simple(refr, components)?;
                if let Expr::String { value, .. } = index.as_ref() {
                    components.push(PathComponent::String(
                        value.as_string()?.as_ref().to_string(),
                    ));
                }
            }
            _ => bail!("internal error: not a simple ref {refr:?}"),
        }
        Ok(())
    }

    let mut components = Vec::new();
    collect_simple(refr, &mut components)?;
    let mut path = document.unwrap_or_default().to_string();
    for component in components {
        if let PathComponent::String(component) = component {
            path = append_path_component(&path, &component)?;
        }
    }
    Ok(path)
}

pub type FunctionTable = BTreeMap<String, (Vec<Ref<Rule>>, u8, Ref<Module>)>;

fn get_extra_arg_impl(
    expr: &Expr,
    module: Option<&str>,
    functions: &FunctionTable,
) -> Result<Option<Ref<Expr>>> {
    if let Expr::Call { fcn, params, .. } = expr {
        let full_path = get_path_string(fcn, module)?;
        let n_args = if let Some((_, n_args, _)) = functions.get(&full_path) {
            *n_args
        } else {
            let path = get_path_string(fcn, None)?;
            if let Some((_, n_args, _)) = functions.get(&path) {
                *n_args
            } else if let Some((_, n_args)) = BUILTINS.get(path.as_str()) {
                *n_args
            } else {
                return Ok(None);
            }
        };
        if (n_args as usize) + 1 == params.len() {
            return Ok(params.last().cloned());
        }
    }
    Ok(None)
}

pub fn get_extra_arg(
    expr: &Expr,
    module: Option<&str>,
    functions: &FunctionTable,
) -> Option<Ref<Expr>> {
    get_extra_arg_impl(expr, module, functions).unwrap_or_default()
}

pub fn gather_functions(modules: &[Ref<Module>]) -> Result<FunctionTable> {
    let mut table = FunctionTable::new();

    for module in modules {
        let module_path = get_path_string(&module.package.refr, Some("data"))?;
        for rule in &module.policy {
            if let Rule::Spec {
                span,
                head: RuleHead::Func { refr, args, .. },
                ..
            } = rule.as_ref()
            {
                let full_path = get_path_string(refr, Some(module_path.as_str()))?;

                if let Some((functions, arity, _)) = table.get_mut(&full_path) {
                    if args.len() as u8 != *arity {
                        bail!(span.error(
                            format!("{full_path} was previously defined with {arity} arguments.")
                                .as_str()
                        ));
                    }
                    functions.push(rule.clone());
                } else {
                    table.insert(
                        full_path,
                        (vec![rule.clone()], args.len() as u8, module.clone()),
                    );
                }
            }
        }
    }
    Ok(table)
}

pub fn get_root_var(mut expr: &Expr) -> Result<SourceStr> {
    let empty = expr.span().source_str().clone_empty();
    loop {
        match expr {
            Expr::Var { span: v, .. } => return Ok(v.source_str()),
            Expr::RefDot { refr, .. } | Expr::RefBrack { refr, .. } => expr = refr,
            _ => return Ok(empty),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::append_path_component;
    use alloc::format;
    use anyhow::Result;

    #[test]
    fn path_component_formatting_matches_rego_identifier_grammar() -> Result<()> {
        let cases = [
            ("ordinary_name_9", "data.ordinary_name_9"),
            ("if", "data.if"),
            ("9ordinary", r#"data["9ordinary"]"#),
            ("with-hyphen", r#"data["with-hyphen"]"#),
            ("a.b", r#"data["a.b"]"#),
            (r#"escaped".dot"#, r#"data["escaped\".dot"]"#),
            ("", r#"data[""]"#),
            ("éclair", r#"data["éclair"]"#),
        ];

        for (component, expected) in cases {
            let actual = append_path_component("data", component)?;
            if actual != expected {
                return Err(anyhow::Error::msg(format!(
                    "expected {expected}, got {actual}"
                )));
            }
        }

        Ok(())
    }
}
