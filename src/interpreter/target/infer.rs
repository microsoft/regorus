use super::super::error::TargetCompileError;
use super::super::*;
use crate::ast::{BoolOp, Expr, Literal, Query, Rule};
use crate::compiled_policy::InferredResourceTypes;
use crate::value::Value;
use crate::{Rc, Schema};

type String = Rc<str>;

/// Analyzes policy rules to infer resource types from equality expressions.
///
/// This function examines the compiled policy rules corresponding to the effect path
/// and searches for equality statements that compare the resource selector field with
/// string literals. It identifies patterns like:
/// - `input.<resource_selector> == "resource_type_name"`
/// - `input["resource_selector"] == "resource_type_name"`
/// - `"resource_type_name" == input.<resource_selector>`
/// - `"resource_type_name" == input["resource_selector"]`
///
/// The `resource_selector` is determined by the target's resource schema selector
/// configuration (e.g., "type", "@odata.type").
///
/// # Schema Resolution
/// For each inferred resource type, the function attempts to find the corresponding
/// schema from the target's resource_schema_lookup table. If no specific schema is
/// found, it falls back to the default_resource_schema after validating compatibility.
///
/// # Returns
/// An InferredResourceTypes map mapping Query references to ResourceTypeInfo tuples
/// containing (resource_type_name, schema).
/// The results are also stored in the compiled policy's inferred_resource_types field
/// for later use during policy evaluation.
///
/// # Errors
/// Returns `TargetCompileError` if:
/// - Default resource schema is missing when needed
/// - Default schema is incompatible with the resource selector
/// - Default schema is not an object type
///
/// # Examples
/// For a policy with rules like:
/// ```rego
/// effect := "allow" { input.type == "Microsoft.Storage/storageAccounts" }
/// effect := "deny" { input["@odata.type"] == "microsoft.graph.user" }
/// ```
/// This function returns a map with entries for each query containing the resource type
/// conditions, mapping queries to their respective type names and schemas.
pub fn infer_resource_type(
    interpreter: &mut Interpreter,
) -> Result<InferredResourceTypes, TargetCompileError> {
    // Check if we have target info
    if let Some(ref target_info) = interpreter.compiled_policy.target_info {
        let target = &target_info.target;
        let effect_path = &target_info.effect_path;
        let resource_selector = &target.resource_schema_selector;

        let mut result = InferredResourceTypes::new();

        // Get rules for the effect path
        if let Some(rules) = interpreter.compiled_policy.rules.get(effect_path.as_ref()) {
            for rule in rules {
                analyze_rule_for_resource_types(rule, resource_selector, target, &mut result)?;
            }
        }

        // Note: We don't check default_rules because default rules cannot access input

        // Store the result in the compiled policy for later use
        let compiled_policy = Rc::make_mut(&mut interpreter.compiled_policy);
        compiled_policy.inferred_resource_types = Some(result.clone());

        Ok(result)
    } else {
        // No target info available
        Ok(InferredResourceTypes::new())
    }
}

fn analyze_rule_for_resource_types(
    rule: &Rule,
    resource_selector: &str,
    target: &crate::target::Target,
    result: &mut InferredResourceTypes,
) -> Result<(), TargetCompileError> {
    if let Rule::Spec { bodies, .. } = rule {
        for body in bodies {
            analyze_query_for_resource_types(&body.query, resource_selector, target, result)?;
        }
    }
    // Default rules typically don't contain resource type conditions
    Ok(())
}

fn analyze_query_for_resource_types(
    query: &Ref<Query>,
    resource_selector: &str,
    target: &crate::target::Target,
    result: &mut InferredResourceTypes,
) -> Result<(), TargetCompileError> {
    let mut found_resource_type: Option<String> = None;

    for stmt in &query.stmts {
        if let Literal::Expr { expr, .. } = &stmt.literal {
            if let Some(resource_type) = analyze_expr_for_resource_types(expr, resource_selector) {
                found_resource_type = Some(resource_type);
                break; // Found resource type, no need to continue searching
            }
        }
        // Note: We don't analyze NotExpr because it contains the opposite of type equality
        // (e.g., not input.type == "value" means the type is NOT that value)
        // Other literal statement (SomeVars, SomeIn, Every) don't typically contain
        // direct resource type comparisons
    }

    // Now handle the insertion outside the loop
    if let Some(resource_type) = found_resource_type {
        // Look up the schema for this resource type
        let resource_type_value = Value::String(resource_type.clone());
        if let Some(schema) = target.resource_schema_lookup.get(&resource_type_value) {
            result.insert(query.clone(), (resource_type, schema.clone()));
            return Ok(());
        }
        // If not found in lookup, use default schema
        let default_schema = get_validated_default_schema(target, resource_selector)?;
        result.insert(query.clone(), (resource_type, default_schema));
    } else {
        // If no resource type was found for this query, use default schema
        let default_schema = get_validated_default_schema(target, resource_selector)?;
        result.insert(query.clone(), ("<default>".into(), default_schema));
    }

    Ok(())
}

fn analyze_expr_for_resource_types(expr: &Expr, resource_selector: &str) -> Option<String> {
    // Only look for direct equality expressions: input.<resource_selector> == "string"
    if let Expr::BoolExpr {
        op: BoolOp::Eq,
        lhs,
        rhs,
        ..
    } = expr
    {
        // Check if this is input.<resource_selector> == "string"
        if let (Some(input_field), Some(string_value)) = (
            extract_input_field_access(lhs, resource_selector),
            extract_string_literal(rhs),
        ) {
            if input_field.as_ref() == resource_selector {
                return Some(string_value);
            }
        }
        // Also check the reverse: "string" == input.<resource_selector>
        else if let (Some(string_value), Some(input_field)) = (
            extract_string_literal(lhs),
            extract_input_field_access(rhs, resource_selector),
        ) {
            if input_field.as_ref() == resource_selector {
                return Some(string_value);
            }
        }
    }
    // We only look for direct equality expressions, no nested analysis
    None
}

/// Extract input field access like `input.type` or `input["@odata.type"]`
fn extract_input_field_access(expr: &Expr, _expected_field: &str) -> Option<String> {
    use crate::value::Value;

    match expr {
        // Handle input.field
        Expr::RefDot { refr, field, .. } => {
            if let (
                Expr::Var {
                    value: Value::String(var_name),
                    ..
                },
                Value::String(field_name),
            ) = (refr.as_ref(), &field.1)
            {
                if var_name.as_ref() == "input" {
                    return Some(field_name.clone());
                }
            }
        }
        // Handle input["field"] - the field is always a string literal
        Expr::RefBrack { refr, index, .. } => {
            if let (
                Expr::Var {
                    value: Value::String(var_name),
                    ..
                },
                Some(field_name),
            ) = (refr.as_ref(), extract_string_literal(index))
            {
                if var_name.as_ref() == "input" {
                    return Some(field_name);
                }
            }
        }
        _ => {}
    }
    None
}

/// Extract string literal from expression
fn extract_string_literal(expr: &Expr) -> Option<String> {
    use crate::value::Value;

    if let Expr::String {
        value: Value::String(s),
        ..
    } = expr
    {
        Some(s.clone())
    } else {
        None
    }
}

/// Get and validate the default resource schema.
/// Returns the default schema if it exists and is compatible with the resource selector.
fn get_validated_default_schema(
    target: &crate::target::Target,
    resource_selector: &str,
) -> Result<Rc<Schema>, TargetCompileError> {
    if let Some(default_schema) = &target.default_resource_schema {
        // Validate that default schema can handle the resource selector field
        validate_default_schema_compatibility(default_schema, resource_selector)?;
        Ok(default_schema.clone())
    } else {
        Err(TargetCompileError::MissingDefaultResourceSchema(
            format!("Target '{}' has no default resource schema", target.name).into(),
        ))
    }
}

/// Validate that the default schema is compatible with the resource selector field.
/// The schema must either allow additional properties or have a property matching the resource selector.
fn validate_default_schema_compatibility(
    schema: &Rc<Schema>,
    resource_selector: &str,
) -> Result<(), TargetCompileError> {
    use crate::schema::Type;

    match schema.as_type() {
        Type::Object {
            properties,
            additional_properties,
            ..
        } => {
            // Check if the schema has a property matching the resource selector
            if properties.contains_key(resource_selector) {
                return Ok(());
            }

            // Check if additional properties are allowed
            if additional_properties.is_some() {
                return Ok(());
            }

            // Neither condition is met
            Err(TargetCompileError::IncompatibleDefaultSchema(
                format!(
                    "Default resource schema must either have additional properties enabled or contain a '{}' property",
                    resource_selector
                ).into()
            ))
        }
        _ => {
            // Default schema is not an object type
            Err(TargetCompileError::InvalidDefaultSchemaType(
                "Default resource schema must be an object type".into(),
            ))
        }
    }
}
