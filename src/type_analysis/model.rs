// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use alloc::borrow::ToOwned;
use alloc::{
    boxed::Box,
    collections::BTreeMap,
    format,
    string::{String, ToString},
    vec::Vec,
};

use crate::{schema::Schema, value::Value, Rc};

/// Structural type information that is lightweight to manipulate while
/// propagating types through expressions.
#[derive(Clone, Debug, PartialEq)]
pub enum StructuralType {
    Any,
    Boolean,
    Number,
    Integer,
    String,
    Null,
    Array(Box<StructuralType>),
    Set(Box<StructuralType>),
    Object(StructuralObjectShape),
    Union(Vec<StructuralType>),
    Enum(Vec<Value>),
    Unknown,
}

impl StructuralType {
    pub fn any() -> Self {
        StructuralType::Any
    }

    pub fn boolean() -> Self {
        StructuralType::Boolean
    }

    pub fn from_schema(schema: &Schema) -> Self {
        use crate::schema::Type;
        match schema.as_type() {
            Type::Any { .. } => StructuralType::Any,
            Type::Boolean { .. } => StructuralType::Boolean,
            Type::Integer { .. } => StructuralType::Integer,
            Type::Number { .. } => StructuralType::Number,
            Type::Null { .. } => StructuralType::Null,
            Type::String { .. } => StructuralType::String,
            Type::Array { items, .. } => {
                StructuralType::Array(Box::new(StructuralType::from_schema(items)))
            }
            Type::Set { items, .. } => {
                StructuralType::Set(Box::new(StructuralType::from_schema(items)))
            }
            Type::Object { properties, .. } => {
                let mut shape = BTreeMap::new();
                for (name, prop_schema) in properties.iter() {
                    shape.insert(name.to_string(), StructuralType::from_schema(prop_schema));
                }
                StructuralType::Object(StructuralObjectShape { fields: shape })
            }
            Type::Enum { values, .. } => StructuralType::Enum((**values).clone()),
            Type::AnyOf(_) | Type::Const { .. } => StructuralType::Any,
        }
    }
}

/// Additional information about a structural object, namely the shape of
/// known fields. The analyser purposely keeps this light-weight – we only
/// track the fields that have been observed so far.
#[derive(Clone, Debug, PartialEq)]
pub struct StructuralObjectShape {
    pub fields: BTreeMap<String, StructuralType>,
}

impl Default for StructuralObjectShape {
    fn default() -> Self {
        Self::new()
    }
}

impl StructuralObjectShape {
    pub fn new() -> Self {
        StructuralObjectShape {
            fields: BTreeMap::new(),
        }
    }
}

/// The primary descriptor for a type fact associated with an expression.
#[derive(Clone, Debug)]
pub enum TypeDescriptor {
    Schema(Schema),
    Structural(StructuralType),
}

impl TypeDescriptor {
    pub fn schema(schema: Schema) -> Self {
        TypeDescriptor::Schema(schema)
    }

    pub fn structural(ty: StructuralType) -> Self {
        TypeDescriptor::Structural(ty)
    }

    pub fn as_schema(&self) -> Option<&Schema> {
        match self {
            TypeDescriptor::Schema(s) => Some(s),
            _ => None,
        }
    }
}

/// Where did a particular type fact originate from.
#[derive(Clone, Debug)]
pub enum TypeProvenance {
    SchemaInput,
    SchemaData,
    Literal,
    Assignment,
    Propagated,
    Builtin,
    Rule,
    Unknown,
}

/// Root source for values propagated through type analysis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceRoot {
    Input,
    Data,
}

/// Segment within an origin path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathSegment {
    Field(String),
    Index(usize),
    Any,
}

/// Captures provenance path information for a value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceOrigin {
    pub root: SourceRoot,
    pub path: Vec<PathSegment>,
    pub derived: bool,
}

impl SourceOrigin {
    pub fn new(root: SourceRoot) -> Self {
        SourceOrigin {
            root,
            path: Vec::new(),
            derived: false,
        }
    }

    pub fn from_path(root: SourceRoot, path: Vec<PathSegment>, derived: bool) -> Self {
        SourceOrigin {
            root,
            path,
            derived,
        }
    }

    pub fn mark_derived(mut self) -> Self {
        self.derived = true;
        self
    }

    pub fn with_segment(mut self, segment: PathSegment) -> Self {
        self.path.push(segment);
        self
    }
}

/// Constant information attached to a type fact.
#[derive(Clone, Debug)]
pub enum ConstantValue {
    Known(Value),
    Unknown,
}

impl ConstantValue {
    pub fn known(value: Value) -> Self {
        ConstantValue::Known(value)
    }

    pub fn unknown() -> Self {
        ConstantValue::Unknown
    }

    pub fn as_value(&self) -> Option<&Value> {
        match self {
            ConstantValue::Known(v) => Some(v),
            ConstantValue::Unknown => None,
        }
    }
}

/// Canonical representation of a rule specialization signature.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RuleSpecializationSignature {
    pub module_idx: u32,
    pub rule_idx: usize,
    pub arguments: Vec<SpecializationArgument>,
}

/// Canonicalized argument data used within a specialization signature.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SpecializationArgument {
    pub descriptor_key: String,
    pub constant: Option<Value>,
}

/// Metadata describing which specializations contributed to a type fact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecializationHit {
    pub signature: RuleSpecializationSignature,
}

/// Combined fact stored in lookup tables for each expression.
#[derive(Clone, Debug)]
pub struct TypeFact {
    pub descriptor: TypeDescriptor,
    pub constant: ConstantValue,
    pub provenance: TypeProvenance,
    pub origins: Vec<SourceOrigin>,
    pub specialization_hits: Vec<SpecializationHit>,
}

impl TypeFact {
    pub fn new(descriptor: TypeDescriptor, provenance: TypeProvenance) -> Self {
        TypeFact {
            descriptor,
            constant: ConstantValue::Unknown,
            provenance,
            origins: Vec::new(),
            specialization_hits: Vec::new(),
        }
    }

    pub fn with_constant(mut self, constant: ConstantValue) -> Self {
        self.constant = constant;
        self
    }

    pub fn with_origin(mut self, origin: SourceOrigin) -> Self {
        self.origins.push(origin);
        self
    }

    pub fn with_origins(mut self, origins: Vec<SourceOrigin>) -> Self {
        self.origins = origins;
        self
    }

    pub fn with_specialization_hit(mut self, hit: SpecializationHit) -> Self {
        self.specialization_hits.push(hit);
        self
    }

    pub fn with_specialization_hits(mut self, hits: Vec<SpecializationHit>) -> Self {
        self.specialization_hits.extend(hits);
        self
    }
}

impl RuleSpecializationSignature {
    pub fn from_facts(module_idx: u32, rule_idx: usize, arguments: &[TypeFact]) -> Self {
        let arguments = arguments
            .iter()
            .map(|fact| SpecializationArgument {
                descriptor_key: specialization_descriptor_key(&fact.descriptor),
                constant: fact.constant.as_value().cloned(),
            })
            .collect();

        RuleSpecializationSignature {
            module_idx,
            rule_idx,
            arguments,
        }
    }
}

fn specialization_descriptor_key(descriptor: &TypeDescriptor) -> String {
    match descriptor {
        TypeDescriptor::Schema(schema) => {
            structural_descriptor_key(&StructuralType::from_schema(schema))
        }
        TypeDescriptor::Structural(ty) => structural_descriptor_key(ty),
    }
}

fn structural_descriptor_key(ty: &StructuralType) -> String {
    match ty {
        StructuralType::Any => "any".to_owned(),
        StructuralType::Boolean => "boolean".to_owned(),
        StructuralType::Number => "number".to_owned(),
        StructuralType::Integer => "integer".to_owned(),
        StructuralType::String => "string".to_owned(),
        StructuralType::Null => "null".to_owned(),
        StructuralType::Array(inner) => {
            format!("array({})", structural_descriptor_key(inner))
        }
        StructuralType::Set(inner) => format!("set({})", structural_descriptor_key(inner)),
        StructuralType::Object(shape) => {
            if shape.fields.is_empty() {
                return "object".to_owned();
            }

            let mut parts = Vec::with_capacity(shape.fields.len());
            for (name, field_ty) in &shape.fields {
                parts.push(format!("{name}:{}", structural_descriptor_key(field_ty)));
            }
            format!("object{{{}}}", parts.join(","))
        }
        StructuralType::Union(types) => {
            if types.is_empty() {
                return "union()".to_owned();
            }

            let mut parts: Vec<String> = types.iter().map(structural_descriptor_key).collect();
            parts.sort();
            format!("union({})", parts.join("|"))
        }
        StructuralType::Enum(values) => {
            if values.is_empty() {
                return "enum()".to_owned();
            }

            let mut parts: Vec<String> = values.iter().map(|value| value.to_string()).collect();
            parts.sort();
            format!("enum({})", parts.join("|"))
        }
        StructuralType::Unknown => "unknown".to_owned(),
    }
}

/// Discriminates whether the descriptor is schema-backed or structural.
#[derive(Clone, Debug)]
pub enum HybridTypeKind {
    Schema,
    Structural,
}

/// Wrapper returned by the analyser.
#[derive(Clone, Debug)]
pub struct HybridType {
    pub fact: TypeFact,
    pub kind: HybridTypeKind,
}

impl HybridType {
    pub fn from_fact(fact: TypeFact) -> Self {
        let kind = match fact.descriptor {
            TypeDescriptor::Schema(_) => HybridTypeKind::Schema,
            TypeDescriptor::Structural(_) => HybridTypeKind::Structural,
        };
        HybridType { fact, kind }
    }
}

/// Diagnostics emitted by the analyser.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypeDiagnosticSeverity {
    Error,
    Warning,
}

#[derive(Clone, Debug)]
pub struct TypeDiagnostic {
    pub message: String,
    pub kind: TypeDiagnosticKind,
    pub severity: TypeDiagnosticSeverity,
    pub file: Rc<str>,
    pub line: u32,
    pub col: u32,
    pub end_line: u32,
    pub end_col: u32,
}

#[derive(Clone, Debug)]
pub enum TypeDiagnosticKind {
    SchemaViolation,
    InternalError,
    TypeMismatch,
    UnreachableStatement,
}

/// State of constant evaluation for a rule.
#[derive(Clone, Debug, Default)]
pub enum RuleConstantState {
    /// Not yet attempted
    #[default]
    Unknown,
    /// Currently being evaluated (for recursion detection)
    InProgress,
    /// Successfully evaluated to a constant value
    Done(Value),
    /// Cannot be constant folded (needs input/data or has recursion)
    NeedsRuntime,
}

/// Aggregated metadata for an analysed rule.
#[derive(Clone, Debug, Default)]
pub struct RuleAnalysis {
    pub input_dependencies: Vec<SourceOrigin>,
    pub rule_dependencies: Vec<String>,
    pub constant_state: RuleConstantState,
}

impl RuleAnalysis {
    pub fn record_origins(&mut self, origins: &[SourceOrigin]) {
        for origin in origins {
            if let Some(existing) = self
                .input_dependencies
                .iter_mut()
                .find(|candidate| candidate.root == origin.root && candidate.path == origin.path)
            {
                existing.derived |= origin.derived;
            } else {
                self.input_dependencies.push(origin.clone());
            }
        }
    }

    pub fn record_rule_dependency<S: Into<String>>(&mut self, dependency: S) {
        let dep = dependency.into();
        if !self
            .rule_dependencies
            .iter()
            .any(|existing| existing == &dep)
        {
            self.rule_dependencies.push(dep);
        }
    }

    pub fn merge(&mut self, other: RuleAnalysis) {
        self.record_origins(&other.input_dependencies);
        for dep in other.rule_dependencies {
            self.record_rule_dependency(dep);
        }
        // Keep the first constant state if already set
        if matches!(self.constant_state, RuleConstantState::Unknown) {
            self.constant_state = other.constant_state;
        }
    }
}
