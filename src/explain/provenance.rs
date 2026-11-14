// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Static provenance of the checks in a compiled RVM [`Program`].
//!
//! [`Provenance`] decodes, once per program and without running it, every
//! instruction that checks a condition: its policy text and location, its
//! [`ConditionKind`] and [`Operator`], the references its operands were read
//! from, and the rule or function that owns it. Explanation capture records
//! only program counters; reports resolve them through this table.
//!
//! Only programs compiled from Rego are decoded, as identified by
//! [`ProgramMetadata::language`](crate::rvm::program::ProgramMetadata::language)
//! (`"rego"`, or empty for the Rego compiler's programs). Programs from any
//! other language, such as Azure Policy, have no sites until that language
//! has its own decoder, so their conditions and their reads of the `context`
//! root are not described rather than misdescribed.

use super::report::{ConditionKind, Operator, RuleKind, SourceLocation};
use crate::lexer::{Lexer, Source, Token, TokenKind};
use crate::rvm::instructions::{GuardMode, Instruction};
use crate::rvm::program::{Program, SpanInfo};
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use core::num::{NonZeroU32, NonZeroUsize};

/// Identifies a [`CheckSite`] within its [`Provenance`].
///
/// Sites are numbered from 0 in program order, so compiling the same policy
/// with the same entry points gives the same ids. Explanations refer to a
/// check by id instead of repeating its text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SiteId(pub u32);

/// The rule body or function definition that a check belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct SiteOwner {
    /// Index of the rule; see [`Provenance::rule`].
    pub rule: usize,
    /// Index of the rule definition.
    pub definition: usize,
    /// Index of the body within the definition (`else` bodies count), or
    /// `None` for the matching of a function's arguments.
    pub body: Option<usize>,
}

/// A rule or function of the program.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct RuleOwner {
    /// Full path of the rule, for example `data.test.allow`.
    pub name: String,
    /// Kind of the rule.
    pub kind: RuleKind,
}

/// An instruction that checks a condition.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct CheckSite {
    /// Id of the site.
    pub id: SiteId,
    /// Program counter of the checking instruction.
    pub pc: usize,
    /// Rule body that the check belongs to.
    pub owner: SiteOwner,
    /// Position of the check among the checks of its owner body, from 0.
    /// With the owner's rule name, definition and body, this identifies
    /// the check independently of the other rules in the program.
    pub ordinal: usize,
    /// Kind of condition.
    pub kind: ConditionKind,
    /// Operator of a comparison or membership test.
    pub operator: Option<Operator>,
    /// The checked expression as written in the policy.
    pub text: String,
    /// Where the checked expression starts.
    pub location: Option<SourceLocation>,
    /// Reference the left operand (or the checked value) was read from, as
    /// written, for example `input.user.role`. A value bound by iteration
    /// reads as the collection followed by `[_]`, for example
    /// `input.items[_]`. `None` for literals and computed values.
    pub left_path: Option<String>,
    /// Reference the right operand was read from, as for `left_path`.
    pub right_path: Option<String>,
}

/// Static provenance of every check in a program. See the module docs.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Provenance {
    rules: Vec<RuleOwner>,
    sites: Vec<CheckSite>,
}

/// Whether `program` came from the Rego compiler, which leaves the language
/// empty. Other languages need their own decoder.
fn is_rego(program: &Program) -> bool {
    matches!(program.metadata.language.as_str(), "" | "rego")
}

impl Provenance {
    /// Decodes the checks of `program`.
    pub fn new(program: &Program) -> Self {
        if !is_rego(program) || program.rule_infos.is_empty() {
            return Self::default();
        }
        let sources: Vec<SourceIndex> = program
            .sources
            .iter()
            .map(|source| SourceIndex::new(&source.name, &source.content))
            .collect();
        let rules = program
            .rule_infos
            .iter()
            .map(|info| RuleOwner {
                name: info.name.clone(),
                kind: if info.function_info.is_some() {
                    RuleKind::Function
                } else {
                    RuleKind::from(info.rule_type.clone())
                },
            })
            .collect();
        let owners = owner_starts(program);
        let mut next_owner = 0_usize;
        let mut owner = None;
        // The reference each register holds, as written.
        let mut paths: Vec<Option<String>> = alloc::vec![None; 256];
        let mut sites: Vec<CheckSite> = Vec::new();
        let mut ordinal = 0_usize;
        for (pc, instruction) in program.instructions.iter().enumerate() {
            while let Some(&(start, next)) = owners.get(next_owner) {
                if start > pc {
                    break;
                }
                paths.fill(None);
                ordinal = 0;
                owner = Some(next);
                next_owner = next_owner.saturating_add(1);
            }
            let span = program.instruction_spans.get(pc).and_then(Option::as_ref);
            if let (Some(owner), Some(shape)) = (owner, check_shape(program, pc, instruction)) {
                let (text, location) = span
                    .and_then(|span| Some((sources.get(span.source_index)?, span)))
                    .and_then(|(source, span)| {
                        let (mut first, mut last) = source.expression(span)?;
                        if shape.kind == ConditionKind::Iteration {
                            (first, last) = source.include_grouping(first, last);
                        }
                        Some((source.text(first, last)?, Some(source.location(first)?)))
                    })
                    .unwrap_or_default();
                let path = |reg: Option<u8>| paths.get(usize::from(reg?)).cloned().flatten();
                sites.push(CheckSite {
                    id: SiteId(u32::try_from(sites.len()).unwrap_or(u32::MAX)),
                    pc,
                    owner,
                    ordinal,
                    kind: shape.kind,
                    operator: shape.operator,
                    text,
                    location,
                    left_path: path(shape.left),
                    right_path: path(shape.right),
                });
                ordinal = ordinal.saturating_add(1);
            }
            track(program, &sources, instruction, span, &mut paths);
        }
        Self { rules, sites }
    }

    /// All checks, in program order (`sites()[i].id == SiteId(i)`).
    pub fn sites(&self) -> &[CheckSite] {
        &self.sites
    }

    /// The check with id `id`.
    pub fn site(&self, id: SiteId) -> Option<&CheckSite> {
        self.sites.get(usize::try_from(id.0).ok()?)
    }

    /// The check performed by the instruction at `pc`, if it is one.
    pub fn site_at(&self, pc: usize) -> Option<&CheckSite> {
        let index = self.sites.binary_search_by_key(&pc, |site| site.pc).ok()?;
        self.sites.get(index)
    }

    /// The rule or function with index `index`, as used by
    /// [`SiteOwner::rule`].
    pub fn rule(&self, index: usize) -> Option<&RuleOwner> {
        self.rules.get(index)
    }
}

struct Shape {
    kind: ConditionKind,
    operator: Option<Operator>,
    left: Option<u8>,
    right: Option<u8>,
}

/// Classifies the instruction at `pc` if it checks a condition. The guards
/// the compiler adds to make sure a binding is defined are not checks.
fn check_shape(program: &Program, pc: usize, instruction: &Instruction) -> Option<Shape> {
    let shape = |kind, operator, left, right| Shape {
        kind,
        operator,
        left,
        right,
    };
    match *instruction {
        Instruction::Guard {
            register,
            mode: GuardMode::Condition,
        } => {
            let writer = pc
                .checked_sub(1)
                .and_then(|previous| program.instructions.get(previous));
            let comparison = |operator, left, right| {
                shape(
                    ConditionKind::Comparison,
                    Some(operator),
                    Some(left),
                    Some(right),
                )
            };
            Some(match writer.copied() {
                Some(Instruction::Eq { dest, left, right }) if dest == register => {
                    comparison(Operator::Eq, left, right)
                }
                Some(Instruction::Ne { dest, left, right }) if dest == register => {
                    comparison(Operator::Ne, left, right)
                }
                Some(Instruction::Lt { dest, left, right }) if dest == register => {
                    comparison(Operator::Lt, left, right)
                }
                Some(Instruction::Le { dest, left, right }) if dest == register => {
                    comparison(Operator::Le, left, right)
                }
                Some(Instruction::Gt { dest, left, right }) if dest == register => {
                    comparison(Operator::Gt, left, right)
                }
                Some(Instruction::Ge { dest, left, right }) if dest == register => {
                    comparison(Operator::Ge, left, right)
                }
                Some(Instruction::Contains {
                    dest,
                    collection,
                    value,
                }) if dest == register => shape(
                    ConditionKind::Membership,
                    Some(Operator::In),
                    Some(value),
                    Some(collection),
                ),
                Some(Instruction::Not { dest, operand }) if dest == register => {
                    keyed_membership(program, pc, register).unwrap_or_else(|| {
                        shape(ConditionKind::Negation, None, Some(operand), None)
                    })
                }
                // A loop's result guard: an `every` is checked at its
                // `LoopStart` site. The VM doesn't yet report the guard that
                // fails an `every` iteration when a `some ... in` or indexed
                // loop in its body matches nothing, so it has no site either.
                Some(Instruction::LoopNext {
                    body_start,
                    loop_end,
                }) if usize::from(loop_end) == pc
                    && loop_result(program, body_start) == Some(register) =>
                {
                    return None;
                }
                _ => shape(ConditionKind::Truthiness, None, Some(register), None),
            })
        }
        Instruction::Guard {
            register,
            mode: GuardMode::Not,
        } => Some(shape(ConditionKind::Negation, None, Some(register), None)),
        Instruction::AssertEq { left, right } => Some(shape(
            ConditionKind::Comparison,
            Some(Operator::Eq),
            Some(left),
            Some(right),
        )),
        Instruction::LoopStart { params_index } => {
            let params = program.instruction_data.get_loop_params(params_index)?;
            Some(shape(
                ConditionKind::Iteration,
                None,
                Some(params.collection),
                None,
            ))
        }
        _ => None,
    }
}

/// The result register of the loop whose body starts at `body_start`.
fn loop_result(program: &Program, body_start: u16) -> Option<u8> {
    let start = usize::from(body_start).checked_sub(1)?;
    match *program.instructions.get(start)? {
        Instruction::LoopStart { params_index } => program
            .instruction_data
            .get_loop_params(params_index)
            .map(|params| params.result_reg),
        _ => None,
    }
}

/// Keyed membership is lowered to Index, Eq and two in-place Nots so that a
/// missing key produces false rather than Undefined.
fn keyed_membership(program: &Program, pc: usize, register: u8) -> Option<Shape> {
    let instruction = |offset: usize| {
        pc.checked_sub(offset)
            .and_then(|index| program.instructions.get(index))
            .copied()
    };
    match (
        instruction(1)?,
        instruction(2)?,
        instruction(3)?,
        instruction(4)?,
    ) {
        (
            Instruction::Not {
                dest: first_dest,
                operand: first_operand,
            },
            Instruction::Not {
                dest: second_dest,
                operand: second_operand,
            },
            Instruction::Eq {
                dest: eq_dest,
                left: indexed,
                ..
            },
            Instruction::Index {
                dest: index_dest,
                container,
                key,
            },
        ) if first_dest == register
            && first_operand == register
            && second_dest == register
            && second_operand == register
            && eq_dest == register
            && indexed == index_dest =>
        {
            Some(Shape {
                kind: ConditionKind::Membership,
                operator: Some(Operator::In),
                left: Some(key),
                right: Some(container),
            })
        }
        _ => None,
    }
}

/// Start of each rule body and argument-matching block, sorted by pc. The
/// compiler emits each rule's code contiguously, so a body runs from its
/// start to the next start.
fn owner_starts(program: &Program) -> Vec<(usize, SiteOwner)> {
    let mut starts = Vec::new();
    for (rule, info) in program.rule_infos.iter().enumerate() {
        for (definition, bodies) in info.definitions.iter().enumerate() {
            let destructuring = info.destructuring_blocks.get(definition).copied().flatten();
            let entries = destructuring.map(|pc| (pc, None)).into_iter().chain(
                bodies
                    .iter()
                    .enumerate()
                    .map(|(body, &pc)| (pc, Some(body))),
            );
            for (pc, body) in entries {
                if let Ok(pc) = usize::try_from(pc) {
                    let owner = SiteOwner {
                        rule,
                        definition,
                        body,
                    };
                    starts.push((pc, owner));
                }
            }
        }
    }
    starts.sort_by_key(|&(pc, _)| pc);
    starts
}

/// Updates `paths` with the registers that `instruction` writes.
fn track(
    program: &Program,
    sources: &[SourceIndex],
    instruction: &Instruction,
    span: Option<&SpanInfo>,
    paths: &mut [Option<String>],
) {
    let path = |reg: u8| paths.get(usize::from(reg)).cloned().flatten();
    let value = match *instruction {
        Instruction::Move { src, .. } => path(src),
        Instruction::LoadInput { .. } => Some("input".to_string()),
        Instruction::LoadData { .. } => Some("data".to_string()),
        Instruction::LoopStart { params_index } => {
            let Some(params) = program.instruction_data.get_loop_params(params_index) else {
                return;
            };
            let value = path(params.collection).map(|path| alloc::format!("{path}[_]"));
            for reg in [params.key_reg, params.result_reg, params.value_reg] {
                if let Some(slot) = paths.get_mut(usize::from(reg)) {
                    *slot = None;
                }
            }
            // A loop that needs no key, such as `every x in xs`, uses one
            // register for the key and the value; it holds the value.
            if let Some(slot) = paths.get_mut(usize::from(params.value_reg)) {
                *slot = value;
            }
            return;
        }
        Instruction::Index { .. }
        | Instruction::IndexLiteral { .. }
        | Instruction::ChainedIndex { .. }
        | Instruction::VirtualDataDocumentLookup { .. }
        | Instruction::CallRule { .. } => span.and_then(|span| {
            let source = sources.get(span.source_index)?;
            let (first, last) = source.expression(span)?;
            let (first, last) = source.strip_grouping(first, last);
            source.is_reference(first, last).then_some(())?;
            source.text(first, last)
        }),
        _ => None,
    };
    for reg in writes(program, instruction).into_iter().flatten() {
        if let Some(slot) = paths.get_mut(usize::from(reg)) {
            *slot = value.clone();
        }
    }
}

/// The registers that `instruction` writes. Loop and comprehension
/// registers are attributed to the instruction that starts the loop or
/// comprehension.
fn writes(program: &Program, instruction: &Instruction) -> [Option<u8>; 3] {
    use Instruction::*;
    let data = &program.instruction_data;
    match *instruction {
        Load { dest, .. }
        | LoadTrue { dest }
        | LoadFalse { dest }
        | LoadNull { dest }
        | LoadBool { dest, .. }
        | LoadData { dest }
        | LoadInput { dest }
        | LoadContext { dest }
        | LoadMetadata { dest }
        | Move { dest, .. }
        | Add { dest, .. }
        | Sub { dest, .. }
        | Mul { dest, .. }
        | Div { dest, .. }
        | Mod { dest, .. }
        | Eq { dest, .. }
        | Ne { dest, .. }
        | Lt { dest, .. }
        | Le { dest, .. }
        | Gt { dest, .. }
        | Ge { dest, .. }
        | And { dest, .. }
        | Or { dest, .. }
        | Not { dest, .. }
        | HostAwait { dest, .. }
        | Index { dest, .. }
        | IndexLiteral { dest, .. }
        | ArrayNew { dest }
        | SetNew { dest }
        | Contains { dest, .. }
        | Count { dest, .. }
        | CallRule { dest, .. }
        | PolicyCondition { dest, .. } => [Some(dest), None, None],
        ArrayPush { arr, .. } | ArrayPushDefined { arr, .. } => [Some(arr), None, None],
        SetAdd { set, .. } => [Some(set), None, None],
        ObjectSet { obj, .. } => [Some(obj), None, None],
        CoalesceUndefinedToNull { register } => [Some(register), None, None],
        RuleInit { result_reg, .. } => [Some(result_reg), None, None],
        LogicalBlockStart { result, .. }
        | AllOfNext { result, .. }
        | AnyOfNext { result, .. }
        | LogicalBlockEnd { result, .. } => [Some(result), None, None],
        BuiltinCall { params_index } => data
            .get_builtin_call_params(params_index)
            .map_or([None; 3], |p| [Some(p.dest), None, None]),
        FunctionCall { params_index } => data
            .get_function_call_params(params_index)
            .map_or([None; 3], |p| [Some(p.dest), None, None]),
        ObjectCreate { params_index } => data
            .get_object_create_params(params_index)
            .map_or([None; 3], |p| [Some(p.dest), None, None]),
        ArrayCreate { params_index } => data
            .get_array_create_params(params_index)
            .map_or([None; 3], |p| [Some(p.dest), None, None]),
        SetCreate { params_index } => data
            .get_set_create_params(params_index)
            .map_or([None; 3], |p| [Some(p.dest), None, None]),
        VirtualDataDocumentLookup { params_index } => data
            .get_virtual_data_document_lookup_params(params_index)
            .map_or([None; 3], |p| [Some(p.dest), None, None]),
        ChainedIndex { params_index } => data
            .get_chained_index_params(params_index)
            .map_or([None; 3], |p| [Some(p.dest), None, None]),
        LoopStart { params_index } => data.get_loop_params(params_index).map_or([None; 3], |p| {
            [Some(p.key_reg), Some(p.value_reg), Some(p.result_reg)]
        }),
        ComprehensionBegin { params_index } => data
            .get_comprehension_begin_params(params_index)
            .map_or([None; 3], |p| {
                [Some(p.key_reg), Some(p.value_reg), Some(p.result_reg)]
            }),
        Return { .. }
        | AssertEq { .. }
        | Guard { .. }
        | ReturnUndefinedIfNotTrue { .. }
        | LoopNext { .. }
        | DestructuringSuccess {}
        | RuleReturn {}
        | Halt {}
        | ComprehensionYield { .. }
        | ComprehensionEnd {} => [None; 3],
    }
}

/// The tokens of one source, as the parser read them.
///
/// The parser gives an expression the line and column of one of its tokens
/// and the length from its first token to its last; a string token's span
/// excludes its quotes. A statement and a literal start at their first
/// token, but a reference such as `input.user.name` or `f(x)` points at its
/// last `.`, `[` or `(`, and an operation such as `a + b` or `a | b` at its
/// operator. The expression is found as the tokens around that one that
/// span the length. A check whose expression cannot be found this way, such
/// as one anchored at a unary minus, has empty text and no location.
struct SourceIndex<'a> {
    file: &'a str,
    content: &'a str,
    tokens: Vec<SourceToken>,
}

#[derive(Clone, Copy)]
struct SourceToken {
    line: usize,
    column: usize,
    /// Byte range as the lexer reports it, without quotes.
    start: usize,
    end: usize,
    kind: TokenClass,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TokenClass {
    Name,
    Number,
    /// A string or raw string.
    Quoted,
    Symbol,
}

impl SourceToken {
    /// Byte range including the quotes of a string.
    const fn lexeme(&self) -> (usize, usize) {
        match self.kind {
            TokenClass::Quoted => (self.start.saturating_sub(1), self.end.saturating_add(1)),
            _ => (self.start, self.end),
        }
    }
}

impl<'a> SourceIndex<'a> {
    fn new(file: &'a str, content: &'a str) -> Self {
        let mut tokens = Vec::new();
        let max = NonZeroUsize::MAX;
        if let Ok(source) = Source::from_contents_with_limits(file.into(), content.into(), max, max)
        {
            let to_usize = |n: u32| usize::try_from(n).unwrap_or(usize::MAX);
            let mut lexer = Lexer::new(&source);
            lexer.set_max_col(NonZeroU32::MAX);
            while let Ok(Token(kind, span)) = lexer.next_token() {
                let kind = match kind {
                    TokenKind::Ident => TokenClass::Name,
                    TokenKind::Number => TokenClass::Number,
                    TokenKind::String | TokenKind::RawString => TokenClass::Quoted,
                    TokenKind::Eof => break,
                    _ => TokenClass::Symbol,
                };
                tokens.push(SourceToken {
                    line: to_usize(span.line),
                    column: to_usize(span.col),
                    start: to_usize(span.start),
                    end: to_usize(span.end),
                    kind,
                });
            }
        }
        Self {
            file,
            content,
            tokens,
        }
    }

    fn symbol(&self, index: usize) -> Option<&str> {
        let token = self.tokens.get(index)?;
        (token.kind == TokenClass::Symbol)
            .then(|| self.content.get(token.start..token.end))
            .flatten()
    }

    fn is_keyword(&self, index: usize) -> bool {
        self.tokens.get(index).is_some_and(|token| {
            token.kind == TokenClass::Name
                && matches!(
                    self.content.get(token.start..token.end),
                    Some(
                        "as" | "contains"
                            | "default"
                            | "else"
                            | "every"
                            | "if"
                            | "in"
                            | "not"
                            | "some"
                            | "with"
                    )
                )
        })
    }

    /// Whether the token at `index` continues a reference: a `[` or `(`
    /// directly after a term, or the `(` of a call after a space.
    fn continues(&self, index: usize) -> bool {
        let before = index.wrapping_sub(1);
        let (Some(previous), Some(token)) = (self.tokens.get(before), self.tokens.get(index))
        else {
            return false;
        };
        let call = self.symbol(index) == Some("(")
            && previous.kind == TokenClass::Name
            && previous.line == token.line
            && !self.is_keyword(before);
        let ends_term = previous.kind != TokenClass::Symbol
            || matches!(self.symbol(before), Some(")" | "]" | "}"));
        call || (matches!(self.symbol(index), Some("[" | "("))
            && ends_term
            && previous.lexeme().1 == token.start)
    }

    /// The first and last token of the expression of `span`.
    fn expression(&self, span: &SpanInfo) -> Option<(usize, usize)> {
        let anchor = self
            .tokens
            .binary_search_by(|t| (t.line, t.column).cmp(&(span.line, span.column)))
            .ok()?;
        let at = self.tokens.get(anchor)?;
        // The expression ending with token `last`, if it is balanced.
        let ending = |last: usize| {
            let start = self.tokens.get(last)?.end.checked_sub(span.length)?;
            let first = self.tokens.binary_search_by_key(&start, |t| t.start).ok()?;
            (first <= anchor && self.balanced(first, last)).then_some((first, last))
        };
        let starting = || {
            let end = at.start.checked_add(span.length)?;
            let rest = self.tokens.get(anchor..)?;
            let last = anchor.checked_add(rest.binary_search_by_key(&end, |t| t.end).ok()?)?;
            self.balanced(anchor, last).then_some((anchor, last))
        };
        match self.symbol(anchor) {
            // A reference ends with the field or brackets after its last
            // separator.
            Some(".") => ending(anchor.checked_add(1)?),
            Some("[" | "(") if self.continues(anchor) => {
                ending(self.closing(anchor, self.tokens.len())?)
            }
            Some(_) if self.bracket(anchor) == 0 => {
                // An operation: the expression must be the only one around
                // its operator that has the length of the span and starts
                // and ends between operands.
                let mut found = None;
                for first in (0..anchor).rev() {
                    let start = self.tokens.get(first)?.start;
                    let end = start.checked_add(span.length)?;
                    if end <= at.end {
                        break;
                    }
                    let rest = self.tokens.get(anchor..)?;
                    let Ok(last) = rest.binary_search_by_key(&end, |t| t.end) else {
                        continue;
                    };
                    let last = anchor.checked_add(last)?;
                    if self.bounded(first, last) && self.balanced(first, last) {
                        if found.is_some() {
                            return None;
                        }
                        found = Some((first, last));
                    }
                }
                found
            }
            // Anything else starts the expression.
            _ => starting(),
        }
    }

    /// Whether an operand can start at token `first` and end at `last`:
    /// neither continues the term or statement around it.
    fn bounded(&self, first: usize, last: usize) -> bool {
        let before = first.wrapping_sub(1);
        let starts = match (self.tokens.get(before), self.tokens.get(first)) {
            (Some(token), Some(at)) => {
                token.line < at.line
                    || self.is_keyword(before)
                    || (token.kind == TokenClass::Symbol
                        && !matches!(self.symbol(before), Some("." | ")" | "]" | "}")))
            }
            _ => true,
        };
        let ends = self.tokens.get(last).is_some_and(|token| {
            token.kind != TokenClass::Symbol || matches!(self.symbol(last), Some(")" | "]" | "}"))
        });
        let next = last.saturating_add(1);
        starts && ends && self.symbol(next) != Some(".") && !self.continues(next)
    }

    /// 1 for a token that opens a bracket, -1 for one that closes it.
    fn bracket(&self, index: usize) -> i8 {
        let Some(token) = self.tokens.get(index) else {
            return 0;
        };
        match self.content.get(token.start..token.end) {
            // The lexer reads an empty set's `set(` as one token.
            Some("[" | "(" | "{" | "set(") if token.kind != TokenClass::Quoted => 1,
            Some("]" | ")" | "}") if token.kind == TokenClass::Symbol => -1,
            _ => 0,
        }
    }

    /// The token closing the bracket at `open`, if it is before `limit`.
    fn closing(&self, open: usize, limit: usize) -> Option<usize> {
        let mut depth = 0_usize;
        for index in open..limit {
            depth = match self.bracket(index) {
                1 => depth.saturating_add(1),
                -1 => depth.checked_sub(1)?,
                _ => continue,
            };
            if depth == 0 {
                return Some(index);
            }
        }
        None
    }

    /// Whether the brackets of tokens `first..=last` match.
    fn balanced(&self, first: usize, last: usize) -> bool {
        let mut depth = 0_usize;
        for index in first..=last {
            depth = match (self.bracket(index), depth.checked_sub(1)) {
                (1, _) => depth.saturating_add(1),
                (-1, Some(depth)) => depth,
                (-1, None) => return false,
                _ => depth,
            };
        }
        depth == 0
    }

    /// Remove parentheses that wrap the entire expression, not parentheses
    /// belonging to a call or to a subexpression.
    fn strip_grouping(&self, mut first: usize, mut last: usize) -> (usize, usize) {
        while self.symbol(first) == Some("(")
            && self.closing(first, last.saturating_add(1)) == Some(last)
        {
            first = first.saturating_add(1);
            last = last.saturating_sub(1);
        }
        (first, last)
    }

    /// Include matched source parentheses surrounding an expression. The
    /// parser drops grouping nodes, but provenance text must retain them.
    fn include_grouping(&self, mut first: usize, mut last: usize) -> (usize, usize) {
        while let Some(open) = first.checked_sub(1) {
            if self.symbol(open) != Some("(")
                || self.closing(open, self.tokens.len()) != last.checked_add(1)
            {
                break;
            }
            first = open;
            last = last.saturating_add(1);
        }
        (first, last)
    }

    /// Whether tokens `first..=last` are a reference such as `input.a` or
    /// `data.roles[input.role]`, rather than a computed value.
    fn is_reference(&self, first: usize, last: usize) -> bool {
        if self.tokens.get(first).map(|t| t.kind) != Some(TokenClass::Name) {
            return false;
        }
        let mut index = first.saturating_add(1);
        while index <= last {
            if !self.continues(index) && self.symbol(index) != Some(".") {
                return false;
            }
            index = match self.symbol(index) {
                Some(".") => {
                    let field = index.saturating_add(1);
                    if self.tokens.get(field).map(|t| t.kind) != Some(TokenClass::Name) {
                        return false;
                    }
                    field.saturating_add(1)
                }
                Some("[") => match self.closing(index, last.saturating_add(1)) {
                    Some(close) => close.saturating_add(1),
                    None => return false,
                },
                Some("(") => return false,
                _ => return false,
            };
        }
        index == last.saturating_add(1)
    }

    /// Text of tokens `first..=last`.
    fn text(&self, first: usize, last: usize) -> Option<String> {
        let start = self.tokens.get(first)?.lexeme().0;
        let end = self.tokens.get(last)?.lexeme().1;
        Some(self.content.get(start..end)?.to_string())
    }

    /// Where the token `first` starts.
    fn location(&self, first: usize) -> Option<SourceLocation> {
        let token = self.tokens.get(first)?;
        // The lexer places a string after its opening quote.
        let column = match token.kind {
            TokenClass::Quoted => token.column.checked_sub(1)?,
            _ => token.column,
        };
        Some(SourceLocation {
            file: self.file.into(),
            line: token.line,
            column,
        })
    }
}

#[cfg(test)]
#[allow(clippy::panic_in_result_fn)]
mod tests;
