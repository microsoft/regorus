// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::as_conversions)]

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{enforce_limit, ensure_args_count, ensure_numeric, ensure_string};
use crate::lexer::Span;
use crate::value::Value;
use crate::*;

use anyhow::{bail, Result};
use regex::{Regex, RegexBuilder};

// ---------------------------------------------------------------------------
// Compiled-regex cache (feature = "cache")
//
// When enabled, compiled Regex objects are stored in a bounded LRU cache
// protected by a Mutex (parking_lot when std, spin when no_std).
// The capacity is configurable at runtime
// via regorus::cache::configure().
// ---------------------------------------------------------------------------

/// Maximum compiled NFA size (in bytes) for a regex pattern.
/// This bounds both compilation time and match-time cost by limiting the
/// automaton's structural complexity. At 100 KiB, every real-world policy
/// pattern (IPv4, hostname, semver, UUID, image-digest, CIDR, etc.) compiles
/// comfortably, while adversarial patterns that would otherwise cause
/// expensive DFA construction are rejected at compile time.
const REGEX_SIZE_LIMIT: usize = 100 * 1024;

/// Compile a regex pattern with a size limit to bound resource consumption.
fn compile_regex(pattern: &str) -> core::result::Result<Regex, regex::Error> {
    RegexBuilder::new(pattern)
        .size_limit(REGEX_SIZE_LIMIT)
        .build()
}

/// Compile a regex pattern, using the cache when the `cache` feature
/// is enabled and falling back to direct compilation otherwise.
fn get_or_compile_regex(pattern: &str) -> core::result::Result<Regex, regex::Error> {
    #[cfg(feature = "cache")]
    {
        {
            let mut cache = crate::cache::REGEX_CACHE.lock();
            if let Some(re) = cache.get(pattern) {
                return Ok(re.clone());
            }
        }
        let re = compile_regex(pattern)?;
        {
            let mut cache = crate::cache::REGEX_CACHE.lock();
            cache.put(alloc::string::String::from(pattern), re.clone());
            Ok(re)
        }
    }
    #[cfg(not(feature = "cache"))]
    {
        compile_regex(pattern)
    }
}

/// Compile a regex for use in a builtin function.
///
/// - `CompiledTooBig` is raised as [`LimitError::RegexSizeLimitExceeded`] so
///   that it propagates as a hard error even in non-strict mode.
/// - Syntax errors produce a span-attached "invalid regex" error that the
///   evaluator may swallow to `Undefined` in non-strict mode (OPA-compatible).
fn compile_regex_for_builtin(span: &Span, pattern: &str) -> Result<Regex> {
    get_or_compile_regex(pattern).map_err(|e| match e {
        regex::Error::CompiledTooBig(_) => {
            anyhow::Error::new(crate::utils::limits::LimitError::RegexSizeLimitExceeded {
                limit: REGEX_SIZE_LIMIT,
            })
        }
        _ => anyhow::anyhow!(span.error("invalid regex")),
    })
}

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert(
        "regex.find_all_string_submatch_n",
        (find_all_string_submatch_n, 3),
    );
    m.insert("regex.find_n", (find_n, 3));
    m.insert("regex.globs_match", (globs_match, 2));
    m.insert("regex.is_valid", (is_valid, 1));
    m.insert("regex.match", (regex_match, 2));
    m.insert("regex.replace", (regex_replace, 3));
    m.insert("regex.split", (regex_split, 2));
    m.insert("regex.template_match", (regex_template_match, 4));
}

// ---------------------------------------------------------------------------
// regex.globs_match
//
// OPA's `regex.globs_match(glob1, glob2)` is true when the two glob-style
// expressions match at least one common non-empty string. OPA delegates to
// github.com/yashtewari/glob-intersection (Apache-2.0). This module follows
// that library's parser and intersection algorithm, rewritten in Rust, so
// both accept the same syntax and give the same answers.
//
// Syntax: literal characters, `.` (any character), `[...]` sets with `a-z`
// ranges, the flags `+` and `*` after a token, and `\` to escape the next
// character. `?` and `^` have no special meaning, and inside a set only `]`,
// `-` and `\` are special.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
enum GlobFlag {
    None,
    Plus,
    Star,
}

#[derive(Clone, PartialEq)]
enum GlobKind {
    Char(char),
    Dot,
    /// Sorted, non-overlapping, inclusive ranges of code points.
    Set(Vec<(u32, u32)>),
}

#[derive(Clone)]
struct GlobToken {
    kind: GlobKind,
    flag: GlobFlag,
}

impl GlobToken {
    /// Whether the two tokens can match a common character, ignoring flags.
    fn matches(&self, other: &Self) -> bool {
        match self.kind {
            GlobKind::Dot => true,
            GlobKind::Char(a) => match other.kind {
                GlobKind::Dot => true,
                GlobKind::Char(b) => a == b,
                GlobKind::Set(ref s) => Self::set_has(s, a),
            },
            GlobKind::Set(ref a) => match other.kind {
                GlobKind::Dot => true,
                GlobKind::Char(c) => Self::set_has(a, c),
                GlobKind::Set(ref b) => a
                    .iter()
                    .any(|&(alo, ahi)| b.iter().any(|&(blo, bhi)| alo <= bhi && blo <= ahi)),
            },
        }
    }

    fn set_has(set: &[(u32, u32)], c: char) -> bool {
        let c = u32::from(c);
        set.iter().any(|&(lo, hi)| lo <= c && c <= hi)
    }
}

fn glob_error(input: &[char], pos: usize, msg: &str) -> anyhow::Error {
    let input: String = input.iter().collect();
    anyhow::anyhow!("input:{input}, pos:{pos}, {msg}: the input provided is invalid")
}

enum GlobRune {
    End,
    /// Index after the rune, the rune, and whether it was escaped.
    Rune(usize, char, bool),
}

fn glob_next_rune(index: usize, input: &[char]) -> Result<GlobRune> {
    match input.get(index) {
        None => Ok(GlobRune::End),
        Some(&'\\') => match input.get(index + 1) {
            Some(&r) => Ok(GlobRune::Rune(index + 2, r, true)),
            None => Err(glob_error(
                input,
                index,
                "input ends with a \\ (escape) character",
            )),
        },
        Some(&r) => Ok(GlobRune::Rune(index + 1, r, false)),
    }
}

fn glob_normalize(mut ranges: Vec<(u32, u32)>) -> Vec<(u32, u32)> {
    ranges.sort_unstable();
    let mut out: Vec<(u32, u32)> = Vec::new();
    for (lo, hi) in ranges {
        match out.last_mut() {
            Some(last) if lo <= last.1.saturating_add(1) => last.1 = last.1.max(hi),
            _ => out.push((lo, hi)),
        }
    }
    out
}

/// Parses a set whose `[` is already consumed; returns the index after `]`.
fn glob_next_set(index: usize, input: &[char]) -> Result<(usize, GlobKind)> {
    let mut ranges: Vec<(u32, u32)> = Vec::new();
    let mut prev: Option<char> = None;
    let mut cur = index;
    loop {
        let (next, r, escaped) = match glob_next_rune(cur, input)? {
            GlobRune::End => {
                return Err(glob_error(input, cur, "found [ without matching ]"));
            }
            GlobRune::Rune(n, r, e) => (n, r, e),
        };
        cur = next;
        if escaped {
            ranges.push((u32::from(r), u32::from(r)));
            prev = Some(r);
            continue;
        }
        match r {
            '-' => {
                let Some(start) = prev else {
                    return Err(glob_error(
                        input,
                        cur,
                        "range character '-' must be preceded by a Unicode character",
                    ));
                };
                if cur + 1 >= input.len() {
                    return Err(glob_error(
                        input,
                        cur,
                        "range character '-' must be followed by a Unicode character",
                    ));
                }
                let (next, end, end_escaped) = match glob_next_rune(cur, input)? {
                    GlobRune::End => {
                        return Err(glob_error(input, cur, "found [ without matching ]"));
                    }
                    GlobRune::Rune(n, r, e) => (n, r, e),
                };
                cur = next;
                if !end_escaped && (end == ']' || end == '-') {
                    return Err(glob_error(
                        input,
                        cur,
                        "range character '-' cannot be followed by a special symbol",
                    ));
                }
                if end < start {
                    return Err(glob_error(
                        input,
                        cur,
                        &format!(
                            "range is out of order: '{end}' comes before '{start}' in Unicode"
                        ),
                    ));
                }
                ranges.push((u32::from(start), u32::from(end)));
                prev = None;
            }
            ']' => return Ok((cur, GlobKind::Set(glob_normalize(ranges)))),
            _ => {
                ranges.push((u32::from(r), u32::from(r)));
                prev = Some(r);
            }
        }
    }
}

fn parse_glob(input: &str) -> Result<Vec<GlobToken>> {
    let input: Vec<char> = input.chars().collect();
    let mut tokens: Vec<GlobToken> = Vec::new();
    let mut index = 0;
    loop {
        let (mut next, r, escaped) = match glob_next_rune(index, &input)? {
            GlobRune::End => break,
            GlobRune::Rune(n, r, e) => (n, r, e),
        };
        let kind = if escaped {
            GlobKind::Char(r)
        } else {
            match r {
                '.' => GlobKind::Dot,
                '[' => {
                    let (n, set) = glob_next_set(next, &input)?;
                    next = n;
                    set
                }
                ']' => {
                    return Err(glob_error(
                        &input,
                        next,
                        "set-close ']' with no preceding '['",
                    ))
                }
                '+' | '*' => {
                    return Err(glob_error(
                        &input,
                        next,
                        &format!("flag '{r}' must be preceded by a non-flag"),
                    ))
                }
                _ => GlobKind::Char(r),
            }
        };
        let mut flag = GlobFlag::None;
        if let GlobRune::Rune(n, f, false) = glob_next_rune(next, &input)? {
            match f {
                '+' => {
                    flag = GlobFlag::Plus;
                    next = n;
                }
                '*' => {
                    flag = GlobFlag::Star;
                    next = n;
                }
                _ => {}
            }
        }
        tokens.push(GlobToken { kind, flag });
        index = next;
    }
    if tokens.len() > GLOB_MAX_TOKENS {
        bail!("regex.globs_match: a glob may have at most {GLOB_MAX_TOKENS} tokens");
    }
    Ok(glob_simplify(tokens))
}

/// Merges adjacent equal tokens that both carry a flag, as the upstream
/// library does (`t+t*` and `t*t+` become `t+`, `t*t*` becomes `t*`).
fn glob_simplify(tokens: Vec<GlobToken>) -> Vec<GlobToken> {
    let mut simple: Vec<GlobToken> = Vec::new();
    for t in tokens {
        if let Some(latest) = simple.last_mut() {
            if t.flag != GlobFlag::None && latest.flag != GlobFlag::None && t.kind == latest.kind {
                latest.flag = if t.flag == GlobFlag::Plus || latest.flag == GlobFlag::Plus {
                    GlobFlag::Plus
                } else {
                    GlobFlag::Star
                };
                continue;
            }
        }
        simple.push(t);
    }
    simple
}

/// Removes matching unflagged prefixes and suffixes, keeping one token of
/// each so neither side becomes empty. `None` when a pair cannot match.
fn glob_trim<'a>(
    g1: &'a [GlobToken],
    g2: &'a [GlobToken],
) -> Option<(&'a [GlobToken], &'a [GlobToken])> {
    let plain = |t: &GlobToken| t.flag == GlobFlag::None;
    let mut l = 0;
    while let (Some(a), Some(b)) = (g1.get(l), g2.get(l)) {
        if !plain(a) || !plain(b) {
            break;
        }
        if !a.matches(b) {
            return None;
        }
        l += 1;
    }
    l = l.saturating_sub(1);

    // Signed indices: both can reach -1.
    let mut r1 = g1.len() as isize - 1;
    let mut r2 = g2.len() as isize - 1;
    let l_signed = l as isize;
    while r1 >= 0 && r1 >= l_signed && r2 >= 0 && r2 >= l_signed {
        let (Some(a), Some(b)) = (g1.get(r1 as usize), g2.get(r2 as usize)) else {
            break;
        };
        if !plain(a) || !plain(b) {
            break;
        }
        if !a.matches(b) {
            return None;
        }
        r1 -= 1;
        r2 -= 1;
    }
    if r1 < g1.len() as isize - 1 {
        r1 += 1;
        r2 += 1;
    }
    Some((g1.get(l..(r1 + 1) as usize)?, g2.get(l..(r2 + 1) as usize)?))
}

/// Longest glob (in tokens) `regex.globs_match` accepts. The intersection
/// search recurses roughly once per flagged token, so this also bounds the
/// stack depth.
const GLOB_MAX_TOKENS: usize = 256;

/// Work allowed for one `regex.globs_match` call. The search backtracks and
/// can take exponential time on adversarial globs, so it is cut off here.
const GLOB_STEP_LIMIT: usize = 1_000_000;

/// Work counter shared by the recursive intersection routines.
struct GlobBudget {
    steps: usize,
}

impl GlobBudget {
    fn tick(&mut self) -> Result<()> {
        self.steps = self.steps.saturating_add(1);
        if self.steps > GLOB_STEP_LIMIT {
            bail!("regex.globs_match: the globs are too complex to compare");
        }
        if self.steps & 1023 == 0 {
            enforce_limit()?;
        }
        Ok(())
    }
}

fn glob_intersect_normal(g1: &[GlobToken], g2: &[GlobToken], w: &mut GlobBudget) -> Result<bool> {
    w.tick()?;
    let (mut i, mut j) = (0, 0);
    while let (Some(a), Some(b)) = (g1.get(i), g2.get(j)) {
        if a.flag == GlobFlag::None && b.flag == GlobFlag::None {
            if !a.matches(b) {
                return Ok(false);
            }
        } else {
            return glob_intersect_special(
                g1.get(i..).unwrap_or(&[]),
                g2.get(j..).unwrap_or(&[]),
                w,
            );
        }
        i += 1;
        j += 1;
    }
    Ok(i == g1.len() && j == g2.len())
}

fn glob_intersect_special(g1: &[GlobToken], g2: &[GlobToken], w: &mut GlobBudget) -> Result<bool> {
    let (Some(a), Some(_)) = (g1.first(), g2.first()) else {
        return Ok(false);
    };
    let (flagged, other) = if a.flag != GlobFlag::None {
        (g1, g2)
    } else {
        (g2, g1)
    };
    match flagged.first().map(|t| t.flag) {
        Some(GlobFlag::Plus) => glob_intersect_plus(flagged, other, w),
        Some(GlobFlag::Star) => glob_intersect_star(flagged, other, w),
        _ => Ok(false),
    }
}

fn glob_intersect_plus(
    plussed: &[GlobToken],
    other: &[GlobToken],
    w: &mut GlobBudget,
) -> Result<bool> {
    w.tick()?;
    let (Some(p), Some(o)) = (plussed.first(), other.first()) else {
        return Ok(false);
    };
    if !p.matches(o) {
        return Ok(false);
    }
    // Either the plussed token gobbled up other[0]...
    if glob_intersect_star(plussed, other.get(1..).unwrap_or(&[]), w)? {
        return Ok(true);
    }
    // ...or other[0] has a flag and may completely gobble up plussed[0].
    if o.flag == GlobFlag::None {
        return Ok(false);
    }
    glob_intersect_normal(plussed.get(1..).unwrap_or(&[]), other, w)
}

fn glob_intersect_star(
    starred: &[GlobToken],
    other: &[GlobToken],
    w: &mut GlobBudget,
) -> Result<bool> {
    let Some(star) = starred.first() else {
        return Ok(false);
    };
    let next = starred.get(1);
    for (i, t) in other.iter().enumerate() {
        w.tick()?;
        match next {
            Some(n) if t.matches(n) => {
                if glob_intersect_normal(
                    starred.get(1..).unwrap_or(&[]),
                    other.get(i..).unwrap_or(&[]),
                    w,
                )? {
                    return Ok(true);
                }
                if !t.matches(star) {
                    return Ok(false);
                }
            }
            _ => {
                if !t.matches(star) {
                    return Ok(false);
                }
            }
        }
    }
    Ok(next.is_none())
}

fn globs_non_empty(g1: &[GlobToken], g2: &[GlobToken]) -> Result<bool> {
    match glob_trim(g1, g2) {
        Some((a, b)) => glob_intersect_normal(a, b, &mut GlobBudget { steps: 0 }),
        None => Ok(false),
    }
}

fn globs_match(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "regex.globs_match";
    ensure_args_count(span, name, params, args, 2)?;
    let glob1 = ensure_string(name, &params[0], &args[0])?;
    let glob2 = ensure_string(name, &params[1], &args[1])?;

    let parse = |param: &Ref<Expr>, glob: &str| {
        parse_glob(glob).map_err(|e| {
            if strict {
                anyhow::anyhow!(param.span().error(&e.to_string()))
            } else {
                e
            }
        })
    };
    let a = parse(&params[0], &glob1)?;
    let b = parse(&params[1], &glob2)?;
    Ok(Value::Bool(globs_non_empty(&a, &b)?))
}

fn find_all_string_submatch_n(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "regex.find_all_string_submatch_n";
    ensure_args_count(span, name, params, args, 3)?;

    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;
    let n = ensure_numeric(name, &params[2], &args[2])?;

    let re = compile_regex_for_builtin(params[0].span(), &pattern)?;

    if !n.is_integer() {
        bail!(params[2].span().error("n must be an integer"));
    }

    let n = match n.as_i64() {
        Some(n) if n < 0 => usize::MAX,
        Some(n) => n as usize,
        None => usize::MAX,
    };

    Ok(Value::from_array(
        re.captures_iter(&value)
            .map(|capture| {
                let groups = capture
                    .iter()
                    .map(|group| {
                        let value = Value::String(match group {
                            Some(s) => s.as_str().into(),
                            _ => "".into(),
                        });
                        // Guard match accumulation while adding each capture group.
                        enforce_limit()?;
                        Ok(value)
                    })
                    .collect::<Result<Vec<Value>>>()?;
                let array = Value::from_array(groups);
                // Guard outer match accumulation as nested arrays grow.
                enforce_limit()?;
                Ok(array)
            })
            .take(n)
            .collect::<Result<Vec<Value>>>()?,
    ))
}

fn find_n(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "regex.find_n";
    ensure_args_count(span, name, params, args, 3)?;

    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;
    let n = ensure_numeric(name, &params[2], &args[2])?;

    let re = compile_regex_for_builtin(params[0].span(), &pattern)?;

    if !n.is_integer() {
        bail!(params[2].span().error("n must be an integer"));
    }

    let n = match n.as_i64() {
        Some(n) if n < 0 => usize::MAX,
        Some(n) => n as usize,
        None => usize::MAX,
    };

    Ok(Value::from_array(
        re.find_iter(&value)
            .map(|m| {
                let value = Value::String(m.as_str().into());
                // Guard match accumulation while pushing each substring.
                enforce_limit()?;
                Ok(value)
            })
            .take(n)
            .collect::<Result<Vec<Value>>>()?,
    ))
}

fn is_valid(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "regex.is_valid";
    ensure_args_count(span, name, params, args, 1)?;
    let pattern = match ensure_string(name, &params[0], &args[0]) {
        Ok(p) => p,
        Err(_) => return Ok(Value::Bool(false)),
    };
    match get_or_compile_regex(&pattern) {
        Ok(_) => Ok(Value::Bool(true)),
        // Size-limit exceeded is a resource-limit violation; propagate as hard error.
        Err(regex::Error::CompiledTooBig(_)) => Err(anyhow::Error::new(
            crate::utils::limits::LimitError::RegexSizeLimitExceeded {
                limit: REGEX_SIZE_LIMIT,
            },
        )),
        // Syntax errors mean the pattern is genuinely invalid.
        Err(_) => Ok(Value::Bool(false)),
    }
}

pub fn regex_match(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "regex.match";
    ensure_args_count(span, name, params, args, 2)?;
    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;

    let re = compile_regex_for_builtin(params[0].span(), &pattern)?;
    Ok(Value::Bool(re.is_match(&value)))
}

fn regex_replace(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "regex.replace";
    ensure_args_count(span, name, params, args, 3)?;

    let s = ensure_string(name, &params[0], &args[0])?;
    let pattern = ensure_string(name, &params[1], &args[1])?;
    let value = ensure_string(name, &params[2], &args[2])?;

    let re = match get_or_compile_regex(&pattern) {
        Ok(p) => p,
        Err(regex::Error::CompiledTooBig(_)) => {
            return Err(anyhow::Error::new(
                crate::utils::limits::LimitError::RegexSizeLimitExceeded {
                    limit: REGEX_SIZE_LIMIT,
                },
            ));
        }
        // TODO: This behavior is due to OPA test not raising error. Should we raise error?
        _ => return Ok(Value::Undefined),
    };

    Ok(Value::String(re.replace_all(&s, value.as_ref()).into()))
}

fn regex_split(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "regex.split";
    ensure_args_count(span, name, params, args, 2)?;
    let pattern = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;

    let re = compile_regex_for_builtin(params[0].span(), &pattern)?;
    Ok(Value::from_array(
        re.split(&value)
            .map(|s| {
                let value = Value::String(s.into());
                // Guard output accumulation as each split segment is emitted.
                enforce_limit()?;
                Ok(value)
            })
            .collect::<Result<Vec<Value>>>()?,
    ))
}

fn regex_template_match(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "regex.template_match";
    ensure_args_count(span, name, params, args, 4)?;
    let template = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;
    let delimiter_start = ensure_string(name, &params[2], &args[2])?;
    let delimiter_end = ensure_string(name, &params[3], &args[3])?;

    let delimiter_start = delimiter_start.as_ref();
    let delimiter_end = delimiter_end.as_ref();
    let mut template = template.as_ref();
    let mut value = value.as_ref();

    while let (Some(start), Some(end)) =
        (template.find(delimiter_start), template.find(delimiter_end))
    {
        if start >= end {
            return Ok(Value::Undefined);
        }
        // Match precesing literal (if any)
        if value.get(..start) != Some(&template[..start]) {
            return Ok(Value::Bool(false));
        }

        // Fetch pattern, excluding delimiters.
        let Some(pattern) = template.get(start + delimiter_start.len()..end) else {
            return Ok(Value::Undefined);
        };
        let re = compile_regex_for_builtin(params[0].span(), pattern)?;

        // Skip preceding literal in value.
        value = &value[start..];

        let m = match re.find(value) {
            Some(m) if m.start() == 0 => m,
            _ => return Ok(Value::Bool(false)),
        };
        // Skip match in string.
        value = &value[m.len()..];

        // Skip regex and delimiter in template.
        template = &template[end + delimiter_end.len()..];
    }

    // Ensure that ending literal matches.
    Ok(Value::Bool(template == value))
}
