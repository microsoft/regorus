// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{bail, Result};
use regorus::unstable::*;
use serde::{Deserialize, Serialize};
use test_generator::test_resources;

fn get_tokens(source: &Source) -> Result<Vec<Token>> {
    let mut tokens = vec![];
    let mut lex = Lexer::new(source);
    loop {
        let tok = lex.next_token()?;
        tokens.push(tok.clone());
        if tok.0 == TokenKind::Eof {
            break;
        }
    }

    Ok(tokens)
}

fn check_loc(tok: &Token) -> Result<()> {
    let msg = tok.1.source.message(tok.1.line, tok.1.col, "", "");
    let lines: Vec<&str> = msg.split('\n').collect();
    let source_line = lines[3];
    let caret_line = lines[4];
    let mut idx = 0usize;
    let mut source_idx = idx;
    loop {
        match source_idx < source_line.len() && idx < caret_line.len() {
            true => (),
            // Handle Eof
            false if tok.0 == TokenKind::Eof && source_idx >= source_line.len() => return Ok(()),
            // Handle case where a raw string's first char is a newline.
            false if tok.0 == TokenKind::RawString && &tok.1.text()[0..1] == "\n" => return Ok(()),
            _ => {
                bail!("could not find caret for {tok:#?} {msg}");
            }
        }
        match &caret_line[idx..idx + 1] {
            "^" => {
                let span_str = tok.1.text();
                let span_str = span_str.split('\n').collect::<Vec<&str>>()[0];
                let source_str = &source_line[source_idx..];
                assert!(
                    source_str.starts_with(span_str) || span_str.starts_with(source_str),
                    "location mismatch for {tok:#?} {msg}\n{span_str}\n{source_str}"
                );
                return Ok(());
            }
            _ if &source_line[source_idx..source_idx + 1] == "\t" => idx += 4,
            _ => idx += 1,
        }
        source_idx += 1;
    }
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct Case {
    pub rego: String,
    pub note: String,
    pub tokens: Vec<String>,
    pub kinds: Option<Vec<String>>,
    pub error: Option<String>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct Test {
    cases: Vec<Case>,
}

fn yaml_test_impl(file: &str) -> Result<()> {
    println!("\nrunning {file}");

    let yaml = std::fs::read_to_string(file)?;
    let test: Test = serde_yaml::from_str(&yaml)?;

    for case in &test.cases {
        let source = Source::from_contents("case.rego".to_string(), case.rego.clone())?;
        print!("case {} ", &case.note);

        match get_tokens(&source) {
            Ok(tokens) => {
                for (idx, tok) in tokens.iter().enumerate() {
                    if idx >= case.tokens.len() {
                        break;
                    }
                    assert_eq!(
                        *tok.1.text(),
                        case.tokens[idx],
                        "{} Expected token `{}` not found",
                        source.message(tok.1.line, tok.1.col, "mismatch-error", &case.tokens[idx]),
                        &case.tokens[idx]
                    );

                    if let Some(k) = &case.kinds {
                        if idx >= k.len() {
                            break;
                        }
                        assert_eq!(
                            format!("{:?}", tok.0),
                            k[idx],
                            "{}",
                            source.message(
                                tok.1.line,
                                tok.1.col,
                                "mismatch-error",
                                "token kind mismatch"
                            )
                        );
                    }

                    check_loc(tok)?;
                }
                assert_eq!(
                    tokens.len(),
                    case.tokens.len(),
                    "\n. Token count mismatch.\nLexed tokens:{tokens:?}"
                );
                if let Some(k) = &case.kinds {
                    assert_eq!(
                        tokens.len(),
                        k.len(),
                        "\n. Kind count mismatch.\nLexed tokens:{tokens:?}"
                    );
                }
            }
            Err(actual) => match &case.error {
                Some(expected) => {
                    let actual = actual.to_string();
                    if !actual.contains(expected) {
                        bail!("Error message\n`{actual}\n`\ndoes not contain `{expected}`");
                    }
                }
                _ => return Err(actual),
            },
        }

        println!("passed");
    }
    println!("{} cases passed.", test.cases.len());
    Ok(())
}

fn yaml_test(file: &str) -> Result<()> {
    match yaml_test_impl(file) {
        Ok(_) => Ok(()),
        Err(e) => {
            // If Err is returned, it doesn't always get printed by cargo test.
            // Therefore, panic with the error.
            panic!("{}", e);
        }
    }
}

#[test_resources("tests/lexer/**/*.yaml")]
fn run(path: &str) {
    yaml_test(path).unwrap()
}

#[test]
fn debug() -> Result<()> {
    let rego = "\"This string is 35 characters long.\"\"short string\"";
    let source = Source::from_contents("case.rego".to_string(), rego.to_string())?;

    let mut lexer = Lexer::new(&source);
    let tok = lexer.next_token()?;
    check_loc(&tok)?;

    assert_eq!(
        format!("{:?}", tok.1),
        "1:2:1:35, \"This string is 35 characters lon...\"",
        "long span not truncated correctly"
    );

    let tok = lexer.next_token()?;
    check_loc(&tok)?;
    assert_eq!(format!("{:?}", tok.1), "1:38:37:49, \"short string\"");

    Ok(())
}

#[test]
fn tab() -> Result<()> {
    let rego = r#"	"This string is 35 characters long."`raw	string`p"#;
    let source = Source::from_contents("case.rego".to_string(), rego.to_string())?;

    let mut lexer = Lexer::new(&source);

    // read first tab and string.
    let tok = lexer.next_token()?;
    check_loc(&tok)?;
    assert_eq!(tok.1.col, 6, "tab not accounted correctly.");

    // read raw string which contains tab.
    let tok = lexer.next_token()?;
    check_loc(&tok)?;
    assert_eq!(tok.1.col, 42, "raw string not positioned correctly");

    // read next token (ident)
    let tok = lexer.next_token()?;
    check_loc(&tok)?;
    println!("{:?}", &tok);
    println!("{}", source.message(tok.1.line, tok.1.col, "", ""));
    assert_eq!(
        tok.1.col, 56,
        "tab within rawstring not accounted correctly"
    );

    Ok(())
}

#[test]
fn invalid_line() -> Result<()> {
    let rego = "";
    let source = Source::from_contents("case.rego".to_string(), rego.to_string())?;

    assert_eq!(
        source.message(2, 0, "", ""),
        "case.rego: invalid line 2 specified"
    );

    Ok(())
}

#[test]
fn file_more_than_64_kb_size() -> Result<()> {
    let source = Source::from_file("tests/kata/data/large.rego")?;
    let mut lexer = Lexer::new(&source);

    let mut count = 0;
    // Read tokens until EOF.
    loop {
        let token = lexer.next_token()?;
        count += 1;
        if token.0 == TokenKind::Eof {
            break;
        }
    }
    assert_eq!(count, 8789);
    Ok(())
}
