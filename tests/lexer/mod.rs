// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![cfg(test)]

use anyhow::{bail, Result};
use rego_rs::*;
use serde::{Deserialize, Serialize};
use std::env;
use test_generator::test_resources;
//use walkdir::WalkDir;

fn get_tokens<'source>(source: &'source Source<'source>) -> Result<Vec<Token<'source>>> {
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
            _ => bail!("could not find caret for {tok:#?} {msg}"),
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

#[test]
#[ignore = "intended for use by scripts/lex-file"]
fn one_file() -> Result<()> {
    let mut file = String::default();
    let mut verbose = false;
    for a in env::args() {
        if a.ends_with(".rego") {
            file = a.clone();
        }
        if matches!(a.as_str(), "verbose") {
            verbose = true;
        }
    }

    if file.is_empty() {
        bail!("missing <policy.rego>")
    }

    let contents = std::fs::read_to_string(&file)?;

    let source = Source {
        file: file.as_str(),
        contents: contents.as_str(),
        lines: contents.split('\n').collect(),
    };

    for tok in &get_tokens(&source)? {
        if tok.0 == TokenKind::Eof {
            break;
        }
        check_loc(tok)?;
        if verbose {
            println!("{}", tok.1.source.message(tok.1.line, tok.1.col, "", ""));
        }
        println!("{:?}", tok);
    }

    Ok(())
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
    println!("\nrunning {}", file);

    let yaml = std::fs::read_to_string(file)?;
    let test: Test = serde_yaml::from_str(&yaml)?;

    for case in &test.cases {
        let source = Source {
            file: "case.rego",
            contents: case.rego.as_str(),
            lines: case.rego.as_str().split('\n').collect(),
        };

        print!("case {} ", &case.note);

        match get_tokens(&source) {
            Ok(tokens) => {
                for (idx, tok) in tokens.iter().enumerate() {
                    if idx >= case.tokens.len() {
                        break;
                    }
                    assert_eq!(
                        tok.1.text(),
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
                    "\n. Token count mismatch.\nLexed tokens:{:?}",
                    tokens
                );
                if let Some(k) = &case.kinds {
                    assert_eq!(
                        tokens.len(),
                        k.len(),
                        "\n. Kind count mismatch.\nLexed tokens:{:?}",
                        tokens
                    );
                }
            }
            Err(actual) => match &case.error {
                Some(expected) => {
                    let actual = actual.to_string();
                    if !actual.contains(expected) {
                        bail!(
                            "Error message\n`{}\n`\ndoes not contain `{}`",
                            actual,
                            expected
                        );
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

#[test]
#[ignore = "intended for use by scripts/yaml-test-lex"]
fn one_yaml() -> Result<()> {
    let mut file = String::default();
    for a in env::args() {
        if a.ends_with(".yaml") {
            file = a;
            break;
        }
    }

    if file.is_empty() {
        bail!("missing yaml test file");
    }

    yaml_test(file.as_str())
}

/*
fn run_yaml_tests_in(folder: &str) -> Result<()> {
    let mut total = 0;

    for entry in WalkDir::new(folder)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path = entry
            .path()
            .to_str()
            .ok_or_else(|| anyhow!("failed to convert path to utf8 {:?}", entry.path()))?;
        if !path.ends_with(".yaml") {
            continue;
        }

        total += 1;
        yaml_test(path)?;
    }

    println!("{} lexer yaml tests passed.", total);
    Ok(())
}

#[test]
fn lexer_yaml_tests() -> Result<()> {
    run_yaml_tests_in("tests/lexer")
}*/

#[test_resources("tests/lexer/**/*.yaml")]
fn run(path: &str) {
    yaml_test(path).unwrap()
}

#[test]
fn debug() -> Result<()> {
    let rego = "\"This string is 35 characters long.\"\"short string\"";
    let source = Source {
        file: "case.rego",
        contents: rego,
        lines: rego.split('\n').collect(),
    };

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
    let source = Source {
        file: "case.rego",
        contents: rego,
        lines: rego.split('\n').collect(),
    };

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
    let source = Source {
        file: "case.rego",
        contents: rego,
        lines: rego.split('\n').collect(),
    };

    assert_eq!(
        source.message(2, 0, "", ""),
        "case.rego: invalid line 2 specified"
    );

    Ok(())
}
