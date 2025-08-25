// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use regorus::{Engine, Value};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use serde::{Deserialize, Serialize};
use walkdir::WalkDir;

use std::path::Path;

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestCase {
    note: String,
    data: Value,
    input: Value,
    modules: Vec<String>,
    query: String,
    want_result: Value,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn aci_policy_eval(c: &mut Criterion) {
    let dir = Path::new("tests/aci");
    for entry in WalkDir::new(dir)
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path = entry.path();
        if !path.to_string_lossy().ends_with(".yaml") {
            continue;
        }

        let yaml = std::fs::read(path).expect("failed to read yaml test");
        let yaml = String::from_utf8_lossy(&yaml);
        let test: YamlTest = serde_yaml::from_str(&yaml).expect("failed to deserialize yaml test");

        for case in &test.cases {
            let rule = case.query.replace("=x", "");
            c.bench_with_input(
                BenchmarkId::new("case ", format!("{} {}", &case.note, &rule)),
                &case,
                |b, case| {
                    let mut engine = Engine::new();
                    engine.set_rego_v0(true);

                    engine
                        .add_data(case.data.clone())
                        .expect("failed to add data");
                    engine.set_input(case.input.clone());

                    for (idx, rego) in case.modules.iter().enumerate() {
                        if rego.ends_with(".rego") {
                            let path = dir.join(rego);
                            let path = path.to_str().expect("not a valid path");
                            engine
                                .add_policy_from_file(path)
                                .expect("failed to add policy");
                        } else {
                            engine
                                .add_policy(format!("rego{idx}.rego"), rego.clone())
                                .expect("failed to add policy");
                        }
                    }

                    b.iter(|| {
                        engine.eval_rule(rule.clone()).unwrap();
                    })
                },
            );
        }
    }
}

criterion_group!(aci_benches, aci_policy_eval);
criterion_main!(aci_benches);
