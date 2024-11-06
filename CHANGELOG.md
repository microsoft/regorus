# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.8](https://github.com/microsoft/regorus/compare/regorus-v0.2.7...regorus-v0.2.8) - 2024-11-06

### Other
- *(deps)* update jsonschema requirement from 0.24.0 to 0.26.1 ([#343](https://github.com/microsoft/regorus/pull/343))
- Update to OPA v0.70.0 ([#341](https://github.com/microsoft/regorus/pull/341))

## [0.2.7](https://github.com/microsoft/regorus/compare/regorus-v0.2.6...regorus-v0.2.7) - 2024-10-22

### Fixed
- docs failing to build ([#334](https://github.com/microsoft/regorus/pull/334))

### Other
- *(deps)* update jsonschema requirement from 0.23.0 to 0.24.0 ([#332](https://github.com/microsoft/regorus/pull/332))
- *(deps)* update jsonschema requirement from 0.22.3 to 0.23.0 ([#331](https://github.com/microsoft/regorus/pull/331))

## [0.2.6](https://github.com/microsoft/regorus/compare/regorus-v0.2.5...regorus-v0.2.6) - 2024-10-09

### Added
- integer conversion functions for Value ([#328](https://github.com/microsoft/regorus/pull/328))

### Other
- update to OPA v0.69.0 ([#327](https://github.com/microsoft/regorus/pull/327))
- *(deps)* update jsonschema requirement from 0.21.0 to 0.22.3 ([#326](https://github.com/microsoft/regorus/pull/326))
- *(deps)* update jsonschema requirement from 0.20.0 to 0.21.0 ([#325](https://github.com/microsoft/regorus/pull/325))
- update to jsonschema 0.20.0 ([#323](https://github.com/microsoft/regorus/pull/323))

## [0.2.5](https://github.com/microsoft/regorus/compare/regorus-v0.2.4...regorus-v0.2.5) - 2024-09-18

### Added
- or keyword ([#315](https://github.com/microsoft/regorus/pull/315))

### Fixed
- Null terminate C# strings in Rust boundary ([#318](https://github.com/microsoft/regorus/pull/318))
- Update readme with correct path to example policy ([#312](https://github.com/microsoft/regorus/pull/312))

### Other
- Update jsonschema requirement from 0.18.0 to 0.19.1 ([#317](https://github.com/microsoft/regorus/pull/317))
- Update chrono-tz requirement from 0.8.5 to 0.10.0 ([#316](https://github.com/microsoft/regorus/pull/316))
- Add tests for builtin strings::lower method ([#313](https://github.com/microsoft/regorus/pull/313))
- Add tests for builtin strings::indexof method ([#311](https://github.com/microsoft/regorus/pull/311))

## [0.2.4](https://github.com/microsoft/regorus/compare/regorus-v0.2.3...regorus-v0.2.4) - 2024-09-04

### Added
- OPA v0.68.0. Engine::set_rego_v1 ([#305](https://github.com/microsoft/regorus/pull/305))

### Fixed
- Handle parsing corner cases ([#309](https://github.com/microsoft/regorus/pull/309))
- Propagate errors encountered in argument evaluation ([#308](https://github.com/microsoft/regorus/pull/308))
- Issues [#302](https://github.com/microsoft/regorus/pull/302), [#303](https://github.com/microsoft/regorus/pull/303) ([#304](https://github.com/microsoft/regorus/pull/304))

## [0.2.3](https://github.com/microsoft/regorus/compare/regorus-v0.2.2...regorus-v0.2.3) - 2024-08-16

### Fixed
- Match OPA behavior for split ([#295](https://github.com/microsoft/regorus/pull/295))
- Merge data to init document ([#293](https://github.com/microsoft/regorus/pull/293))

### Other
- Update cbindgen requirement from 0.26.0 to 0.27.0 ([#296](https://github.com/microsoft/regorus/pull/296))
- Bump rexml in /bindings/ruby in the bundler group across 1 directory ([#294](https://github.com/microsoft/regorus/pull/294))
- Update csbindgen requirement from =1.9.0 to =1.9.3 ([#292](https://github.com/microsoft/regorus/pull/292))

## [0.2.2](https://github.com/microsoft/regorus/compare/regorus-v0.2.1...regorus-v0.2.2) - 2024-07-28

### Added
- Update to opa v0.67.0 ([#286](https://github.com/microsoft/regorus/pull/286))

### Fixed
- Handle aliases in scheduler ([#285](https://github.com/microsoft/regorus/pull/285))

### Other
- Update readme ([#288](https://github.com/microsoft/regorus/pull/288))
- Update binding versions ([#287](https://github.com/microsoft/regorus/pull/287))
- build.rs create hooks dir if not exists ([#283](https://github.com/microsoft/regorus/pull/283))
- add extension_list example ([#281](https://github.com/microsoft/regorus/pull/281))
- Fix build break ([#278](https://github.com/microsoft/regorus/pull/278))
- Update pyo3 requirement from 0.21.0 to 0.22.0 ([#275](https://github.com/microsoft/regorus/pull/275))
- Update to OPA v0.66.0 ([#274](https://github.com/microsoft/regorus/pull/274))

## [0.2.1](https://github.com/microsoft/regorus/compare/regorus-v0.2.0...regorus-v0.2.1) - 2024-06-19

### Added
- get_policies: Way to obtain policy files and content ([#267](https://github.com/microsoft/regorus/pull/267))

### Other
- Fix c,cpp,no-std binding examples ([#272](https://github.com/microsoft/regorus/pull/272))
- Update binding versions for next release ([#270](https://github.com/microsoft/regorus/pull/270))
- rename method from 'Clone' to 'clone' in 'Engine' class to match the java naming convention and definiont in the of java.lang.Object. ([#268](https://github.com/microsoft/regorus/pull/268))
- Suppress clippy unused warning ([#269](https://github.com/microsoft/regorus/pull/269))
- Provide ability to get JSON representation of policy AST ([#266](https://github.com/microsoft/regorus/pull/266))
- Update OPA tests to v0.65.0 ([#264](https://github.com/microsoft/regorus/pull/264))
- Allow lexer to be used for other policy languages ([#262](https://github.com/microsoft/regorus/pull/262))

## [0.2.0](https://github.com/microsoft/regorus/compare/regorus-v0.1.5...regorus-v0.2.0) - 2024-05-30

### Other
- Add release-plz config to publish only regorus package ([#259](https://github.com/microsoft/regorus/pull/259))
- Revert "chore: release v0.2.0 ([#257](https://github.com/microsoft/regorus/pull/257))" ([#258](https://github.com/microsoft/regorus/pull/258))
- release v0.2.0 ([#257](https://github.com/microsoft/regorus/pull/257))
- Fix release-plz hash ([#256](https://github.com/microsoft/regorus/pull/256))
- non collections should evaluate to false ([#253](https://github.com/microsoft/regorus/pull/253))
- Fix merge issue ([#252](https://github.com/microsoft/regorus/pull/252))
- Update bindings to include newer APIs ([#250](https://github.com/microsoft/regorus/pull/250))
- update ruby bindings version to 0.1.5, bump deps ([#251](https://github.com/microsoft/regorus/pull/251))
- Use correct docsrs feature annotation ([#248](https://github.com/microsoft/regorus/pull/248))
- Lockdown kata test prints as well as prints of various values ([#249](https://github.com/microsoft/regorus/pull/249))
- Fix bindings and add CI tests ([#247](https://github.com/microsoft/regorus/pull/247))
- Add test-ruby CI for github actions ([#244](https://github.com/microsoft/regorus/pull/244))
- Update `README.md` for Java bindings to mention we don't publish to ([#246](https://github.com/microsoft/regorus/pull/246))
- Update itertools requirement from 0.12.1 to 0.13.0 ([#245](https://github.com/microsoft/regorus/pull/245))
- Update ruby bindings for add_policy and add_policy_from_file to return package name ([#240](https://github.com/microsoft/regorus/pull/240))
- Provide a way to obtain package names of loaded policies ([#239](https://github.com/microsoft/regorus/pull/239))
- `c_no_std` binding to show use in C freestanding environments. ([#238](https://github.com/microsoft/regorus/pull/238))
- Bump rexml in /bindings/ruby in the bundler group across 1 directory ([#236](https://github.com/microsoft/regorus/pull/236))
- Update prettydiff requirement from 0.6.4 to 0.7.0 ([#234](https://github.com/microsoft/regorus/pull/234))
- Update jsonschema requirement from 0.17.1 to 0.18.0 ([#235](https://github.com/microsoft/regorus/pull/235))
- no_std support ([#232](https://github.com/microsoft/regorus/pull/232))
- add `std` feature ([#231](https://github.com/microsoft/regorus/pull/231))
- Tests from MSFT fork of kata-containers ([#230](https://github.com/microsoft/regorus/pull/230))
- Use alloc, core instead of std ([#225](https://github.com/microsoft/regorus/pull/225))

## [0.1.5](https://github.com/microsoft/regorus/compare/regorus-v0.1.4...regorus-v0.1.5) - 2024-05-07

### Added
- Support policy files greater than 64KB in size ([#217](https://github.com/microsoft/regorus/pull/217))
- Add tests for kata containers policies ([#221](https://github.com/microsoft/regorus/pull/221))
- Support for OPA v0.64.0 ([#219](https://github.com/microsoft/regorus/pull/219))
  - New builtin `json.marshal_with_options`
### Changed
- Improve example in readme ([#224](https://github.com/microsoft/regorus/pull/224))
### Fixed
- OPA Conformance: Do not interpret # within regular string ([#216](https://github.com/microsoft/regorus/pull/216))

## [0.1.4](https://github.com/microsoft/regorus/compare/regorus-v0.1.3...regorus-v0.1.4) - 2024-04-22

### Other
- early return ([#189](https://github.com/microsoft/regorus/pull/189))
- Fix anyhow dependency issues ([#208](https://github.com/microsoft/regorus/pull/208))
- remove unused compact-rc dependency ([#207](https://github.com/microsoft/regorus/pull/207))

## [0.1.3](https://github.com/microsoft/regorus/compare/regorus-v0.1.2...regorus-v0.1.3) - 2024-04-11

### Other
- Add a note in example to prefer eval_rule over eval_query ([#204](https://github.com/microsoft/regorus/pull/204))
- Do not enable serde_json/arbitrary_precision by default ([#203](https://github.com/microsoft/regorus/pull/203))
- Rewrite so that code compiles with chrono_tz 0.8.5 and 0.9.0 ([#201](https://github.com/microsoft/regorus/pull/201))
- update ruby bindings ([#200](https://github.com/microsoft/regorus/pull/200))
- Store Value instances in AST for strings, numbers and idents ([#197](https://github.com/microsoft/regorus/pull/197))
- :Value> and From<serde_yaml::Value> ([#196](https://github.com/microsoft/regorus/pull/196))
- Build dependency on git only if opa.runtime feature is enabled. ([#194](https://github.com/microsoft/regorus/pull/194))
- Update to opa v0.63.0 ([#192](https://github.com/microsoft/regorus/pull/192))
- Update pyo3 requirement from 0.20.2 to 0.21.0 ([#190](https://github.com/microsoft/regorus/pull/190))
- Ruby bindings for existing FFI methods, plus eval_rule() ([#188](https://github.com/microsoft/regorus/pull/188))
- Evaluate rules directly instead of queries ([#186](https://github.com/microsoft/regorus/pull/186))
- Remove cruft. ([#184](https://github.com/microsoft/regorus/pull/184))

## [0.1.2](https://github.com/microsoft/regorus/compare/regorus-v0.1.1...regorus-v0.1.2) - 2024-03-22

### Other
- Handle non simple refs in chained expressions ([#182](https://github.com/microsoft/regorus/pull/182))
- Ability to gather print statements ([#179](https://github.com/microsoft/regorus/pull/179))
- Top-down evaluation ([#177](https://github.com/microsoft/regorus/pull/177))
- Make unary `-` operator OPA compatible. ([#175](https://github.com/microsoft/regorus/pull/175))
- Don't use deprecated chrono `Duration` methods ([#173](https://github.com/microsoft/regorus/pull/173))
- Propagate Undefined in object expressions ([#171](https://github.com/microsoft/regorus/pull/171))
- Bump to OPA v0.62.0 ([#169](https://github.com/microsoft/regorus/pull/169))
- Fix regression ([#164](https://github.com/microsoft/regorus/pull/164))
- Separately keep track of whether rules have been evaluated or not ([#163](https://github.com/microsoft/regorus/pull/163))
- Link Linux libraries against glibc 2.17 using `cargo-zigbuild` ([#158](https://github.com/microsoft/regorus/pull/158))

## [0.1.1](https://github.com/microsoft/regorus/compare/regorus-v0.1.0...regorus-v0.1.1) - 2024-02-23

### Other
- Handle else block without body ([#155](https://github.com/microsoft/regorus/pull/155))
- Ignore errors from builtin functions in non strict mode ([#154](https://github.com/microsoft/regorus/pull/154))
- Java publishing ([#151](https://github.com/microsoft/regorus/pull/151))
- Document coverage feature; Convenience query functions ([#152](https://github.com/microsoft/regorus/pull/152))
- Policy Coverage ([#149](https://github.com/microsoft/regorus/pull/149))
- Initial implementation of policy coverage ([#146](https://github.com/microsoft/regorus/pull/146))
- Java bindings ([#147](https://github.com/microsoft/regorus/pull/147))
- Preserve false in single-expression queries ([#145](https://github.com/microsoft/regorus/pull/145))
- Create rust-clippy.yml ([#143](https://github.com/microsoft/regorus/pull/143))
- `arc` feature to enable using Engine and other data structures from multiple threads ([#142](https://github.com/microsoft/regorus/pull/142))
- genpolicy tweaks ([#141](https://github.com/microsoft/regorus/pull/141))
- io.jwt.decode ([#140](https://github.com/microsoft/regorus/pull/140))
- Use compact_rc ([#139](https://github.com/microsoft/regorus/pull/139))
- Scripting tweaks ([#138](https://github.com/microsoft/regorus/pull/138))

## [0.1.0-alpha.3](https://github.com/microsoft/regorus/compare/regorus-v0.1.0-alpha.2...regorus-v0.1.0-alpha.3) - 2024-02-01

### Fixed
- fix bitwise.and and add tests ([#19](https://github.com/microsoft/regorus/pull/19))

### Other
- Document bindings ([#119](https://github.com/microsoft/regorus/pull/119))
- Conform to OPA 0.61.0. ([#118](https://github.com/microsoft/regorus/pull/118))
- Update publish-python.yml
- Publish python packages ([#117](https://github.com/microsoft/regorus/pull/117))
- Publish wasm ([#116](https://github.com/microsoft/regorus/pull/116))
- Set working-directory for wasm-pack
- Python bindings ([#115](https://github.com/microsoft/regorus/pull/115))
- WASM binding ([#114](https://github.com/microsoft/regorus/pull/114))
- release ([#112](https://github.com/microsoft/regorus/pull/112))
- Improve crate documentation ([#111](https://github.com/microsoft/regorus/pull/111))
- Try out manual trigger for release-plz ([#110](https://github.com/microsoft/regorus/pull/110))
- - Document Location, Expression, QueryResult ([#109](https://github.com/microsoft/regorus/pull/109))
- Update Cargo.toml ([#108](https://github.com/microsoft/regorus/pull/108))
- Change version to `0.1.0-alpha.1` ([#107](https://github.com/microsoft/regorus/pull/107))
- Add crate documentation ([#106](https://github.com/microsoft/regorus/pull/106))
- Release preparation ([#105](https://github.com/microsoft/regorus/pull/105))
- Update READEME.md with current status, grammar etc. ([#102](https://github.com/microsoft/regorus/pull/102))
- Implement builtin `time.parse_duration_ns` method ([#100](https://github.com/microsoft/regorus/pull/100))
- Implement import keyword ([#101](https://github.com/microsoft/regorus/pull/101))
- OPA conformance: Pass refheads test suite ([#90](https://github.com/microsoft/regorus/pull/90))
- OPA conformance: Ensure that `withkeyword` OPA tests pass ([#88](https://github.com/microsoft/regorus/pull/88))
- Handle walk builtin as a loop expression ([#86](https://github.com/microsoft/regorus/pull/86))
- Implement most of the builtin `time` module ([#82](https://github.com/microsoft/regorus/pull/82))
- OPA Conformance
- OPA conformance ([#81](https://github.com/microsoft/regorus/pull/81))
- More OPA conformance ([#77](https://github.com/microsoft/regorus/pull/77))
- OPA conformance ([#71](https://github.com/microsoft/regorus/pull/71))
- Builtin UUID module ([#68](https://github.com/microsoft/regorus/pull/68))
- Add tests for builtin `string::format_int` method ([#65](https://github.com/microsoft/regorus/pull/65))
- More builtins and semantic improvements ([#66](https://github.com/microsoft/regorus/pull/66))
- More OPA conformance; in-progress: ability to trace interpreter ([#63](https://github.com/microsoft/regorus/pull/63))
- More OPA conformant semantics ([#62](https://github.com/microsoft/regorus/pull/62))
- Updated readme. Added bundle support. ([#61](https://github.com/microsoft/regorus/pull/61))
- crypto builtins ([#57](https://github.com/microsoft/regorus/pull/57))
- Regex and Glob builtins ([#56](https://github.com/microsoft/regorus/pull/56))
- Formalize concept of a Number ([#55](https://github.com/microsoft/regorus/pull/55))
- Lock down ACI tests and more OPA test folders ([#54](https://github.com/microsoft/regorus/pull/54))
- Fix scheduling regression ([#53](https://github.com/microsoft/regorus/pull/53))
- add full api to engine ([#50](https://github.com/microsoft/regorus/pull/50))
- Use Rc<str> instead of string. ([#52](https://github.com/microsoft/regorus/pull/52))
- More library functions ([#51](https://github.com/microsoft/regorus/pull/51))
- Added semver.is_valid and semver.compare ([#49](https://github.com/microsoft/regorus/pull/49))
- OPA conformance tests ([#45](https://github.com/microsoft/regorus/pull/45))
- Avoid dependency on `source lifetime. ([#43](https://github.com/microsoft/regorus/pull/43))
- Allow with modifier for builtin and user functions ([#42](https://github.com/microsoft/regorus/pull/42))
- Special cases of refs to data ([#41](https://github.com/microsoft/regorus/pull/41))
- Fix scheduling statements that don't create bindings ([#40](https://github.com/microsoft/regorus/pull/40))
- Ability to run the OPA testsuite ([#39](https://github.com/microsoft/regorus/pull/39))
- Engine ([#38](https://github.com/microsoft/regorus/pull/38))
- Use Ref for storing ast nodes in collections. ([#37](https://github.com/microsoft/regorus/pull/37))
- all, any deprecated functions ([#35](https://github.com/microsoft/regorus/pull/35))
- all, any deprecated functions ([#34](https://github.com/microsoft/regorus/pull/34))
- Improvements ([#33](https://github.com/microsoft/regorus/pull/33))
- Order query expression results ([#32](https://github.com/microsoft/regorus/pull/32))
- Scheduling of statements in user queries ([#31](https://github.com/microsoft/regorus/pull/31))
- eval, lex, parse commands ([#30](https://github.com/microsoft/regorus/pull/30))
- eval_user_query for OPA style results ([#29](https://github.com/microsoft/regorus/pull/29))
- Arity for builtins ([#28](https://github.com/microsoft/regorus/pull/28))
- Handle chained _ ([#27](https://github.com/microsoft/regorus/pull/27))
- Minimize PR 22  ([#26](https://github.com/microsoft/regorus/pull/26))
- improve errors location ([#23](https://github.com/microsoft/regorus/pull/23))
- Fix clippy warning ([#25](https://github.com/microsoft/regorus/pull/25))
- negation of an undefined value should return true ([#21](https://github.com/microsoft/regorus/pull/21))
- Ensure that scopes are cleaned up correctly upon error. ([#20](https://github.com/microsoft/regorus/pull/20))
- support of or-functions ([#18](https://github.com/microsoft/regorus/pull/18))
- Statement Scheduler Implementation
- Remove unnecessary lifetime
- json.filter, object.filter, object.get, object.keys, object.remove
- :to_number builtin
- :trace builtin
- bitwise builtins
- :print builtin
- Partial sprintf implementation.
- All string functions except sprintf. TODO: Add tests
- More string functions without tests
- More string functions
- concat and contains
- string concat (WIP)
- Support build on non Linux platforms
- Prepare for upstreaming
- Test for multi-assign
- Support dependencies between vars defined in same statement
- Statement scheduler (WIP)
- Print small-form table of files without 100% coverage.
- Code tweaks to improve coverage
- Tests for aggregates builtins
- Tests for numbers builtins
- Tests for arrays builtins
- Tests for types functions
- Destructuring of arrays and objects in some-in expressions
- `some .. in` implementation
- Fix key, value in membership and some-in
- refactor
- Arrays and Aggregates
- Implement `every` statement ([#4](https://github.com/microsoft/regorus/pull/4))
- Set loop index variable if not "_" ([#3](https://github.com/microsoft/regorus/pull/3))
- Allow comprehensions in default value. ([#2](https://github.com/microsoft/regorus/pull/2))
- Lock down numbers
- mod function
- Builtin functions for numbers (WIP)
- Implement comparison operators. Formalize semantics.
- Rework assign operations ([#6](https://github.com/microsoft/regorus/pull/6))
- Locked down supported values in default rule.
- Improvements to github workflow ([#4](https://github.com/microsoft/regorus/pull/4))
- Update name to regorus
- Update rust.yml
- Add simple git action
- Add missing config.toml
- Update license to MIT
- Code from github.com/anakrish/rego-rs
- SUPPORT.md committed
- SECURITY.md committed
- README.md committed
- LICENSE committed
- CODE_OF_CONDUCT.md committed
- Initial commit

## [0.1.0-alpha.2](https://github.com/microsoft/regorus/compare/v0.1.0-alpha.1...v0.1.0-alpha.2) - 2024-01-19

### Other
- Improve crate documentation ([#111](https://github.com/microsoft/regorus/pull/111))
- Try out manual trigger for release-plz ([#110](https://github.com/microsoft/regorus/pull/110))
- - Document Location, Expression, QueryResult ([#109](https://github.com/microsoft/regorus/pull/109))

## [0.1.0-alpha.1](https://github.com/microsoft/regorus/releases/tag/v0.1.0-alpha.1) - 2024-01-15

### Fixed
- fix bitwise.and and add tests ([#19](https://github.com/microsoft/regorus/pull/19))

### Other
- Change version to `0.1.0-alpha.1`
- Add crate documentation ([#106](https://github.com/microsoft/regorus/pull/106))
- Release preparation ([#105](https://github.com/microsoft/regorus/pull/105))
- Update READEME.md with current status, grammar etc. ([#102](https://github.com/microsoft/regorus/pull/102))
- Implement builtin `time.parse_duration_ns` method ([#100](https://github.com/microsoft/regorus/pull/100))
- Implement import keyword ([#101](https://github.com/microsoft/regorus/pull/101))
- OPA conformance: Pass refheads test suite ([#90](https://github.com/microsoft/regorus/pull/90))
- OPA conformance: Ensure that `withkeyword` OPA tests pass ([#88](https://github.com/microsoft/regorus/pull/88))
- Handle walk builtin as a loop expression ([#86](https://github.com/microsoft/regorus/pull/86))
- Implement most of the builtin `time` module ([#82](https://github.com/microsoft/regorus/pull/82))
- OPA Conformance
- OPA conformance ([#81](https://github.com/microsoft/regorus/pull/81))
- More OPA conformance ([#77](https://github.com/microsoft/regorus/pull/77))
- OPA conformance ([#71](https://github.com/microsoft/regorus/pull/71))
- Builtin UUID module ([#68](https://github.com/microsoft/regorus/pull/68))
- Add tests for builtin `string::format_int` method ([#65](https://github.com/microsoft/regorus/pull/65))
- More builtins and semantic improvements ([#66](https://github.com/microsoft/regorus/pull/66))
- More OPA conformance; in-progress: ability to trace interpreter ([#63](https://github.com/microsoft/regorus/pull/63))
- More OPA conformant semantics ([#62](https://github.com/microsoft/regorus/pull/62))
- Updated readme. Added bundle support. ([#61](https://github.com/microsoft/regorus/pull/61))
- crypto builtins ([#57](https://github.com/microsoft/regorus/pull/57))
- Regex and Glob builtins ([#56](https://github.com/microsoft/regorus/pull/56))
- Formalize concept of a Number ([#55](https://github.com/microsoft/regorus/pull/55))
- Lock down ACI tests and more OPA test folders ([#54](https://github.com/microsoft/regorus/pull/54))
- Fix scheduling regression ([#53](https://github.com/microsoft/regorus/pull/53))
- add full api to engine ([#50](https://github.com/microsoft/regorus/pull/50))
- Use Rc<str> instead of string. ([#52](https://github.com/microsoft/regorus/pull/52))
- More library functions ([#51](https://github.com/microsoft/regorus/pull/51))
- Added semver.is_valid and semver.compare ([#49](https://github.com/microsoft/regorus/pull/49))
- OPA conformance tests ([#45](https://github.com/microsoft/regorus/pull/45))
- Avoid dependency on `source lifetime. ([#43](https://github.com/microsoft/regorus/pull/43))
- Allow with modifier for builtin and user functions ([#42](https://github.com/microsoft/regorus/pull/42))
- Special cases of refs to data ([#41](https://github.com/microsoft/regorus/pull/41))
- Fix scheduling statements that don't create bindings ([#40](https://github.com/microsoft/regorus/pull/40))
- Ability to run the OPA testsuite ([#39](https://github.com/microsoft/regorus/pull/39))
- Engine ([#38](https://github.com/microsoft/regorus/pull/38))
- Use Ref for storing ast nodes in collections. ([#37](https://github.com/microsoft/regorus/pull/37))
- all, any deprecated functions ([#35](https://github.com/microsoft/regorus/pull/35))
- all, any deprecated functions ([#34](https://github.com/microsoft/regorus/pull/34))
- Improvements ([#33](https://github.com/microsoft/regorus/pull/33))
- Order query expression results ([#32](https://github.com/microsoft/regorus/pull/32))
- Scheduling of statements in user queries ([#31](https://github.com/microsoft/regorus/pull/31))
- eval, lex, parse commands ([#30](https://github.com/microsoft/regorus/pull/30))
- eval_user_query for OPA style results ([#29](https://github.com/microsoft/regorus/pull/29))
- Arity for builtins ([#28](https://github.com/microsoft/regorus/pull/28))
- Handle chained _ ([#27](https://github.com/microsoft/regorus/pull/27))
- Minimize PR 22  ([#26](https://github.com/microsoft/regorus/pull/26))
- improve errors location ([#23](https://github.com/microsoft/regorus/pull/23))
- Fix clippy warning ([#25](https://github.com/microsoft/regorus/pull/25))
- negation of an undefined value should return true ([#21](https://github.com/microsoft/regorus/pull/21))
- Ensure that scopes are cleaned up correctly upon error. ([#20](https://github.com/microsoft/regorus/pull/20))
- support of or-functions ([#18](https://github.com/microsoft/regorus/pull/18))
- Statement Scheduler Implementation
- Remove unnecessary lifetime
- json.filter, object.filter, object.get, object.keys, object.remove
- :to_number builtin
- :trace builtin
- bitwise builtins
- :print builtin
- Partial sprintf implementation.
- All string functions except sprintf. TODO: Add tests
- More string functions without tests
- More string functions
- concat and contains
- string concat (WIP)
- Support build on non Linux platforms
- Prepare for upstreaming
- Test for multi-assign
- Support dependencies between vars defined in same statement
- Statement scheduler (WIP)
- Print small-form table of files without 100% coverage.
- Code tweaks to improve coverage
- Tests for aggregates builtins
- Tests for numbers builtins
- Tests for arrays builtins
- Tests for types functions
- Destructuring of arrays and objects in some-in expressions
- `some .. in` implementation
- Fix key, value in membership and some-in
- refactor
- Arrays and Aggregates
- Implement `every` statement ([#4](https://github.com/microsoft/regorus/pull/4))
- Set loop index variable if not "_" ([#3](https://github.com/microsoft/regorus/pull/3))
- Allow comprehensions in default value. ([#2](https://github.com/microsoft/regorus/pull/2))
- Lock down numbers
- mod function
- Builtin functions for numbers (WIP)
- Implement comparison operators. Formalize semantics.
- Rework assign operations ([#6](https://github.com/microsoft/regorus/pull/6))
- Locked down supported values in default rule.
- Improvements to github workflow ([#4](https://github.com/microsoft/regorus/pull/4))
- Update name to regorus
- Update rust.yml
- Add simple git action
- Add missing config.toml
- Update license to MIT
- Code from github.com/anakrish/rego-rs
- SUPPORT.md committed
- SECURITY.md committed
- README.md committed
- LICENSE committed
- CODE_OF_CONDUCT.md committed
- Initial commit

