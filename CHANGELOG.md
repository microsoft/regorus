# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

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
