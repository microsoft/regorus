# Built-in Functions


This page lists all the supported Rego built-in functions and the cargo feature that is needed to enable each builtin.

Those builtins that are not need for a specific use of the Regorus crate can be excluded from the binary by not specifying
the corresponding feature. This is useful in Confidential Computing scenarios where
  - There needs to be control over what a policy execution can and cannot do.
  - There needs to be control over exactly what goes into the [Trusted Computing Base](https://en.wikipedia.org/wiki/Trusted_computing_base).

Currently many builtins are `baked-in`, i.e. there is no way to exclude them from the TCB.
In future, each builtin will be associated with a feature (many builtins could be associated with the same feature).

- [Comparison](https://www.openpolicyagent.org/docs/latest/policy-reference/#comparison)
  | Builtin                                                                                          | Feature |
  |--------------------------------------------------------------------------------------------------|---------|
  | [x == y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-comparison-equal) | _       |
  | [x > y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-comparison-gt)     | _       |
  | [x >= y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-comparison-gte)   | _       |
  | [x < y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-comparison-lt)     | _       |
  | [x <= y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-comparison-lte)   | _       |
  | [x != y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-comparison-neq)   | _       |

- [Numbers](https://www.openpolicyagent.org/docs/latest/policy-reference/#numbers)
  | Builtin                                                                                                               | Feature |
  |-----------------------------------------------------------------------------------------------------------------------|---------|
  | [abs](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-abs)                              | _       |
  | [ceil](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-ceil)                            | _       |
  | [x / y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-div)                            | _       |
  | [floor](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-floor)                          | _       |
  | [x - y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-minus)                          | _       |
  | [x * y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-mul)                            | _       |
  | [numbers.range](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-numbersrange)           | _       |
  | [numbers.range_step](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-numbersrange_step) | _       |
  | [x + y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-plus)                           | _       |
  | [rand.intn](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-randintn)                   | _       |
  | [x % y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-rem)                            | _       |
  | [round](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-numbers-round)                          | _       |


- [Aggregates](https://www.openpolicyagent.org/docs/latest/policy-reference/#aggregates)
  | Builtin                                                                                             | Feature |
  |-----------------------------------------------------------------------------------------------------|---------|
  | [count](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-aggregates-count)     | _       |
  | [max](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-aggregates-max)         | _       |
  | [min](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-aggregates-min)         | _       |
  | [product](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-aggregates-product) | _       |
  | [sort](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-aggregates-sort)       | _       |
  | [sum](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-aggregates-sum)         | _       |

- [Arrays](https://www.openpolicyagent.org/docs/latest/policy-reference/#arrays-2)
  | Builtin                                                                                                   | Feature |
  |-----------------------------------------------------------------------------------------------------------|---------|
  | [array.concat](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-array-arrayconcat)   | _       |
  | [array.reverse](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-array-arrayreverse) | _       |
  | [array.slice](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-array-arrayslice)     | _       |

- [Sets](https://www.openpolicyagent.org/docs/latest/policy-reference/#sets-2)
  | Builtin                                                                                                 | Feature |
  |---------------------------------------------------------------------------------------------------------|---------|
  | [x & y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-sets-and)                 | _       |
  | [intersection](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-sets-intersection) | _       |
  | [x - y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-sets-minus)               | _       |
  | [x \| y](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-sets-or)                 | _       |
  | [union](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-sets-union)               | _       |

- [Objects](https://www.openpolicyagent.org/docs/latest/policy-reference/#object)
  | Builtin                                                                                                              | Feature      |
  |----------------------------------------------------------------------------------------------------------------------|--------------|
  | [json.filter](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-jsonfilter)               | _            |
  | [json.match_schema](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-jsonmatch_schema)   | `jsonschema` |
  | [json.patch](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-jsonpatch)                 | `jsonpatch`  |
  | [json.remove](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-jsonremove)               | _            |
  | [json.verify_schema](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-jsonverify_schema) | `jsonschema` |
  | [object.filter](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-objectfilter)           | _            |
  | [object.get](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-objectget)                 | _            |
  | [object.keys](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-objectkeys)               | _            |
  | [object.remove](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-objectremove)           | _            |
  | [object.subset](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-objectsubset)           | _            |
  | [object.union](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-objectunion)             | _            |
  | [object.union_n](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-object-objectunion_n)         | _            |

- [Strings](https://www.openpolicyagent.org/docs/latest/policy-reference/#strings)
  | Builtin                                                                                                                           | Feature |
  |-----------------------------------------------------------------------------------------------------------------------------------|---------|
  | [concat](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-concat)                                    | _       |
  | [contains](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-contains)                                | _       |
  | [endswith](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-endswith)                                | _       |
  | [format_int](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-format_int)                            | _       |
  | [indexof](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-indexof)                                  | _       |
  | [indexof_n](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-indexof_n)                              | _       |
  | [lower](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-lower)                                      | _       |
  | [replace](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-replace)                                  | _       |
  | [split](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-split)                                      | _       |
  | [sprintf](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-sprintf)                                  | _       |
  | [startswith](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-startswith)                            | _       |
  | [strings.any_prefix_match](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-stringsany_prefix_match) | _       |
  | [strings.any_suffix_match](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-stringsany_suffix_match) | _       |
  | [strings.render_template](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-stringsrender_template)   | _       |
  | [strings.replace_n](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-stringsreplace_n)               | _       |
  | [strings.reverse](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-stringsreverse)                   | _       |
  | [substring](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-substring)                              | _       |
  | [trim](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-trim)                                        | _       |
  | [trim_left](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-trim_left)                              | _       |
  | [trim_prefix](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-trim_prefix)                          | _       |
  | [trim_right](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-trim_right)                            | _       |
  | [trim_space](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-trim_space)                            | _       |
  | [trim_suffix](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-trim_suffix)                          | _       |
  | [upper](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-upper)                                      | _       |

- [Regex](https://www.openpolicyagent.org/docs/latest/policy-reference/#regex)
  | Builtin                                                                                                                                         | Feature |
  |-------------------------------------------------------------------------------------------------------------------------------------------------|---------|
  | [regex.find_all_string_submatch_n](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-regex-regexfind_all_string_submatch_n) | `regex` |
  | [regex.find_n](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-regex-regexfind_n)                                         | `regex` |
  | [regex.globs_match](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-regex-regexglobs_match)                               | `regex` |
  | [regex.is_valid](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-regex-regexis_valid)                                     | `regex` |
  | [regex.match](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-regex-regexmatch)                                           | `regex` |
  | [regex.replace](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-regex-regexreplace)                                       | `regex` |
  | [regex.split](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-regex-regexsplit)                                           | `regex` |
  | [regex.template_match](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-regex-regextemplate_match)                         | `regex` |

- [Glob](https://www.openpolicyagent.org/docs/latest/policy-reference/#regex)
  | Builtin                                                                                                      | Feature |
  |--------------------------------------------------------------------------------------------------------------|---------|
  | [glob.match](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-glob-globmatch)           | `glob`  |
  | [glob.quote_meta](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-glob-globquote_meta) | `glob`  |

- [Bitwise](https://www.openpolicyagent.org/docs/latest/policy-reference/#regex)
  | Builtin                                                                                              | Feature |
  |------------------------------------------------------------------------------------------------------|---------|
  | [bits.and](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-bits-bitsand)       | _       |
  | [bits.lsh](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-bits-bitslsh)       | _       |
  | [bits.negate](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-bits-bitsnegate) | _       |
  | [bits.or](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-bits-bitsor)         | _       |
  | [bits.rsh](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-bits-bitsrsh)       | _       |
  | [bits.xor](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-bits-bitsxor)       | _       |

- [Conversions](https://www.openpolicyagent.org/docs/latest/policy-reference/#conversions)
  | Builtin | Feature |
  |-------|---------|
  [to_number](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-conversions-to_number) | _ |
|
- [Units](https://www.openpolicyagent.org/docs/latest/policy-reference/#units)
  | Builtin                                                                                                           | Feature |
  |-------------------------------------------------------------------------------------------------------------------|---------|
  | [units.parse](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-units-unitsparse)             | _       |
  | [units.parse_bytes](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-units-unitsparse_bytes) | _       |

- [Types](https://www.openpolicyagent.org/docs/latest/policy-reference/#types)
  | Builtin                                                                                              | Feature |
  |------------------------------------------------------------------------------------------------------|---------|
  | [is_array](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-types-is_array)     | _       |
  | [is_boolean](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-types-is_boolean) | _       |
  | [is_null](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-types-is_null)       | _       |
  | [is_number](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-types-is_number)   | _       |
  | [is_object](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-types-is_object)   | _       |
  | [is_set](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-types-is_set)         | _       |
  | [is_string](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-types-is_string)   | _       |
  | [type_name](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-types-type_name)   | _       |
  
- [Encoding](https://www.openpolicyagent.org/docs/latest/policy-reference/#encoding)
  | Builtin                                                                                                                              | Feature     |
  |--------------------------------------------------------------------------------------------------------------------------------------|-------------|
  | [base64.is_valid](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-base64is_valid)                     | `base64`    |
  | [base64url.decode](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-base64urldecode)                   | `base64`    |
  | [base64url.encode](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-base64urlencode)                   | `base64url` |
  | [base64url.encode_no_pad](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-base64urlencode_no_pad)     | `base64url` |
  | [hex.decode](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-hexdecode)                               | `hex`       |
  | [hex.encode](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-hexencode)                               | `hex`       |
  | [json.is_valid](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-jsonis_valid)                         | _           |
  | [json.marshal](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-jsonmarshal)                           | _           |
  | [json.marshal_with_options](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-jsonmarshal_with_options) | _           |
  | [json.unmarshal](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-jsonunmarshal)                       | _           |
  | [urlquery.decode](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-urlquerydecode)                     | `urlquery`  |
  | [urlquery.decode_object](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-urlquerydecode_object)       | `urlquery`  |
  | [urlquery.encode](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-urlqueryencode)                     | `urlquery`  |
  | [urlquery.encode_object](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-urlqueryencode_object)       | `urlquery`  |
  | [yaml.is_valid](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-yamlis_valid)                         | `yaml`      |
  | [yaml.marshal](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-yamlmarshal)                           | `yaml`      |
  | [yaml.unmarshal](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-encoding-yamlunmarshal)                       | `yaml`      |

- [Time](https://www.openpolicyagent.org/docs/latest/policy-reference/#time)
   | Builtin                                                                                                                    | Feature |
   |----------------------------------------------------------------------------------------------------------------------------|---------|
   | ([time.add_date](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timeadd_date)                  | `time`  |
   | [time.add_date](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timeadd_date)                   | `time`  |
   | [time.clock](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timeclock)                         | `time`  |
   | [time.date](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timedate)                           | `time`  |
   | [time.diff](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timediff)                           | `time`  |
   | [time.format](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timeformat)                       | `time`  |
   | [time.now_ns](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timenow_ns)                       | `time`  |
   | [time.parse_duration_ns](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timeparse_duration_ns) | `time`  |
   | [time.parse_ns](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timeparse_ns)                   | `time`  |
   | [time.parse_rfc3339_ns](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timeparse_rfc3339_ns)   | `time`  |
   | [time.weekday](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-time-timeweekday)                     | `time`  |

- [Cryptography](https://www.openpolicyagent.org/docs/latest/policy-reference/#crypto)
   | Builtin                                                                                                             | Feature  |
   |---------------------------------------------------------------------------------------------------------------------|----------|
   | [crypto.hmac.equal](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-crypto-cryptohmacequal)   | `crypto` |
   | [crypto.hmac.md5](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-crypto-cryptohmacmd5)       | `crypto` |
   | [crypto.hmac.sha1](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-crypto-cryptohmacsha1)     | `crypto` |
   | [crypto.hmac.sha256](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-crypto-cryptohmacsha256) | `crypto` |
   | [crypto.hmac.sha512](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-crypto-cryptohmacsha512) | `crypto` |
   | [crypto.md5](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-crypto-cryptomd5)                | `crypto` |
   | [crypto.sha1](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-crypto-cryptosha1)              | `crypto` |
   | [crypto.sha256](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-crypto-cryptosha256)          | `crypto` |

- [Graphs](https://www.openpolicyagent.org/docs/latest/policy-reference/#graph)
   | Builtin                                                                                                       | Feature |
   |---------------------------------------------------------------------------------------------------------------|---------|
   | [graph.reachable](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-graph-graphreachable) | `graph` |
   | [walk](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-graph-walk)                      | `graph` |

- [UUID](https://www.openpolicyagent.org/docs/latest/policy-reference/#uuid)
   | Builtin                                                                                                | Feature |
   |--------------------------------------------------------------------------------------------------------|---------|
   | [uuid.parse](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-uuid-uuidparse)     | `uuid`  |
   | [uuid.rfc4122](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-uuid-uuidrfc4122) | `uuid`  |

- [Semantic Versions](https://www.openpolicyagent.org/docs/latest/policy-reference/#semver)
   | Builtin                                                                                                        | Feature  |
   |----------------------------------------------------------------------------------------------------------------|----------|
   | [semver.compare](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-semver-semvercompare)   | `semver` |
   | [semver.is_valid](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-semver-semveris_valid) | `semver` |

- [OPA](https://www.openpolicyagent.org/docs/latest/policy-reference/#opa
   | Builtin                                                                                             | Feature |
   |-----------------------------------------------------------------------------------------------------|---------|
   | [opa.runtime](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-opa-oparuntime) | _       |

- [Debugging](https://www.openpolicyagent.org/docs/latest/policy-reference/#opa)
   | Builtin                                                                         | Feature |
   |---------------------------------------------------------------------------------|---------|
   | [print(...)](https://www.openpolicyagent.org/docs/latest/policy-reference/#opa) | _       |

- [Tracing](https://www.openpolicyagent.org/docs/latest/policy-reference/#tracing)
   | Builtin                                                                                      | Feature |
   |----------------------------------------------------------------------------------------------|---------|
   | [trace](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-tracing-trace) | _       |

## Typed history tables (native Rust, RVM only)

The opt-in `history` feature enables typed history tables, not a Rego builtin.
It implies `rvm` and `arc`, supports no_std, and is not included in the default
features or `full-opa`. The former generic history builtin is removed; calls to
it fail function resolution. Language bindings do not forward a `history` feature
or expose the native owner/identity API.

The canonical owned DSL and Event trait belong to in-tree `src/history-syntax`;
`junco-core` owns flat source validation/lowering and shared contracts,
`history-store` owns interning and history transactions, and `history-semantics`
owns numeric compilation/evaluation and generic policies. Regorus retains the
native `Value` parser, VM dispatch/limit adapter, and shared Program-keyed table
cache. Its public `HistoryStore::{new, intern_principal, intern_action,
intern_resource, new_history, append, truncate, len}` APIs are unchanged. Store's
generic typed `Store<E>`/`History<E>` APIs are separate, not replacement Regorus
entrypoints. Native no_std + alloc remains supported. `std` and Semantics' `cache`
do not imply `runtime`; Regorus `history` enables Store and Semantics runtime,
while source validation depends only on core and Syntax. `test-util` supplies
dev-only integration probes.

### Native boundary

Create an application-owned `Arc<HistoryStore>` from
`regorus::languages::history_table`. Intern exact raw UTF-8 paths separately with
`intern_principal`, `intern_action`, and `intern_resource`. The resulting opaque
eight-byte `Principal`, `Action`, and `Resource` IDs form an `Event` containing
exactly those three coordinates. Case, slashes, embedded NULs, and distinct
Unicode encodings remain distinct; there is no normalization or ancestry match.
IDs are not recycled, and foreign-owner IDs are rejected.

Use `store.new_history()`, then `store.append(&history, &events)`,
`store.truncate(&history, len)`, and `store.len(&history)`. Cloned handles share
events. Compile cold policy JSON with `compile(&table, batch_size)`; zero is an
error. After `vm.load_program(program)`, call `vm.attach_history(store.clone())`
and `vm.set_history_input(history, request)`, then
`vm.execute_entry_point_by_name("decide")`. The result is `Value::Null` for grant
or the zero-based first violated rule index. Decisions never append the candidate.
Repeated executions retain staged input. Loading another program cancels an old
execution and requires explicit reattachment and restaging.

### Cold policy grammar

The table envelope is `{"rules": [{"mode": "require"|"forbid", "request": …,
"history": …}]}`. Rules are ordered: require rejects a matching request when the
history is outside its language; forbid rejects when it is inside. Nonmatching
request heads skip the rule.

The request is `{"any":true}` or `{"object":{…}}` containing only `principal`,
`action`, and `resource`. Each coordinate is omitted/a wildcard, `{"any":true}`,
`{"value":"raw path"}`, or `{"var":"name"}`. Variables belong to one domain;
reusing a name across domains is invalid. No nested patterns, arbitrary Value
constants, optional runtime coordinates, or container matching remain.

Tests are Boolean literals, `{"and":[test,…]}`, `{"or":[test,…]}`, or
`{"eq":{"path":["action"],"term":{"value":"edit"}}}` (also `neq`). Paths
select exactly one of the three coordinates. A term is a string constant or
`{"var":"name"}` declared by the head in that same domain. Empty conjunction
is true; empty disjunction is false. Every runtime coordinate is present, so
equality and disequality are complements.

| History expression | Complete-history language |
|---|---|
| `{"empty":true}` | No histories |
| `{"all":true}` | All finite histories |
| `{"epsilon":true}` | Empty history only |
| `{"test":test}` | One event satisfying the test |
| `{"concat":[regex,…]}` | Chronological concatenation; empty is epsilon |
| `{"union":[regex,…]}` | Union; empty is empty language |
| `{"intersect":[regex,…]}` | Intersection; empty is universal |
| `{"star":regex}` | Kleene star |
| `{"not":regex}` | Complement over complete finite histories |

### Batching, sharing, and errors

Compilation emits one `HistoryStep` instruction per ordered rule. Each dispatch
consumes at most the explicit batch size and repeats at the same PC when more
events remain. Intermediate nullable prefixes do not grant. The existing VM
executor charges dispatch budgets and preserves continuations during suspension.

A decision captures a revision and target length before execution, including an
empty table. Concurrent appends are excluded until the next decision. Truncation
that removes events changes the revision; resume or finalization reports typed
`HistoryChanged`, rather than restarting or publishing a stale grant. Attachment
or staged-input changes during an active/suspended execution fail.

The owner shares bounded table/graph and retained-prefix caches across VMs;
active continuations pin their graph instance. Eviction or graph replacement
cannot reinterpret a pinned residual. Successful batches publish their cursor
only after fallible batch work completes; errors preserve the batch-entry cursor.
Graph exhaustion permits one fresh lazy-graph retry per rule per decision,
replayed through bounded dispatches. Native errors remain typed in
`VmError::History`; resource limits retain the VM's existing limit variants.

Programs contain portable postorder source tables, not live IDs or store identity.
`HistoryTableRule` retains its mode/source envelope, now using core `RuleMode`
and `FlatPair<String>` with `Component`, `FlatHead`, `FlatTerm`, `FlatTest`, and
`FlatRegex`. The v8 field/variant order and serialized names are unchanged.
`Program::validate_limits` validates these sources even without `history`;
repeated edges, unused nodes, and valid non-last roots remain supported without
unfolding the DAG. Attachment interns constants in the supplied store outside
decision execution. Serialization version 8 rejects older bytecode; recompile
rather than translate.

### Proof and measurement boundaries

The shared specifications live in core's `src/verify/history_specs.rs`; semantic
algebra lives in `history-semantics/src/verify/history_algebra.rs`. Body proofs cover
owned DSL lowering, constant encoding under later map extensions, the numeric
compiler/evaluator, raw/numeric typed-history correspondence, and cached lifecycle
and publication receipts. Native Eq/Hash coherence and stable user projections
are conditional obligations; separating these crates is not a universal proof of
external Event implementations, including root Junco's native `LockEvent` adapter.
Narrow map/container leaves, synchronization, allocation, clocks, arena destruction,
Regorus `Value` parsing, and native facade/diagnostic callbacks remain explicit
trust boundaries. Regorus's byte encoder is a native adapter that delegates UTF-8
interning to `history-store`, not a universally verified external component encoder.

The matched proof configuration uses Rust `1.98.1`, Verus
`0.2026.10.04.426d8b0`, Z3 `4.16.0`, and `vstd = 0.0.0-2026-10-04-0306`.
These boundaries describe the implementation and contracts, not a claim that
every configuration or external consumer has passed verification.

`cargo bench --features history --bench history_table` measures native decisions
with batch size 256 and 16/256/4096 events for both early-accepting `contains edit`
and full-scan `edit*` policies. Cases cover unchanged-prefix reuse, one appended
event after priming the retained prefix, and revision-invalidated root replay
with graph/successor caches warm. Compilation, interning, attachment, staging,
truncation, append, and the priming decision occur outside timing. The replay
control bypasses retained-prefix reuse without disabling symbolic graph caches;
the `cache` Cargo feature is not a retained-prefix-cache switch.
`retained_residuals_avoid_replay_without_changing_answers` also checks identical
accept/reject answers and exact event work with retained cursors versus clearing
only those cursors, in both execution modes. These are decision measurements,
not ingestion or generic-builtin benchmarks.

