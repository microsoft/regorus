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

## History/request policies (Regorus extension)

`history.match(policy, history, request) -> boolean` requires the opt-in `history`
Cargo feature, which is not included in `full-opa` or the default features.
It works with the interpreter and RVM, including no_std builds. It matches an
explicit prior history oldest-to-newest; it never appends the request or mutates
either argument. Rego rules and comprehensions can aggregate Boolean results.

The policy is an object with exactly `history` and `request` members. All tagged
forms below have exactly one member; extra or unknown members are invalid.

| Request pattern | Meaning |
|---|---|
| `{"value": v}` | Exact structural Value equality; operator-looking literal objects stay literal |
| `{"var": "name"}` | Bind a nonempty name internally; every repeated occurrence must equal the complete bound Value |
| `{"any": true}` | Any defined Value, including null |
| `{"object": {key: pattern, ...}}` | Object with every required field; additional fields allowed |
| `{"array": [pattern, ...]}` | Array with exactly the given length |

Variable names are scoped to one pair, not Rego variables. Object keys and
values are ordinary Rego Values, not a fixed principal/action/resource schema.
Missing or Undefined required values fail the request pattern, including `any`
and `var`; present null is a normal value. Bindings are not returned.

A history test is `true`, `false`, `{"and": [test, ...]}`,
`{"or": [test, ...]}`, or a comparison:

```rego
{"eq": {"path": ["resource"], "term": {"var": "r"}}}
{"neq": {"path": ["action"], "term": {"value": "edit"}}}
```

Both comparisons accept either term form. Their payload contains exactly `path`
and `term`. Paths contain defined Value keys; `[]` selects the entire event.
Object-key lookup and set membership use Value collection semantics; array
indexes must be nonnegative integers fitting `usize`. Missing/Undefined values,
invalid indexes, and unsupported traversal make **both** equality and
disequality false. Thus `eq(p, v) OR neq(p, v)` means presence, not universal
truth. Empty `and` is true and empty `or` is false. Every variable reference is
validated even in a branch discarded by normalization or a nonmatching request.

| History expression | Complete-history language |
|---|---|
| `{"empty": true}` | No histories |
| `{"all": true}` | All finite histories, including empty |
| `{"epsilon": true}` | Empty history only |
| `{"test": test}` | Exactly one event satisfying the test |
| `{"union": [regex, ...]}` | Union; empty list is empty language |
| `{"concat": [regex, ...]}` | Chronological concatenation; empty list is epsilon |
| `{"star": regex}` | Kleene star |
| `{"intersect": [regex, ...]}` | Intersection; empty list is universal |
| `{"not": regex}` | Complement over all finite histories, not predicate negation |

For example, this pair accepts a release only when the supplied prior history
contains an edit of the same resource; unrelated later events do not erase it:

```rego
package example
import rego.v1

pair := {
    "request": {"object": {
        "action": {"value": "release"},
        "resource": {"var": "r"},
    }},
    "history": {"concat": [
        {"all": true},
        {"test": {"and": [
            {"eq": {"path": ["action"], "term": {"value": "edit"}}},
            {"eq": {"path": ["resource"], "term": {"var": "r"}}},
        ]}},
        {"all": true},
    ]},
}
result := history.match(pair, input.history, input.request)
```

The implementation uses lazy symbolic derivatives, not regex strings or an eager
DFA. Each pair has a 100 KiB structural graph-payload cap, excluding allocator
capacity/padding and external Value payloads; it is not a process-memory bound.
The active evaluator timer and configured memory limits apply during compilation
and replay. Existing Value comparisons are atomic operations, with limit checks
around them, not preemptible traversals. Allocation failures are reported only
where the underlying API supports fallible allocation.

Malformed policies and non-array histories follow builtin strictness: errors in
strict mode, Undefined otherwise. Top-level Undefined arguments propagate before
matching. Graph, allocation, invariant and resource-limit failures are always
errors, even through nested rules and negation. RVM hard matcher failures use
`VmError::HistoryMatchFailure`; scoped strict validation failures use
`VmError::HistoryMatchValidationError`. No binding or authorization/session API is
added, and the existing RVM restriction on `with` is unchanged.

With `cache`, each retained Engine or RegoVM keeps at most 16 exact policy Values
and their owned compiled graphs. Each pair has a lazy 256-entry event-class
successor LRU; signed predicates use canonical unsigned primitive truth vectors,
so events with different unused metadata can select the same successor. Within
one call these derivative/event caches also work without `cache`, but the pair is
dropped at return. Cached exploratory graph exhaustion evicts the entire pair
and retries once from a fresh graph; a fresh graph over the cap is a hard error.
Other errors are not retried. Evaluator clones start with empty matching caches;
VM program replacement clears them. Existing `cache::clear/configure` remains
regex/glob-only. `CompiledPolicy::eval_with_input` creates a fresh evaluator and
does not promise warm cross-call reuse.

Each retained pair keeps one shared `Rc<Array>` history snapshot and up to 16
exact-binding residual cursors. A request mismatch leaves this progress alone.
Pointer-identical arrays prove unchanged content; reconstructed/extended arrays
must compare the entire retained prefix structurally. Truncation or changed
prefixes replay from the source root and replace the old cursors only after a
successful match. Failures do not commit partially consumed progress. A proven
self-loop advances the cursor without changing its residual, but does not skip
later events. Equal Boolean answers alone never authorize residual reuse.

After policy/pattern/binding lookup, an unchanged pointer-identical history has
an O(1) history fast path. A new array requires O(n) prefix event comparisons,
including recursive payload-comparison costs; only automaton replay is limited
to the remaining suffix. Retained snapshots keep caller data alive and can force
full outer-array COW copies on append. There is no overall O(delta) guarantee,
caller-supplied history identity, revision counter, or checkpoint tree. Drop the
evaluator (or replace a VM's program) to release its local matching caches.

### Rust-to-Lean extraction

```sh
cargo test -p regorus-history-extract
AENEAS_HOME="$HOME/.aeneas" cargo xtask extract-history-lean
```

`verification/aeneas/history/rust` includes the production kernel, normalization,
symbolic derivatives and error sources literally, with a checked structural
VecStore backend. It does not include Regorus as a dependency or copy its
semantics. The task requires the already-installed pinned Aeneas
`nightly-2026.10.15-cd41995`, Charon `0.1.287` (`26abff028ced534ebf8e861f2d3dd1743e2aa318`), its
`nightly-2026-09-17` Rust SDK components, and Lean
`leanprover/lean4:v4.35.0-rc4`, matching both pinned dependencies. It installs no tools. The Lean project pins
Aeneas commit `cd419953b67caae3e4d6b514b3ee3f3f1ff76ea1` and mathlib commit
`1f414401f69059aa7eead47b53ee40bd38455eeb`.

The command regenerates fresh LLBC, runs strict translation, validates structured
source/name coverage for all 19 required production APIs and their local
normalization/symbolic helpers, elaborates Lean, and `#check`s manifest-generated
declaration names. It stages under `target/aeneas/history`, keeps dependency
caches between runs, and publishes generated files and both manifests only after
all checks pass. The temporary coverage file is checked but not published. A nonempty unmarked generated tree is
never replaced. Publication failures preserve or restore the prior snapshot.

The pinned `-print-unknown-externals` reporter crashes on Rust unit; the approved
task instead reports assumptions from `translation.json` and generated external
declarations. Only scalar diagnostic factories are explicitly opaque; no
normalization/symbolic implementation or VecStore interning body is hidden.
External assumptions include integer conversions, `size_of`, checked shifts,
Option copying/cloning, Result inspection, slice first/last/search/sort, and Vec
reservation/truncation/slice/pop/emptiness operations; diagnostic construction;
and the opaque types `MaybeUninit`, `Duration`, and `TryReserveError`. The manifest
and `TypesExternal`/`FunsExternal` files record the exact declarations.

This checks translation coverage and Lean elaboration, **not correctness**.
Value traversal/equality, request decoding/binding, runtime arena/storage layout,
event caches, history-progress reuse and evaluator/VM integration remain outside
the extracted core and are covered by Rust differential/integration checks.

Production correctness is established by the body-verified Verus contract on
`HistoryMatchState::evaluate` in `src/builtins/history/mod.rs`. Every successful
`Ok(answer)` equals the independent `policy_lang` specification in
`src/verify/history_specs.rs`: the head matches the request, and the tail consumes
committed history oldest-to-newest. Errors carry no Boolean interpretation and
preserve the retained-state invariant. The proof covers both Base
(`--no-default-features --features history,arc,std`) and Cached
(`--features history`) production profiles, including compilation, normalization,
symbolic execution, event-class caches, replay, and cursor reuse.

The FFI, Java, Python, Ruby, and WASM crates expose an opt-in `history` feature
that forwards to `regorus/history`; their default features are unchanged.

The trusted boundary consists of the existing numeric-library contracts;
semantic Value equality/cloning and collection, string, and Rc/Arc operations;
clocks and resource-limit queries; fallible Vec/SmallVec reservation; the
bumpus arena's `Layout::size`/`Layout::align` bridge, fallible chunk allocation
(`try_allocate`), and slice formation (`slice_ref`) — bump arithmetic, permission
bookkeeping, and freeing are body-verified, and bumpus declares no `global layout`
axiom, so no pointer-width or primitive-alignment assumption is imported; exact
SmallVec/std sequence operations, sorting, deduplication, search, rotation, and
checked shifts; symbol-index map access; concrete successor-LRU operations keyed by
transition and truth-word contents (including the opaque default hasher type);
the native state-drop adapter invoking verified release; and diagnostic formatting.
Hash-consing, bucket lookup/completeness, and structural equality are body-verified.
Hashconsius/bumpus pointer tables and buckets grow with infallible `alloc::vec::Vec`
(OOM aborts; bookkeeping is bounded by `MAX_GRAPH_BYTES` per store).
Native allocator `Send`/`Sync` markers rely on exclusive chunk ownership,
immutable shared access, and corresponding element-type bounds outside SMT.
No compiler, normalizer, derivative, interpreter, matcher,
replay, or evaluator body is trusted. The independent handwritten
`RegorusHistory.Spec.Language` Lean specification remains available with its
language-algebra theorems; the Verus counterparts are catalogued below. The
production-refinement theorem is the Verus contract.

Arena exhaustion is a distinct error, `HistoryError::ArenaExhausted`, separate
from global-allocator failure (`AllocationFailed`) and the byte cap
(`GraphLimit`). `CanonicalStore::intern_*` are verified transactional: on any
error the abstract graph and the charged byte count are unchanged. They also
carry a verified capacity theorem: `ArenaExhausted` can be returned only when
`slack < MAX_GRAPH_BYTES - capacity`, where `capacity` is the per-arena chunk size
and `slack` is the charged weight of the graph minus the bytes actually resident in
the arenas (never decreasing on a successful push, zero for a fresh store). A
production store (`ArenaStorage::new`, `capacity == MAX_GRAPH_BYTES`) therefore
hits `GraphLimit` before it can ever exhaust an arena. The premises
(`size_of::<ArenaX>() > 0`, `align_of::<ArenaX>() <= 16`, and
`MAX_GRAPH_BYTES` a multiple of each alignment) are `const`-asserted for every
compile target and re-checked at runtime so the proof does not rely on an
x86_64-specific layout axiom.

Each compiled pair keeps its hash-consed bump store for its whole lifetime: six
100 KiB chunks per retained pair, with no heap copy at compilation's end. Nodes
are interned by `hashconsius::BHConsign`; child lists use `SliceArena` with
`hashconsius::index::Buckets`. Failed compilation, evaluation/publication of fresh
pairs, eviction, explicit state release, and state destruction release the chunks.
The destructor adapter is native; the release implementation is verified.

Production evaluation passes a zero-sized `ObservationWorld` capability through
the clock and fallible reservation call sites; arena allocation uses verified bumpus operations.
The capability itself adds no runtime trace/counter or retained matcher state,
and does not change the Engine/FFI interface. Kernel reservation callbacks preserve the existing
reserve → charge → resize order. This makes observations explicit for the
production proof; its generic finite-interaction replay model is checked, while
the generated matcher’s native replay/adequacy link is not yet established.

Fresh Base/Cached production MIR reaches the real recursive Value/collection
comparisons. The pinned Aeneas backend currently rejects their mixed recursive
function/trait-implementation groups. The published kernel snapshot is therefore
not a production matcher correctness proof; no comparison body is hidden to
work around this limitation.

### Verified regex-language theorems

The paper *Past Regular Expressions over Product Events* states the results
below. Regorus adapts product events to JSON-like `Data`: missing paths make both
source `Eq` and `Neq` false, so source tests have no complement operation.
Union, intersection, concatenation, and test conjunction/disjunction are n-ary
sequences, with set and splice equations replacing binary rearrangements.
The independent definitions live in
[`history_specs.rs`](../src/verify/history_specs.rs) and
[`history_algebra.rs`](../src/verify/history_algebra.rs).

| Paper result | Independent theorem | Production contract |
| --- | --- | --- |
| Derivative correctness | `history_specs::lemma_derivative_correct`, `lemma_derive_word_correct`, `lemma_derive_word_nullable` | Pure language theorems; no runtime counterpart needed. |
| Similarity preserves language | `history_algebra::theorem_similarity_preserves_language`; policy corollary `theorem_similar_tails_same_decision`; source deviation `theorem_eq_or_neq_not_similar_to_true`; signed-kernel complement `lemma_test_complement_holds` and `lemma_test_complement_involutive` | `normalize.rs` smart constructors `regex_union`, `regex_intersect`, `regex_concat`, `regex_star`, `regex_not`, `regex_test`, `test_and`, `test_or`, `test_not` ensure language/truth equality with the unnormalized combination. Distributivity belongs to the equational theory but is not applied by the normalizer. |
| Symbolic derivative correctness | `history_algebra::theorem_symbolic_derivative_correct`; stronger `lemma_symbolic_derivative_interp` gives syntactic equality with `derivative` | `symbolic::verify::derivative_correct` on `symbolic_derivative`, bridged by `lemma_derivative_correct_is_symbolic_derivative`. Runtime smart-constructor contracts supply the paper's `Norm`; the independent theorem needs no normalization. |
| Matcher correctness | `history_algebra::theorem_matcher_correct`, `theorem_rule_decision`, `theorem_not_fired` | `HistoryMatchState::evaluate` ensures successful `answer == policy_lang`; `progress::verify::lemma_residual_is_symbolic_run` connects runtime residuals to the symbolic run. `history.match` returns this Boolean; the Rego author applies require/forbid modes. |

### Performance scopes

`cargo bench --features history --bench history_match` measures cold first
matching, same-array warm calls, independently reconstructed prefixes, appended
relevant and self-loop events, caller COW append plus evaluation, and alternating
request bindings sharing one snapshot, for 16/256/4096-event histories. Rego
preparation and fixture construction/warming are outside the timed region, except
the explicitly named COW operation. Prefix validation remains in the appended
and reconstructed-array timings. Every timed evaluation asserts its result.
