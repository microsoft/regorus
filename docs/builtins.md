# Built-in Functions


This page lists all the supported Rego built-in functions and the cargo feature that is needed to enable each builtin.

Those builtins that are not need for a specific use of the Regorus crate can be excluded from the binary by not specifying
the corresponding feature. This is useful in Confidential Computing scenarios where
  - There needs to be control over what a policy execution can and cannot do.
  - There needs to be control over exactly what goes into the [Trusted Computing Base](https://en.wikipedia.org/wiki/Trusted_computing_base).

Currently many builtins are `baked-in`, i.e. there is no way to exclude them from the TCB.
In future, each builtin will be associated with a feature (many builtins could be associated with the same feature).

Structured-value operations preserve collection traversal order and use
operation-local nesting budgets where needed. A nesting-limit error remains an
error when strict builtin errors are disabled; ordinary builtin errors retain
their existing Undefined/false behavior. These budgets do not restrict storing
native `Value`s or using their iterative comparison and output methods.

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

  `numbers.range_step` accepts integer endpoints and a positive integer step,
  includes the start, and stops before crossing the end. Descending ranges
  automatically subtract the step. Invalid steps are errors in strict mode
  and Undefined otherwise. Stepping uses exact integers and incremental
  allocation, with existing memory-limit checks during accumulation.

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
  | [strings.count](https://www.openpolicyagent.org/docs/latest/policy-reference/#builtin-strings-stringscount)                       | _       |
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

  `sprintf("%t", [value])` renders boolean values as `true` or `false`, following
  Rust's boolean formatting convention rather than OPA's embedded formatter
  diagnostics (such as `%!t(string=true)`).

  `strings.count` counts non-overlapping matches. An empty needle returns one
  plus the number of Unicode code points, not bytes or grapheme clusters.

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

  `json.marshal`, `json.marshal_with_options`, and `yaml.marshal` retain the
  upstream 64-container serialization budget. For example, an input containing
  65 nested arrays returns a typed serialization-depth error, even in non-strict
  mode; it cannot select a default or make negation succeed. Native `Value`
  formatting and `to_json_str()` remain iterative and do not use that callback
  budget.

  `urlquery.encode` and `urlquery.encode_object` retain the
  `application/x-www-form-urlencoded` escaping used by Rust's `url` crate.
  This intentionally differs from OPA's Go `net/url.QueryEscape` convention:

  | Input | Regorus (Rust `url` crate) | OPA / Go `net/url.QueryEscape` |
  |-------|---------------------------|-------------------------------|
  | `"~"` | `"%7E"`                   | `"~"`                         |
  | `"*"` | `"*"`                     | `"%2A"`                       |
  | `" "` | `"+"`                     | `"+"`                         |
  | `"+"` | `"%2B"`                   | `"%2B"`                       |
  | `"~* "` | `"%7E*+"`               | `"~%2A+"`                     |

  Object keys and values use the same escaping. This shared behavior applies
  to both the interpreter and RVM. Policies comparing encoded strings with
  OPA-generated output should account for the `~` and `*` differences;
  they reflect different encoding conventions, not data loss.

  `urlquery.decode` decodes one query component, preserving literal `&`, `=`,
  `#`, tabs, and newlines; `+` becomes a space. Parameter parsing remains the
  responsibility of `urlquery.decode_object`.

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

## History rules (`history.require` / `history.forbid`, RVM only)

The opt-in `history` feature lets Rego policies constrain a typed event history.
It implies `rvm` and is not included in the default features or `full-opa`.
Only the RVM compiler lowers these calls; the tree-walking interpreter, and the
RVM compiler without `history`, report an unknown function. Language bindings do
not forward a `history` feature.

### Rego syntax

```rego
package approvals
import rego.v1

release_after_edit := history.require(
    {"action": "release", "principal": actor, "resource": doc},
    [any, {principal == actor, action == "edit", resource == doc}, any],
)
no_remove_after_lock := history.forbid(
    {"action": "remove", "resource": doc},
    [any, {action == "lock", resource == doc}, any],
)

allow if {
    release_after_edit
    no_remove_after_lock
}
```

`history.require(request, language)` is `false` when the staged request matches
`request` and the history is outside `language`; `history.forbid` is `false` when
it is inside. Otherwise, including a nonmatching request, the call is `true`; it
is never undefined. Compose the Boolean with ordinary Rego.

The request pattern is an object literal keyed by `"principal"`, `"action"`,
and `"resource"`. A string value matches those exact bytes; a variable binds the
request's coordinate for use in the language; `_` or an omitted key matches
anything. Variables may not be named `principal`, `action`, `resource`, or `any`,
and each belongs to one coordinate.

| Language | Complete histories |
|---|---|
| `any` | All finite histories |
| `[]` | Empty history only |
| `{c == t, ...}` | One event satisfying every comparison |
| `true`, `set()` | One arbitrary event |
| `false` | No histories |
| `[a, b, ...]` | Chronological concatenation |
| `a \| b` | Union |
| `a & b` | Intersection |
| `a - b` | Difference (`a` and not `b`) |
| `star(a)` | Kleene star |

A comparison is `principal`, `action`, or `resource` with `==` or `!=` against a
string constant or a request variable of the same coordinate. `{}` is an empty
object, not a test; use `set()`. Malformed shapes, unknown names, unbound or
cross-coordinate variables fail RVM compilation with a spanned error.

Paths are exact raw UTF-8: case, slashes, embedded NULs, and distinct Unicode
encodings remain distinct; there is no normalization or ancestry match.

Each call compiles to one `HistoryStep` instruction and one row of
`Program::history_tables[0]`. Programs store portable sources (string constants,
not store identifiers) and serialize as format version 7; see the
[instruction reference](rvm/instruction-set.md#history-table-instructions).

### Native boundary

Create an `Arc<HistoryStore>` from `regorus::languages::history_table`. Every
wrapper fronts one process-wide arity-3 store: identities and histories are
shared, so wrappers accept each other's handles and IDs and are not a tenant
isolation boundary. Intern paths per coordinate with `intern(PRINCIPAL, path)`,
`intern(ACTION, path)` and `intern(RESOURCE, path)`, then build an `Event` with
`store.event(&[principal, action, resource])`, which validates arity and domain
membership. Interned paths live for the process; IDs are not recycled.

Use `store.new_history()`, then `store.append(&history, &events)`,
`store.truncate(&history, len)` and `store.len(&history)`. Compile the policy
with `Compiler::compile_from_policy`. After `vm.load_program(program)`, call
`vm.attach_history(store.clone())`, which interns the program's rule constants,
and `vm.set_history_input(history, request)`, then execute any entry point.
Decisions never append the request. Repeated executions retain the staged input.
Loading another program cancels any suspended execution and clears attachment
and input, not the application's histories. Executing a history rule without
attachment or staged input reports `HistoryContextMissing`; changing either
while an execution is suspended reports `HistoryExecutionActive`.
[`examples/history`](../examples/history/main.rs) walks through this sequence
(`cargo run --example history --features history`).

### Evaluation

A decision captures the history's revision and length at its first
`HistoryStep`; later appends are excluded until the next decision. Each dispatch
advances the rule's symbolic-derivative automaton by at most `batch_size` events
of that prefix and repeats at the same PC while events remain, so budgets are
charged per dispatch and suspension keeps the continuation. Intermediate
nullable prefixes do not grant. Truncation changes the revision: resume or
completion reports `HistoryChanged` rather than publishing a stale result.
Rule caching evaluates each history rule at most once per execution.

Sources are evaluated as DAGs: shared subterms, unused nodes and non-last roots
are never unfolded. Each `HistoryStore` wrapper keeps bounded, Program-keyed
caches of compiled rule graphs and of retained per-history prefixes (keyed by
each history's immutable ID), shared by every VM attached to it. An active
continuation pins its graph, so eviction or graph replacement cannot
reinterpret it. A batch publishes its cursor only after its fallible work
completes; an error keeps the batch-entry cursor. When a lazily built graph
exceeds its 100 KiB payload budget (`HistoryError::GraphBudget`), the rule
retries once per decision on a fresh graph, replayed through bounded
dispatches. Native failures are fatal `VmError::History` errors, never rule
failures; time and memory limits keep the VM's own variants.

### Proof boundaries

Verus checks the history crates and Regorus's host adapter
(`cargo verus verify --features history`). Shared specifications live in
`junco-core/src/verify/history_specs.rs` and the semantic algebra in
`history-semantics/src/verify/history_algebra.rs`. Body proofs cover lowering of
owned rules, constant encoding, the numeric compiler and evaluator, the
typed/numeric history correspondence and the cached decision lifecycle: a
successful answer equals the source language's acceptance of the pinned
history prefix. Locking, allocation, clocks, arena destruction, Regorus's
Rego-to-rule lowering and byte-interning adapter, the native facade and
diagnostics, and Eq/Hash coherence of native event types are trusted, not
proved.

The CI proof configuration (`.github/workflows/verus.yml`) is Rust 1.98.1,
Verus `0.2026.10.04.426d8b0`, Z3 4.16.0 and `vstd = 0.0.0-2026-10-04-0306`.

### Benchmarks

`cargo bench --features history --bench history_table` measures compiled Rego
decisions with batch size 256 over histories of 16, 256 and 4096 events, for an
early-accepting `[any, {... action == "edit" ...}, any]` policy and a full-scan
`star({action == "edit"})` policy. Cases cover an unchanged prefix, one event
appended after the prefix was retained, and a replay from the root after
truncation invalidated the revision, with graph and successor caches warm.
Compilation, interning, attachment, staging, truncation, appends and the priming
decision run outside timing. These measure decisions, not ingestion.
