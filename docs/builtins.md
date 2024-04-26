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
