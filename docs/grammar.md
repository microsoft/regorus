
```
module: package  imports { rule }

package: "package" path-ref

imports: { "import" path-ref [ "as" var ] }

path-ref: path-ref NO_WS "." NO_WS IDENT
| path-ref NO_WS "[" STRING "]"
| IDENT

rule: default-rule
| spec-rule

default-rule: "default" rule-ref assign-op term

spec-rule: rule-head rule-bodies

rule-head: func-rule
| contains-rule
| object-rule
| set-rule
| compr-rule

func-rule: rule-ref "(" term { "," term } [","] ")" [ rule-assign ]

contains-rule: rule-ref "contains" or-expr

object-rule: rule-ref NO_WS "[" membership-expr "]" rule-assign

set-rule: rule-ref NO_WS "[" membership-expr "]"

compr-rule: rule-ref [ rule-assign ]

rule-ref: rule-ref NO_WS  "." NO_WS var
| path-ref NO_WS "[" membership-expr "]"
| var

rule-assign: assign-op membership-expr

rule-bodies: "if"  "{" query "}" alternatives
| "if" literal-stmt alternatives
| "{" query "}" alternatives

alternatives: query-blocks
| else-blocks

query-blocks: { "{" query "}" }

else-blocks: { else-block }

else-block: "else" [rule-assign] "if" "{" query "}"
| "else" [rule-assign] "if" literal-stmt
| "else" [rule-assign] "{" query "}"

assign-op: "=" | ":="

query: literal-stmt { sep  literal-stmt }

sep: ";" | "\n" | "\r\n"

literal-stmt: literal with-modifiers

with-modifiers: { "with" path-ref "as" in-expr }

literal: some
| every
| expr
| not-expr

some: some-vars
| some-in

some-vars: "some" var { "," var }

some-in: "some" ref [ "," ref ] "in"

every: "every" var [ "," var ] "in" bool-expr "{" query "}"

expr: assign-expr

not-expr: "not" assign-expr

assign-expr: ref assign-op membership-expr

membership-expr: membership-expr "in" bool-expr
| bool-expr "," bool-expr
| bool-expr

in-expr: in-expr "in" bool-expr
| bool-expr

bool-expr: bool-expr bool-op or-expr
| or-expr

bool-op: "<" | "<=" | "==" | ">=" | ">" | "!="

or-expr: or-expr "|" and-expr
| and-expr

and-expr: and-expr "&" arith-expr
| arith-expr

arith-expr: arith-expr ("+" | "-") mul-div-expr
| mul-div-expr

mul-div-expr: mul-div-expr ("*" | "/") term
| term

term: ref

ref: scalar-or-var
| compr-set-or-object
| compr-or-array
| unary-expr
| parens-expr
| ref-dot
| ref-brack
| call-expr

ref-dot: ref NO_WS "." NO_WS var

ref-brack: ref NO_WS "[" in-expr "]"

call-expr: path-ref NO_WS "(" call-args  [","] ")"

call-args: in-expr { "," in-expr }

parens-expr: "(" membership-expr ")"

unary-expr: "-" in-expr

compr-set-or-object: set-compr
| set
| object-compr
| object

set-compr: "{" compr "}"

# Set must have at least one item.
set: "{" in-expr  { "," in-expr } [","] "}"
| "set(" ")" # empty set

object: "{" field { "," field } [","] "}"
| "{" "}" # empty object

field: in-expr ":" in-expr

# Comprehension or array
compr-or-array: array-compr
| array

array-compr: "[" compr "]"

array: "[" in-expr { "," in-expr } [","] "]"
| "[" "]"  # Empty array

# Comprehension
compr: ref "|" query

scalar-or-var: var
| NUMBER
| STRING
| RAWSTRING
| "null"
| "true"
| "false"

var: IDENT
| non-imported-future-keyword

non-imported-future-future-keyword: "contains" | "every" | "if" | "in"
```
