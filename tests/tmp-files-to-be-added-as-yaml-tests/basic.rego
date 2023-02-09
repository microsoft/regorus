package basic

import future.keywords.if
import future.keywords.in

default hello := false

hello if input.message == "world"


default foo := false

foo {
  # some i, {j:5} in {1,2,3} & {5, 6}
  true
}

bar {
 1 in {1, 2}
}