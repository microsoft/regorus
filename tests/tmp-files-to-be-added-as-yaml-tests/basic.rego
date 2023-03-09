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

x = y {
  some k
  k = 15
  z := k
  y = { p |
    p = [ q | q = z ]
  }
}

z = { p |
  q = k
  p = p1
  p1 = [ q | q = r ]
  r = [1, 2, 3][_]
  k = [1, 2, 3][_]
}

test = q {
    k = t
    t = 100
    q = k
}
