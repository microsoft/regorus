package acc.rego

import future.keywords.in

[ 1, null, 5, "Hello", [ [ 1, 2, 3, set( ), { set(
), 5, `ab
`}] ],
  set().a.b.c[a.b],
  1 >= 2 <= 1 + (- 8 * 44),
  6, (7, 8 in [ 5, 6] & 7),
  {
    a : 56,
    b : 0,
    5 : 6
  },
  a.foo(5+6, 8, {9}),
  [ (x + 5) |
    foo(x)
    true
    not foo(x)
      { (x + 5) |
    foo(x)
    true
    not foo(x)
  }

  ],
  {
    a : { 5, 6, 7 },
    b : 6,
    c : { p: q |
      p + 5 with data.p as 86
      q * 6
      5 in {5, 6}
    }
  }
]