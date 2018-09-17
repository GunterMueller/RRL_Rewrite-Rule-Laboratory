add
;; PROBLEM 3: In a ternary Boolean algebra with the third axiom removed,
;; it is true that f(x, g(x), y) == y for all x and y.

  f(f(v, w, x), y, f(v, w, z)) == f(v, w, f(x, y, z))
  f(y, x, x) == x
  f(x, x, y) == x
  f(g(y), y, x) == x

  f(a, g(a), b) != b
]

operator status f l
operator precedence f g 

kb
