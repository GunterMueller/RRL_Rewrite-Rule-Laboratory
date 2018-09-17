add
;; PROBLEM 1: In a group, if x * x * x = e for all x in the group, then
;; the commutator h(h(x, y), y) = e for all x and y, where h(x, y) is defined
;; as x * y * g(x) * g(y).

  f(e, x) == x
  f(g(x), x) == e
  f(f(x, y), z) == f(x, f(y, z))
  h(x, y) == f(x, f(y, f(g(x), g(y))))

  f(x, f(x, x)) == e
  h(h(a, b), b) != e
]

operator status f l
operator precedence h g f 

kb
