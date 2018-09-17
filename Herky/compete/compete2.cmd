add
;; PROBLEM 2: Robbins Algebra plus o(c, c) = c implies
;;     the Huntington's axiom.
  o(x, y) == o(y, x)
  o(o(x, y), z) == o(x, o(y, z))
  n(o(n(o(x, y)), n(o(x, n(y))))) == x
  o(c, c) == c
  o(n(o(a, n(b))), n(o(n(a), n(b)))) != b
;  o(a, n(o(a, n(a)))) != a
]

operator precedence n o c

kb
