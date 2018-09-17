add
;; PROBLEM 6: Find a fixed-point combinator in {B,W,M}

  a(a(a(B, x), y), z) == a(x, a(y, z))
  a(a(W, x), y) == a(a(x, y), y) 
  a(M, x) == a(x, x)

  a(y, f(y)) != a(f(y), a(y, f(y)))
]

operator precedence a f B W M

operator status a lr

kb

