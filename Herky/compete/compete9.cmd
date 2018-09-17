add
;; PROBLEM 9: skew-symmetry of h(w,x,y,z) = (w*x,y,z) - x*(w,y,z) - (x,y,z)*w.

  (x + y) == (y + x)
  x + (y + z) == (x + y) + z
  x + 0 == x
  x + -(x) == 0
  (x * (y + z)) == ((x * y) + (x * z))
  ((x + y) * z) == ((x * z) + (y * z))

  (x * y) * y == x * (y * y)
  (x * x) * y == x * (x * y)

  a(x, y, z) == ((x * y) * z) + -(x * (y * z))
  h(w, x, y, z) == a((w * x), y, z) + -(x * a(w,y,z)) + -(a(x,y,z) * w)

  h(e, b, c, d) + (h(b, e, c, d)) != 0
]

operator precedence h a * - + 0

kb

