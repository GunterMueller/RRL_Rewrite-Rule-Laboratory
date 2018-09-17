add
;;; PROBLEM 10: In a right alternative ring (just the right alternative axiom)
;;;   (((x,x,y)*x)*(x,x,y)) = 0.	

  (x + y) == (y + x)
  x + (y + z) == (x + y) + z
  x + 0 == x
  x + -(x) == 0
  (x * (y + z)) == ((x * y) + (x * z))
  ((x + y) * z) == ((x * z) + (y * z))

  (x * y) * y == x * (y * y)

  a(x, y, z) == ((x * y) * z) + -(x * (y * z))
  h(w, x, y, z) == a((w * x), y, z) + -(x * a(w,y,z)) + -(a(x,y,z) * w)

  a(c, c, d) * d * a(c, c, d) != 0 
]

operator precedence h a * - + 0

kb

