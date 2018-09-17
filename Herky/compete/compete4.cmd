add
;; PROBLEM 4: The following single axiom specifies the free 
;;            groups, including the associativity of *.
  i(z * i(z)) * (i(i((x * w) * y) * x) * i(y)) == w
  (a * b) * c != a * (b * c)
]

operator status * lr
operator precedence i *

kb

