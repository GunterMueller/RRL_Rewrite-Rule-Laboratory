add
;; PROBLEM 5: The Wajsberg algebra formulation of a conjecture 
;;            by Lukasiewicz.

  i(T,x) == x
  i(i(x,y),i(i(y,z),i(x,z))) == T
  i(i(x,y),y) == i(i(y,x),x)
  i(i(n(x),n(y)),i(y,x)) == T

  i(i(i(a,b),i(b,a)),i(b,a)) != T
]

operator precedence i n a b T 

operator status i lr

kb
