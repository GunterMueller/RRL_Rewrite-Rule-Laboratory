;; CMD file for K

init ;; initialize

add 

;; Rewrite System for K

;; connectives
n(x) ==  x + 1
orr(x,y) == (x * y)  + x + y
imp(x,y) == (x * y) + x + 1

; Boolean Algebra
x + x == 0
x * (y + z) == (x * y) + (x * z)
x * 0 == 0
x * x == x
x + 0 == x
x * 1 == x

; Modal operators

L(x) * L(y) == L(x * y)
L(1) == 1

;; for Q       L(0) == 0

]     ;; to finish adding

oper ac + *

oper pre  imp n orr * L + 0 1

kb



