INIT
option
reduce
1
option
fastkb
poly
t
option
refute
t
refute
k
(X + 0) == X
((X * Y) * Z) == (X * (Y * Z))
(X * (Y + Z)) == ((X * Y) + (X * Z))
((X + Y) * Z) == ((X * Z) + (Y * Z))
(X * 0) == 0
(0 * X) == 0
x*x*x == x
;i(x) == x+x+x+x+x
;(x + i(x)) == 0
;x*i(y)==i(x*y)
;i(x)*y==i(x*y)
;i(x+y) == i(x)+i(y)
;i(i(x))==x
;i(0)==0
(a*b) == (b*a)
]
option
fopc
restrict
3
OPERATOR
AC-OPERATOR
+ 
OPERATOR
PRECEDENCE
b a * + 0
OPTION
AUTOORDER
POST-LIMIT
9999
RULE-LIMIT
9999
QUIT
option
cycle
t
AKB

