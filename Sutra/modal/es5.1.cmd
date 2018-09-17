init

add

;; typing info 

[ID : acc]
[! : wor, acc -> wor]
[* : acc, acc -> acc]
[i : acc -> acc]
[L : bool -> bool]
[M : bool -> bool]

;; reflexivity  E(T). There is a neutral element in A.

x ! ID == x

;; E(Q4) - transitivity of * (semi-group)

(X ! (Y * Z)) == (X ! Y) ! Z
((X * Y) * Z) == (X * (Y * Z)) 

;; E(S4)  (monoid)

x * ID == x
ID * x == x

;; E(S5) make it a group

x * i(x) == ID

]

oper pre  i ! *

oper sta * lr
oper sta ! lr

kb
