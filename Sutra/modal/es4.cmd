init

add

;; typing info 

[ID : acc]
[! : wor, acc -> wor]
[* : acc, acc -> acc]
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

]

oper pre   * !

oper sta * lr
oper sta ! rl

kb
