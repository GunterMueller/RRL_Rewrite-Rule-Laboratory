init

add

;; typing info 

[1 : acc]
[! : wor, acc -> wor]
[* : acc, acc -> acc]

;; reflexivity  E(T). There is a neutral element in A.

x ! 1 == x

;; E(Q4) - transitivity of * (semi-group)

(X ! (Y * Z)) == (X ! Y) ! Z
((X * Y) * Z) == (X * (Y * Z)) 

]

oper pre   * !

oper sta * lr
oper sta ! rl

kb
