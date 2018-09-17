option critical rulesize d

add
;; x^3 = x implies ring commutativity.
;; the order of the input really matters!!!
x * i(y) == i(x * y)
x * x * x == x
(x + 0) == x
(x + i(x)) == 0
((x * y) * z) == (x * (y * z))
(x * (y + z)) == ((x * y) + (x * z))
(x + y) * z == (x * z) + (y * z)
]

operator ac-operator
+ 

operator precedence
* i + 0

operator cancel +
y

operator status * lr

kb

postpone
postpone
postpone
postpone
postpone
postpone
postpone
postpone
postpone
postpone
postpone
postpone

; Number of rules generated             = 72
; Number of rules retained              = 7
; Number of critical pairs              = 388 (of which 74 are unblocked.)
; Time used (incl. garbage collection)  = 23.790 sec
; Done at: 17:8:28 Jul 28 1992 on sparc 2

