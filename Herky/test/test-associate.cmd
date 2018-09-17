option prove f
option order s
option critical rulesize s

add
(x + y) == y + x
x * y == y * x
+(x, 0) == x
x * 0 == 0
x * 1 == x
+(x, i(x)) == 1
x * i(x) == 0
x * +(y, z) == +((x * y), (x * z))
+(x, (y * z)) == +(x, y) * +(x, z)

]

opera
prec
i * + 1 0

prove
(x * y) * z == (x * (y * z))

postpone
postpone
left

; Number of rules generated             = 166
; Number of rules retained              = 73
; Number of critical pairs              = 3849 (of which 903 are unblocked.)
; Time used (incl. garbage collection)  = 59.850 sec
; Done at: 11:19:29 Jul 28 1992 on sparc2.


