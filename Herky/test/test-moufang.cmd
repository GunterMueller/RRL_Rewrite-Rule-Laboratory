option fast poly t n y
option prove f
option brake discard degree 4

add
(x * y) * y == x * (y * y)
(x * x) * y == x * (x * y)

x + -(x) == 0
(x * 0) == 0
(0 * x) == 0
(x * (y + z)) == ((x * y) + (x * z))
((x + y) * z) == ((x * z) + (y * z))
asso(x, y, z) == ((x * y) * z) + -(x * (y * z))
comm(x, y) == ((x * y) + (-(y * x)))
]

operator precedence asso comm * - + 0

prove
; (x * y) * x == x * (y * x)
; asso(y, x, z) + asso(x, y, z) == 0
;;; Left Moufang identity.
; ((x * y) * x) * z == x * (y * (x * z))
;;; Right Moufang identity.
; ((x * z) * y) * z == x * (z * (y * z))
;;; Middle Moufang identity.
; (x * (y * z)) * x == (x * y) * (z * x)
;; Stevens' challenge problem.
 asso((x * y), z, w) + asso(x, y, comm(z, w)) == (x * asso(y, z, w)) + (asso(x, z, w) * y)

n

; Number of rules generated             = 84
; Number of rules retained              = 35
; Number of critical pairs              = 1516
; Time used (incl. garbage collection)  = 25.170 sec
;  Time spent in normalization          = 12.200 sec  (48.47 %)
;  Time spent in unification            = 4.270 sec  (16.96 %)
;  Time spent in ordering               = 0.270 sec  (1.07 %)
;  Time spent in simplifying the rules  = 8.430 sec  (33.49 %)
;  Time spent in flattening terms       = 6.040 sec  (24.00 %)
; Done at: 14:8:21 May 31 1991

