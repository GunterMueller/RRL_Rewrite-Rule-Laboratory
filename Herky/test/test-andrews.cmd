;;; Andrews' challenge problem.
add
not(((exist x (all y (p(x) equ p(y)))) equ 
  ((exist x r(x)) equ (all y p(y)))) equ 
    ((exist x (all y (r(x) equ r(y)))) equ 
  ((exist x p(x)) equ (all y r(y)))))
]
kb

; Number of rules generated             = 45
; Number of rules retained              = 16
; Number of critical pairs              = 78
; Time used (inc. garbage collection)   = 2.830 sec
;  Time spent in normalization          = 0.580 sec  (20.49 %)
;  Time spent in unification            = 1.010 sec  (35.69 %)
;  Time spent in ordering               = 0.120 sec  (4.24 %)
;  Time spent in simplifying the rules  = 1.120 sec  (39.58 %)
;  Time spent in flattening terms       = 2.130 sec  (75.27 %)
