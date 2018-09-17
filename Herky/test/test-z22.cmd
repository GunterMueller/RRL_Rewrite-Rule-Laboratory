option critical unmarked q
option autoorder rule 10000 quit

add
a(a1(x)) == x
b(b1(x)) == x
c(c1(x)) == x
d(d1(x)) == x
e(e1(x)) == x

a1(a(x)) == x
b1(b(x)) == x
c1(c(x)) == x
d1(d(x)) == x
e1(e(x)) == x

a(b(c(x))) == d(x)
b(c(d(x))) == e(x)
c(d(e(x))) == a(x)
d(e(a(x))) == b(x)
e(a(b(x))) == c(x)
]

oper prec
e e1 d d1 c c1 b b1 a1 a 

kb

; SUTRA:
; Number of rules generated            = 1610
; Number of rules retained             = 10
; Number of critical pairs             = 882
; Time used                            = 1133.35 sec
; Time spent in normalization          = 290.48 sec  (25.0 percent of time)
; Time spent in unification            =   0.93 sec   (0.0 percent of time)
; Time spent in ordering               =  16.82 sec   (1.0 percent of time)
; Time spent in simplifying the rules  = 810.17 sec   (71.0 percent of time)
;
; Number of rules generated             = 1743
; Number of rules retained              = 10
; Number of critical pairs              = 730
; Time used (incl. garbage collection)  = 113.430 sec
;  Time spent in normalization          = 35.450 sec  (31.25 %)
;  Time spent in unification            = 2.910 sec  (2.57 %)
;  Time spent in ordering               = 7.770 sec  (6.85 %)
;  Time spent in simplifying the rules  = 67.300 sec  (59.33 %)
; Done at: 15:10:13 Jun 10 1991 on cookie
