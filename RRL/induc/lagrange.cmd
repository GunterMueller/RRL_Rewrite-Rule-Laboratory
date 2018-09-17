;; This file contains RRL's commands for proving Lagrange's theorem in group theory:
;;   for any finite group, the order of any subgroup divides the order of the group.

init

add
[ * : G, G -> G ]
[ i : G -> G ]
[ e : G ]
(x * e) == x
(x * i(x)) == e
(x * (y * z)) == (x * y) * z
]

operator prece
i * e

operator status * lr

kb 
;; the Knuth-Bendix completion generates a canonical system.

option prove e ;; choose the cover set indcution method.

add
[ 0 : num]
[ suc : num -> num]

[ + : num, num -> num]
x + 0 := x
x + suc(y) := suc(x + y)

[sub1 : num -> num]
sub1(0) := 0
sub1(suc(x)) := x

[- : num, num -> num]
0 - x := 0
x - 0 := x
suc(x) - suc(y) := x - y

[=< : num, num -> bool]
0 =< x := true
suc(x) =< 0 := false
suc(x) =< suc(y) := x =< y

[rem : num, num -> num]
rem(x, 0) := x
rem(x, y) := x if not(y =< x)
rem(y + x, y) := rem(x, y)

[divide : num, num -> bool]
divide(x, y) := rem(y,x) = 0

;; data type "set"
[ empty : set ]
[ insert : G, set -> set ]

[length : set -> num]
length(empty) := 0
length(insert(x, y)) := suc(length(y))

[member : G, set -> bool]
member(x, empty) := false
member(x, insert(y, z)) := cond((x = y), true, member(x, z))

[delete : G, set -> set]
delete(x, empty) := empty
delete(x, insert(y, z)) := cond((x = y), z, insert(y, delete(x, z)))

[set_minus : set, set -> set]
set_minus(empty, X) := empty
set_minus(insert(x, Y), Z) := cond(member(x, Z), set_minus(Y, Z), insert(x, set_minus(Y, Z)))
]

operator
constructor
e 0 suc empty insert
y
y

operator
precedence
set_minus length member delete divide rem =< i * - + sub1 cond

makerule

namerule
minus2

add
[distinct : set -> bool]
distinct(empty) := true
distinct(insert(x, y)) := cond(member(x, y), false, distinct(y))

[subsetp : set, set -> bool]
subsetp(empty, w) := true
subsetp(insert(x, y), w) := cond(member(x, w), subsetp(y, w), false)

[lcoset : G, set -> set ]
lcoset(x, empty) := empty
lcoset(x, insert(y, Z)) := insert((y * x), lcoset(x, Z))

[closed : set, set -> bool]
member((x1 * x2), Y2) if closed(Y1, Y2) and member(x1, Y1) and member(x2, Y2)
closed(Y1, Y2) if not member(s1(Y1, Y2), Y1)
closed(Y1, Y2) if not member(s2(Y1, Y2), Y2)
closed(Y1, Y2) if member(s1(Y1, Y2) * s2(Y1, Y2), Y2)

[subG : set -> bool ]
member(e, Y) if subG(Y)
member(i(x), Y) if subG(Y) and member(x, Y)
member(x1 * x2, Y) if subG(Y) and member(x1, Y) and member(x2, Y)

[subgroup : set, set -> bool]
subgroup(Y1, Y2) := subg(y1) and subg(y2) and subsetp(y1, y2)

]

operator status subsetp rl

operator
precedence
subgroup subG closed lcoset distinct subsetp set_minus

makerule

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lemmas about arithmetics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
prove
x =< x + y

y

prove
x - suc(y) == sub1(x - y)

prove
suc(x) - y == suc(x - y) if y =< x

prove
(y + x) - y == x

prove
suc(x) =< y if (x =< sub1(y)) and (suc(0) =< y)

prove
x =< suc(y) if sub1(x) =< y

prove
suc(sub1(x)) == x if suc(0) =< x

prove
rem(x, y) == 0 if (rem(x - y, y) = 0) and (y =< x) and (suc(0) =< y)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lemmas about delete
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

prove
delete(x, w) = w if not member(x, w)

prove
not member(x, delete(x1, y)) if not member(x, y)

prove
distinct(delete(x,v)) if distinct(v)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lemmas about subsetp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

prove
subsetp(x, empty) == (x = empty)

prove
subsetp(Y1, insert(x, Y2)) if subsetp(Y1, Y2)

prove
subsetp(Y, Y)

prove
member(x, Y) if subsetp(Y1, Y) and member(x, Y1)

prove
subsetp(Y1, insert(x, Y)) == subsetp(Y1, Y) if not member(x, Y1)

prove
subsetp(v, insert(x, y)) == subsetp(delete(x, v), y)  if distinct(v)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lemmas about length
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

prove
suc(0) =< length(Y) if member(x, Y)

prove
suc(0) =< length(X) if member(e, X)
n
y

prove
length(delete(x, Y)) == sub1(length(Y)) if member(x, Y)

add
[induc1 : set, set  -> bool]
induc1(v, empty) := true
induc1(v, insert(x, w)) := induc1(delete(x, v), w) if member(x, v)
induc1(v, insert(x, w)) := induc1(delete(x, v), w) if not member(x, v)
]
operator status induc1 rl

operator prece 
induc1 delete

makerule

prove
length(Y1) =< length(Y2) if subsetp(Y1, Y2) and distinct(Y1) and hint(induc(induc1(Y1, Y2)))

y

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lemmas about set_minus
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

prove
set_minus(X, empty) == X

prove
member(x, set_minus(Y, Y1)) == cond(member(x, Y), not(member(x, Y1)), false)

prove
distinct(set_minus(X, Y)) if distinct(X)

prove
set_minus(Y1, insert(x, Y2)) == delete(x, set_minus(Y1, Y2)) if distinct(Y1) 

prove
length(set_minus(Y2, Y1)) == length(Y2) - length(Y1) if distinct(Y1) and distinct(Y2) and subsetp(Y1, Y2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lemmas about lcoset
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

prove
not member(z, lcoset(x, Y))  if not member(z * i(x), Y) 

prove
distinct(lcoset(x, Y)) if distinct(Y)

prove
length(lcoset(x, y)) == length(y)

prove
not ((y1 * xb) = (x * xa)) if not member(xa, lcoset(xb, Y)) and member(i(x) * y1, Y) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lemmas with subG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

prove
suc(0) =< length(X) if subG(X)
n
y

prove
member(i(i(x)), Y) if subG(Y) and member(i(x), Y)
y

prove
member(i(y1) * y2, Y) if subG(Y) and member(y1, Y) and member(y2, Y)
n
y

prove
not member(x * xa, lcoset(xb, Y1)) if subG(Y) and member(x, Y) and subsetp(Y1, Y) and not member(xa, lcoset(xb, Y))

prove
not member(x * xa, lcoset(xb, Y)) if subG(Y) and member(x, Y) and not member(xa, lcoset(xb, Y))
n
y

prove
member(x1 * x2, y2) if subsetp(y1, y2) and subG(y2) and
   member(x1, y1) and member(x2, y2)
n
y

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lemmas about closed 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

prove
subsetp(lcoset(x, Y1), Y3) if closed(Y2, Y3) and member(x, Y1) and subsetp(Y2, Y3) and subsetp(Y1, Y2)

prove
closed(Y, set_minus(Y2, lcoset(xb, Y))) if subg(Y) and closed(Y, Y2) and
    hint(case(member(s1(Y, set_minus(Y2, lcoset(xb, Y))), Y))) and
    hint(case(member(s2(Y, set_minus(Y2, lcoset(xb, Y))), set_minus(Y2, lcoset(xb, Y)))))

prove
subsetp(lcoset(x, Y0), Y2) if subsetp(Y0, Y1) and closed(Y1, Y2) and member(x, Y2)

prove
length(lcoset(x, Y1)) =< length(insert(x, Y2)) if closed(Y1, insert(x, Y2)) and distinct(Y1)
y

prove
closed(y1, y2) if subsetp(y1, y2) and subG(y2) and
   hint(case(member(s1(y1, y2), y1))) and 
   hint(case(member(s2(y1, y2), y2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lemmas about lagrange theorem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

disable minus2

add
[ induct2 : set, set -> bool ]
induct2(empty, empty) := true
induct2(insert(x, y), empty) := true
;; there is a bug in computing don't-care positions!!!
;; Y1 appears in the second argument!
induct2(Y1, insert(x, Y2)) := induct2(Y1, set_minus(insert(x, Y2), lcoset(x, Y1)))
]

makerule
lr
y

prove
rem(length(Y2), length(Y1)) == 0 if subG(Y1) and distinct(Y1) and 
              distinct(Y2) and closed(Y1, Y2) and
              hint(induc(induct2(y1, y2)))

prove
divide(length(Y1), length(Y2)) if subgroup(Y1, Y2) and distinct(Y1) and distinct(Y2)
n
y

list
