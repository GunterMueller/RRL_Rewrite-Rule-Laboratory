;; This file contains RRL's commands for proving the Chinese remainder theorem.

init
option prove e

add
;; the constructors for the naturals:
[ 0 : num]
[ suc : num -> num]

1 == suc(0)

[ + : num, num -> num]
x + 0 := x
x + suc(y) := suc(x + y)

[ * : num, num -> num]
x * 0 := 0
x * suc(y) := x + x * y

[< : num, num -> bool]
0 < suc(x) := true
x < 0 := false
suc(x) < suc(y) := x < y

[sub1 : num -> num]
sub1(0) := 0
sub1(suc(x)) := x

[- : num, num -> num]
0 - x := 0
x - 0 := x
suc(x) - suc(y) := x - y

[div : num, num -> num]
div(x, 0) := 0
div(x, y) := 0 if x < y
div(y + x, y) := suc(div(x, y)) if not(0 = y)

[rem : num, num -> num]
rem(x, 0) := x
rem(x, y) := x if x < y
rem(y + x, y) := rem(x, y)

[divides : num, num -> bool]
divides(x, y) := rem(y,x) = 0

;; the constructors for the lists.
[null : list]
[cons : univ, list -> list]

[append : list, list -> list]
append(null, y) := y
append(cons(x, y), z) := cons(x, append(y, z)) 

[length : list -> num]
length(null) := 0
length(cons(x, y)) := suc(length(y))

[delete : univ, list -> list]
delete(x, null) := null
delete(x, cons(y, z)) := cond((x = y), z, cons(y, delete(x, z)))

[prime1 : num, num -> bool]
;; prime1(x, y) returns true iff for any 0 < z <= y, not(z | x).
prime1(x, 0) := false
prime1(x, suc(0)) := true
prime1(x, suc(y)) := cond(divides(suc(y), x), false, prime1(x,y)) if not(y = 0)

[prime : num -> bool]
prime(0) := false
prime(suc(x)) := prime1(suc(x), x) 

[primelist : list -> bool]
primelist(null) := true
primelist(cons(x, y)) := cond(prime(x), primelist(y), false)

[products : list -> num]
products(null) := suc(0)
products(cons(x, y)) := x * products(y)

[primefacs : num -> list]
primefacs(0) := null
primefacs(suc(0)) := null
primefacs(suc(suc(x))) := cons(suc(suc(x)), null) if prime(suc(suc(x)))
primefacs(x * y) := append(primefacs(x), primefacs(y)) if not(x = 0) and not(y = 0)

[member : univ, list -> bool]
member(x, null) := false
member(x, cons(y, z)) := cond((x = y), true, member(x, z))

[sublist : list, list -> bool]
sublist(null, x) := true
sublist(cons(x, y), null) := false
sublist(cons(x, y), z) := cond(member(x, z), sublist(y, delete(x, z)), false)

[nocommon : list, list -> bool]
nocommon(null, x) := true
nocommon(cons(x, y), z) := cond(member(x, z), false, nocommon(y, z))

[prime2 : num, num -> bool]
prime2(x, y) := nocommon(primefacs(x), primefacs(y))
] ;; end of input

operator constructor
0 suc null cons
y
y

operator
precedence
prime2 primefacs products primelist prime prime1 nocommon sublist length member delete append divides rem div - sub1 < * + cond

operator status sublist lr

makerule

namerule prime2-def

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; the following lemmas are taken from prime.cmd
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

prove
div(0, y) == 0

y
y
y

prove
rem(0, y) == 0

kb

prove
x + y == y + x

prove
(x + y) + z == x + (y + z)

prove
(y * div(y + x, y)) == (y * suc(div(x, y)))

prove
(rem(x, y) + (y * div(x, y))) == x

prove
(y * div(x, y)) == x if divides(y, x)

prove
(x * (y + z)) == ((x * y) + (x * z))

prove
(x * y) * z == x * (y * z)

stat * l

prove
x * y == y * x 

prove
0 < x == not(x = 0)

prove
x < suc(0) == x = 0

prove
y < suc(y)

prove
(x + y) = 0 == (x = 0) and (y = 0)

prove
(x + y) = y == (x = 0)

prove
(x + z) = (y + z) == (x = y)

prove
(x * y) = 0 == (x = 0) or (y = 0)

prove
div((x * y), x) == y if not((x = 0))

prove
rem((y * x), x) == 0

prove
rem((u * y), x) == 0 if divides(x, u) and not(x = 0)

prove
rem(x + y,z) = rem(x, z) if divides(z, y)
exit

prove
delete(x, y) == y if not member(x, y)

prove
divides(x, products(y)) == true if member(x, y)

prove
primelist(delete(x, y)) if primelist(y)

prove 
div(z + y, x) == div(z, x) + div(y, x) if divides(x, z) and not(x = 0)
exit

prove
div(z * y, x) == y * div(z, x) if divides(x, z) and not(x = 0)

prove
products(delete(x, y)) == div(products(y), x) if (not((x = 0)) and member(x, y))

prove
products(x) = 0 == false if primelist(x)

prove
primelist(append(z, z1)) if primelist(z) and primelist(z1)

prove
rem(suc(0), x) == suc(0) if not(x = suc(0))

prove 
suc(x) < y if (x < y) and not(suc(x) = y)

prove
products(primefacs(x)) == x if not(x = 0)

prove
primelist(primefacs(x)) if not(x = 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Below are new lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

prove
append(x, null) == x

;;; lemmas about nocommon

prove
nocommon(x, null)

prove
nocommon(x, cons(y, z)) == not(member(y, x)) if nocommon(x, z)

prove
nocommon(x, cons(y, z)) == false if not nocommon(x, z)

prove
nocommon(x, cons(y, z)) == cond(member(y, x), false, nocommon(x, z))

prove
nocommon(y, append(x1, x2)) == cond(nocommon(y, x1), nocommon(y, x2), false)

prove
nocommon(append(x1, x2), y) == cond(nocommon(x1, y), nocommon(x2, y), false)

;;; lemmas about delete
prove
member(x, delete(x1, z)) == false if (not(member(x, z)))

prove
member(x, delete(x1, z)) == member(x, z) if not(x = x1)

prove
delete(x1, delete(x, z)) == delete(x, delete(x1, z))
nored

namerule delete-comm

;; lemmas about sublist

prove
sublist(y, delete(x, z)) == sublist(y, z) if not member(x, y)
restart
10
old-rule
delete-comm
exit

prove
sublist(y, delete(x, z)) == false if not sublist(y, z)
restart
6
old-rule
delete-comm
exit

prove
sublist(append(x, y), z) if sublist(x, z) and sublist(y, z) and nocommon(x, y) and 
                            hint(induc(sublist(x, z)))

prove
sublist(x, append(x, y))

prove
sublist(x, append(y, x))

prove
sublist(primefacs(x), primefacs(y)) if (rem(y, x) = 0) and not(x = 0) and not(y = 0)

prove
rem(x, (x1 * y)) == 0 if (rem(div(x, x1), y) = 0) and not(x1 = 0) and not(y = 0) and (rem(x, x1) = 0)

prove
rem(products(x), products(y)) == 0 if sublist(y, x) and not(products(y) = 0)

prove
sublist(append(primefacs(x1), primefacs(x2)), primefacs(y)) if
      nocommon(primefacs(x1), primefacs(x2)) and
      (rem(y, x1) = 0) and (rem(y, x2) = 0) and
      not(x1 = 0) and not(x2 = 0) and not(y = 0)
y

prove
rem(products(y), products(append(x1, x2))) == 0 if 
      not(products(append(x1, x2)) = 0) and nocommon(x1, x2) and 
      sublist(x1, y) and sublist(x2, y)
y

prove
products(append(x1, x2)) == products(x1) * products(x2)

prove
rem(products(primefacs(y)), products(append(primefacs(x1), primefacs(x2)))) == 0 if 
      prime2(x1, x2) and 
      sublist(primefacs(x1), primefacs(y)) and 
      sublist(primefacs(x2), primefacs(y)) and
      not(x1 = 0) and not(x2 = 0) and not(y = 0) 
y

prove
;;; an important lemma.
rem(y, x1 * x2) == 0 if
     not(x1 = 0) and not(x2 = 0) and not(y = 0) and
     prime2(x1, x2) and (rem(y, x1) = 0) and (rem(y, x2) = 0)
y

prove
prime2(x, suc(0)) if not((0 = x))
n
y

prove
prime2(x, y * z) if prime2(x, y) and prime2(x, z) and not(y = 0) and not(z = 0)
n
y

disable prime2-def

prove
not (x < x)

prove
y < suc(z) if y < z

prove
x < suc(y) == x = y if not(x < y)

prove
rem(x, suc(0)) == 0
n
restart
3
new-rule
suc(x) == (suc(0) + x)
exit

prove
suc(x) == (suc(0) + x)
n
n

prove
(x1 + x2) - x1 == x2

prove
(x1 + x2) - (x1 + x3) == (x2 - x3)

prove
(y * x1) - (y * x2) == y * (x1 - x2)

prove
rem((x1 - ((y * z) + rem(x1, y))), y) == 0
y

prove
rem(x1 - x2, y) == 0 if (rem(x1, y) = rem(x2, y)) 

prove
not(suc(x) < y) if not(x < y)

prove
(x1 - x2) < y if (x1 < y) and (x2 < y)

prove
not((x1 - x2) = 0) if x2 < x1

prove
not(rem(x1 - x2, y) = 0) if (x1 < y) and (x2 < y) and (x2 < x1)
n
y

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; try to prove the case 2 of the Chinese remainder theorem.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

add
[mp : univ, univ -> pair]
[first : pair -> univ]
[second : pair -> univ]
first(mp(x, y)) == x
second(mp(x, y)) == y

;; distinct(xlist) returns true iff all elements of xlist are distinct.
;; A set is represented by a list of distinct elements.
[distinct : list -> bool]
distinct(null) := true
distinct(cons(x, y)) := not(member(x, y)) and distinct(y)

[subset : list, list -> bool]
subset(null, w) := true
subset(cons(x, u), w) := member(x, w) and subset(u, w)

[index : univ, list -> num]
; index(x, l) returns the position of "x" in "l" (couting
; from right to left of "l" with the position of the rightmost being 0.)
index(x, null) := 0
index(x, cons(y, xl)) := cond((x = y), length(xl), index(x, xl))

[enum1 : num, num -> list]
enum1(xm, 0) :=  null
enum1(xm, suc(xn)) := cons(mp(xm, xn), enum1(xm, xn))

[enum : num, num -> list]
enum(0, xm) := null
enum(suc(xn), xm) := append(enum1(xn, xm), enum(xn, xm))

[pairrem : num, num, num -> pair]
pairrem(xn, xm1, xm2) == mp(rem(xn, xm1), rem(xn, xm2))

[pairrems : num, num, num -> list]
pairrems(0, xm1, xm2) := null
pairrems(suc(xn), xm1, xm2) := cons(pairrem(xn, xm1, xm2), pairrems(xn, xm1, xm2))

[sol2 : num, num, num, num -> num]
;; sol2 is a solution of Chinese remainder theorem of case 2.
sol2(xm1, xa1, xm2, xa2) := index(mp(xa1, xa2), pairrems(xm1 * xm2, xm1, xm2))
]

operator const mp
y

operator status subset rl

operator precedence sol2 index pairrems enum enum1 pairrem subset distinct length rem first second mp

makerule

namerule sol2-def

prove
length(append(x, y)) == length(x) + length(y)

prove
length(enum1(xm1, xm2)) == xm2

prove
length(enum(xm1, xm2)) == xm1 * xm2

prove
distinct(append(x, y)) == distinct(y) if distinct(x) and nocommon(x, y)

prove
not member(mp(x1, y), enum1(x2, z)) if not(y < z)

prove
not member(mp(x1, y), enum1(x2, z)) if x2 < x1

prove
distinct(enum1(x1, xm2))

prove
nocommon(enum1(x, z), enum1(y, z)) if not(x = y)

prove
nocommon(enum1(x, xm2), enum(y, xm2)) if not(x < y)

prove
distinct(enum(xm1, xm2))

prove
member(mp(x1, x2), enum1(x1, xm2)) if (x2 < xm2)

prove
member(x, append(y, z)) if member(x, z)

prove
subset(x, cons(y, z)) if subset(x, z)

prove
member(x, v)  if subset(u, v) and member(x, u)

prove
member(mp(x1, x2), enum(xm1, xm2)) if (x1 < xm1) and (x2 < xm2)

prove
rem(x, y) < y if not(y = 0)
n

prove
index(x, xl) < length(xl) if member(x, xl)

prove
subset(pairrems(xn, xm1, xm2), enum(xm1, xm2)) if not(xm1 = 0) and not(xm2 = 0)

;;; prove pigeonhole lemma.
prove
length(delete(x, v)) == sub1(length(v))  if member(x, v)

prove
subset(y1, delete(x, y2)) if subset(y1, y2) and not member(x, y1)

prove
subset(delete(x, v), y) == subset(v, cons(x, y))  if distinct(v)
namerule subset-delete

prove
subset(y, delete(x, v))  if subset(cons(x, y), v) and distinct(cons(x, y)) and distinct(v)
y

prove
distinct(delete(x,v)) if distinct(v)

prove
subset(v, u) if subset(u, v) and distinct(u) and distinct(v) and (length(u) = length(v))
exit
y
;; end of pigeonhole lemma.

;;; Try to prove this lemma:
;; distinct(pairrems(xn, xm1, xm2)) if not((xm1 * xm2) < xn) and prime2(xm1, xm2)

prove
; do we need this lemma ?
rem(y1 - y2, x1 * x2) == 0 if
     prime2(x1, x2) and (rem(y1, x2) = rem(y2, x2)) and (rem(y1 - y2, x1) = 0)
y

prove
not (rem(y1, x2) = rem(y2, x2)) if
   not(rem(y1 - y2, x1 * x2) = 0) and
   prime2(x1, x2) and (rem(y1 - y2, x1) = 0)
y
namerule bridge1

prove
not (rem(y1, x2) = rem(y2, x2)) if
   ((y1 - y2) < (x1 * x2)) and not((y1 - y2) = 0) and
   prime2(x1, x2) and  (rem(y1 - y2, x1) = 0)
y
namerule bridge2

prove
not (rem(y1, x2) = rem(y2, x2)) if
   (y1 < (x1 * x2)) and (y2 < (x1 * x2)) and (y2 < y1) and
   prime2(x1, x2) and (rem(y1 - y2, x1) = 0)
n
y
namerule bridge3

delete rule bridge1 bridge2

prove
x < y if not(y < suc(x))

namerule bridge4

prove
x < y if suc(x) < y
n
y
namerule bridge5

prove
member(mp(rem(x, xm1), rem(x, xm2)), pairrems(y, xm1, xm2)) == false if 
          (y < (xm1 * xm2)) and not(x < y) and prime2(xm1, xm2) and 
          (x < (xm1 * xm2))
n
namerule bridge6

prove
;; the most time-consuming lemma.
distinct(pairrems(y, xm1, xm2)) if not((xm1 * xm2) < y) and prime2(xm1, xm2)

delete rule bridge3 bridge4 bridge5 bridge6
;; end of distinct-pairrems

prove
length(pairrems(x, y, z)) == x

prove
subset(enum(xm1, xm2), pairrems(xm1 * xm2, xm1, xm2)) if 
       prime2(xm1, xm2) and not(xm1 = 0) and not(xm2 = 0)
y

prove
member(mp(x1, x2), pairrems(xm1 * xm2, xm1, xm2)) if 
      (x1 < xm1) and (x2 < xm2) and
       subset(enum(xm1, xm2), pairrems(xm1 * xm2, xm1, xm2)) 
y

prove
member(mp(x1, x2), pairrems(xm1 * xm2, xm1, xm2)) if 
      (x1 < xm1) and (x2 < xm2) and prime2(xm1, xm2)
y

prove
rem(index(mp(x1, x2), pairrems(xn, xm1, xm2)), xm1) == x1 if 
      member(mp(x1, x2), pairrems(xn, xm1, xm2))

prove
rem(index(mp(x1, x2), pairrems(xn, xm1, xm2)), xm2) == x2 if 
      member(mp(x1, x2), pairrems(xn, xm1, xm2))

prove
sol2(xm1, xa1, xm2, xa2) < length(pairrems(xm1 * xm2, xm1, xm2)) if (xa1 < xm1) and (xa2 < xm2) and prime2(xm1, xm2)
y

prove
;; minor theorem 1
rem(sol2(xm1, xa1, xm2, xa2), xm1) == xa1 if (xa1 < xm1) and (xa2 < xm2) and prime2(xm1, xm2)
n
y

prove
;; minor theorem 2
rem(sol2(xm1, xa1, xm2, xa2), xm2) == xa2 if (xa1 < xm1) and (xa2 < xm2) and prime2(xm1, xm2)
n
y

prove
;; minor theorem 3
sol2(xm1, xa1, xm2, xa2) < (xm1 * xm2) if (xa1 < xm1) and (xa2 < xm2) and prime2(xm1, xm2)
n
y

disable sol2-def

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Now, after case 2 is done, prove the general case.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

add
[prime2list : num, list -> bool]
prime2list(x, null) := true
prime2list(x, cons(y, z)) := prime2(x, first(y)) and prime2list(x, z)

[allprime2 : list -> bool]
allprime2(null) := true
allprime2(cons(y, z)) := prime2list(first(y), z) and allprime2(z)

[positivep : list -> bool]
positivep(null) := true
positivep(cons(y, z)) := (0 < first(y)) and positivep(z)

[allless : list -> bool]
allless(null) := true
allless(cons(y, z)) := (second(y) < first(y)) and allless(z)

[products1 : list -> num]
products1(null) := suc(0)
products1(cons(x, y)) := first(x) * products1(y)

[soln : list -> num]
;; soln is a solution of Chinese remainder theorem of case n.
soln(null) := 0
soln(cons(y, z)) := sol2(first(y), second(y), products1(z), soln(z))

[remainders : num, list -> bool]
remainders(x, null) := true
remainders(x, cons(y, z)) := (rem(x, first(y)) = second(y)) and remainders(x, z)
]

operator precedence soln sol2 remainders allprime2 allless positivep prime2list products1 prime2 

makerule

prove
0 < products1(y) if positivep(y)

prove
;;; major theorem 1:
prime2(x, products1(y)) if allprime2(y) and prime2list(x, y) and positivep(y) and not(x = 0)

prove
;;; major theorem 2:
soln(y) < products1(y) if positivep(y) and allless(y) and allprime2(y) 

prove
;;; major theorem 3: solutions are infinite.
remainders(v + (u * products1(z)), z) == true if 
          (allless(z)) and 
          (allprime2(z)) and 
          (positivep(z)) and 
          (remainders(v, z))

prove
remainders(u, z) == true if 
          (allless(z)) and 
          (allprime2(z)) and 
          (positivep(z)) and 
          (remainders(rem(u, products1(z)), z))

prove
rem(sol2(first(y), second(y), products1(z), soln(z)), products1(z)) == soln(z) if 
          positivep(z) and allless(z) and allprime2(z) and
          ((second(y) < first(y))) and 
          prime2list(first(y), z) and not(first(y) = 0)
y

prove
;;; major theorem 4: soln(y) is a solution.
remainders(soln(y), y) if positivep(y) and allless(y) and allprime2(y) 

prove
;; major theorem 5: ;; the solution is unique modulo products1(y).
rem(x1 - x2, products1(y)) == 0 if 
     positivep(y) and allless(y) and allprime2(y) and 
     remainders(x1, y) and remainders(x2, y) 

list


