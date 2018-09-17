;; This file contains RRL's commands for a little problem proposed
;; by Bob Boyer in May 27, 1992.

;;;; Here's a little challenge problem that Moore and I got from
;;;; McCarthy in 1977.  I'd like to see how your system handles it
;;;; sometime.  The only point of the exercise is that there is no obvious
;;;; `constructor' that corresponds with the `destructor' GOPHER in the
;;;; definition of SAMEFRINGE.  The `obvious' induction is the one
;;;; suggested by the definition of SAMEFRINGE.  Maybe this is old hat for
;;;; you.
;;;; 
;;;; See you at CADE.
;;;; 
;;;; Bob

init

option prove e

add
;; the constructors for the data list. 
[ null : list] ;; the empty list.
[ atom : univ -> list] ;; anything wrapped by ATOM is a singleton list.
[ cons : list, list -> list] ;; a pair of lists is a list.

[ append : list, list -> list]
append(null, y) := y
append(atom(x), y) := cons(atom(x), y)
append(cons(x, y), z) := cons(x, append(y, z)) 

[ flatten : list -> list ]
flatten(null) := cons(null, null)
flatten(atom(x)) := atom(x)
flatten(cons(x, y)) := append(flatten(x), flatten(y))

[mcflatten : list, list -> list]
mcflatten(null, z) := cons(null, z)
mcflatten(atom(x), z) := cons(atom(x), z)
mcflatten(cons(null, y), z) := cons(null, mcflatten(y, z))
mcflatten(cons(atom(x), y), z) := cons(atom(x), mcflatten(y, z))
mcflatten(cons(cons(x, u), y), z) := mcflatten(cons(x, cons(u, y)), z)
]

operator
constructor
null atom cons
y
y

operator status cons lr
operator status append lr

operator precedence mcflatten flatten append

makerule

prove
mcflatten(x, y) == append(flatten(x), y)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  gopher and samefringe
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
add
[ car : list -> list]
car(null) := null
car(atom(x)) := null
car(cons(x, y)) := x

[ cdr : list -> list]
cdr(null) := null
cdr(atom(x)) := null
cdr(cons(x, y)) := y

[ consp : list -> bool]  ;; consp(x) == (not (nlisp x))
consp(null) := false
consp(atom(x)) := false
consp(cons(x, y)) := true

[ gopher : list -> list]
gopher(null) := null
gopher(atom(x)) := atom(x)
gopher(cons(null, y)) := cons(null, y)
gopher(cons(atom(x), y)) := cons(atom(x), y)
gopher(cons(cons(x, u), y)) := gopher(cons(x, cons(u, y)))

[ samefringe : list, list -> bool]
samefringe(x, null) := (x = null)
samefringe(null, x) := (x = null)
samefringe(y, atom(x)) := (y = atom(x))
samefringe(atom(x), y) := (y = atom(x))
samefringe(cons(x1, y1), cons(x2, y2)) :=
   (car(gopher(cons(x1, y1))) = (car(gopher(cons(x2, y2))))) and
   samefringe(cdr(gopher(cons(x1, y1))), cdr(gopher(cons(x2, y2))))
]

operator precedence samefringe gopher mcflatten cdr car consp

makerule

lr y ;; orient the last equation of samefringe from left-to-right.

;; the next five lemmas are used in the base cases of the major theorem.
prove
(append(x, y) = null) == (x = null) and (y = null)

prove
(append(z, z1) = cons(null, null)) == false  if  
         not((cons(null, null) = z)) and
         not((cons(null, null) = z1)) 

prove
(append(x, y) = atom(x1)) == false if not(x = null)

prove
flatten(x) = cons(null, null) == false if not(x = null)

prove
(flatten(x) = atom(x1)) == (atom(x1) = x)

prove
append(append(x, y), z) == append(x, append(y, z))

prove
consp(flatten(x)) if consp(x)

prove
(car(x) = car(y)) and (cdr(x) = cdr(y)) == (x = y) if consp(x) and consp(y)

;; next two lemmas show the relationship between gopher and flatten:
prove
car(gopher(x)) == car(flatten(x))

prove
flatten(cdr(gopher(x))) == cdr(flatten(x)) if consp(x)

;; major theorem
prove
samefringe(x, y) == flatten(x) = flatten(y)

