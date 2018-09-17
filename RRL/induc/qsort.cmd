;; This file contains RRL's commands for verifying the quick-sort algorithm.

init

option prove e

add
;; equations for numbers.
[  0  :  num]
[  suc  :  num -> num]

[  +  :  num, num -> num]
x + 0  := x
x + suc(y)  := suc(x + y)

[ lt  :   mapping]
[ ge  :   mapping]

[ eval :  mapping, univ, univ -> bool]
eval(ge, xa, ya)  := not(eval(lt, xa, ya))
eval(lt, xa, ya)  := false if eval(lt, ya, xa)

;; equations for lists 
[ nl  :  list]
[ cons  :  univ, list -> list]
[ append  :  list, list -> list]
append(nl, y)  := y
append(cons(x, y), z)  := cons(x, append(y, z)) 

[ split  :  univ, list, mapping  -> list]
;; `cond' stands for the three-place if function.
split(xa, nl, xf)  := nl
split(xa, cons(ya, x), xf)  := 
	cond(eval(xf, ya, xa), cons(ya, split(xa, x, xf)), split(xa, x, xf))

[ allp :  univ, list, mapping -> bool]
allp(xa, nl, xf)  := true
allp(xa, cons(ya, x), xf)  := cond(eval(xf, ya, xa), allp(xa, x, xf), false)

[ occur :  univ, list -> num]
occur(xa, nl)  := 0
occur(xa, cons(ya, x))  := cond((xa = ya), suc(occur(xa, x)), occur(xa, x))

[ qsort :  list -> list]
qsort(nl)  := nl
qsort(cons(xa, x))  := append(qsort(split(xa, x, lt)),
                             cons(xa, qsort(split(xa, x, ge))))

[ sortedp :  list -> bool]
sortedp(nl)  := true
sortedp(cons(xa, nl))  := true
sortedp(cons(xa, cons(ya, x)))  := cond(eval(lt, ya, xa), false, sortedp(cons(ya, x)))

]

operator
constructor
0 suc nl cons
y
y

makerule
1
1 2 
1 2 
1 2
1 2
lr
y
1 2

prove
allp(xa, append(x, y), xf) == allp(xa, x, xf) and allp(xa, y, xf)

y

prove
allp(xa, split(ya, x, xf1), xf2) == true if allp(xa, x, xf2)

prove
allp(xa, split(xa, x, xf), xf) == true

prove
allp(xa, qsort(x), xf) == true if allp(xa, x, xf)

prove
occur(xa, append(x, y)) == occur(xa, x) + occur(xa, y)
1 3 6 

prove
occur(xa, split(xb, x, xf)) == cond(eval(xf, xa, xb), occur(xa, x), 0)
1 4

prove
sortedp(append(x, cons(xa, y))) == true if
    sortedp(x) and sortedp(y) and allp(xa, x, lt) and allp(xa, y, ge)
exit
y

prove
sortedp(qsort(x))

prove
occur(xa, qsort(x)) == occur(xa, x)


