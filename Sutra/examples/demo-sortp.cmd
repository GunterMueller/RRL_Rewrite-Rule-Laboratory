init
option
prove
e
add
;; equations for numbers.
[ 0 : num]
[ suc : num -> num]

[ + : num, num -> num]
x + 0 := x
x + suc(y) := suc(x + y)

[filter1 : num, num -> bool]
[filter2 : num, num -> bool]
filter1(x, y) == false if filter1(y, x)
filter2(x, y) == false if filter2(y, x)
filter1(x, y) == false if filter2(y, x)
filter2(x, y) == false if filter1(y, x)

;; shouldnot this follow from the above rule?
filter1(x, x) == false 
filter2(x, x) == false 

[< : num, num -> bool]
0 < suc(x) := true
x < 0 := false
suc(x) < suc(y) := x < y

;; cond stands for the three-place if function.
[cond : bool, univ, univ -> univ]
cond(true, x, y) == x
cond(false, x, y) == y
cond(x, y, y) == y
;cond(not(x), y, z) == cond(x, z, y)

;; equations for lists of numbers.
[nl : list]
[cons : univ, list -> list]
[append : list, list -> list]
append(nl, y) := y
append(cons(x, y), z) := cons(x, append(y, z)) 

[spilt : num, list -> list]
split(xa, nl) := nl
split(xa, cons(ya, x)) := 
	cond((ya filter1 xa), cons(ya, split(xa, x)), split(xa, x))

[allp : num, list -> bool]
allp(xa, nl) := true
allp(xa, cons(ya, x)) := cond((xa filter2 ya), false, allp(xa, x))

[occur : num, list -> num]
occur(xa, nl) := 0
occur(xa, cons(ya, x)) := cond((xa = ya), suc(occur(xa, x)), occur(xa, x))

option
ordering
l
oper
constructor
0 suc nl cons
y
y
makerule
1 2 
1 2 
1 2 
1 2
left_to_right
y
1 2

prove
0 + x == x

prove
allp(xa, append(x, y)) == allp(xa, x) and allp(xa, y)

prove
allp(xa, split(ya, x)) == true if allp(xa, x)

prove
allp(xa, split(xa, x)) == true

prove
allp(xa, qsort(x)) == true if allp(xa, x)

prove
occur(xa, append(x, y)) == occur(xa, x) + occur(xa, y)
1 3 6 

prove
occur(xa, split(xb, x)) == cond((xa filter1 xb), occur(xa, x), 0)
1 4

;;; I do not know why I wrote the thing below

prove
occur(xa, split(xb, x)) == cond((xa filter2 xb), 0, occur(xa, x))
1 4


