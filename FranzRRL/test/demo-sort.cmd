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

[< : num, num -> bool]
0 < suc(x) := true
x < 0 := false
suc(x) < suc(y) := x < y

;; `cond' stands for the three-place if function.
[cond: bool, univ, univ -> univ]
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

[spilt_below : num, list -> list]
split_below(xa, nl) := nl
split_below(xa, cons(ya, x)) := 
	cond((ya < xa), cons(ya, split_below(xa, x)), split_below(xa, x))

[split_above: num, list -> list]
split_above(xa, nl) := nl
split_above(xa, cons(ya, x)) := 
	cond((ya < xa), split_above(xa, x), cons(ya, split_above(xa, x)))

[all_gte: num, list -> bool]
all_gte(xa, nl) := true
all_gte(xa, cons(ya, x)) := cond((xa < ya), false, all_gte(xa, x))

[all_lte: num, list -> bool]
all_lte(xa, nl) := true
all_lte(xa, cons(ya, x)) := cond((ya < xa), false, all_lte(xa, x))

[occur: num, list -> num]
occur(xa, nl) := 0
occur(xa, cons(ya, x)) := cond((xa = ya), suc(occur(xa, x)), occur(xa, x))

[qsort: list -> list]
qsort(nl) := nl
qsort(cons(xa, x)) := append(qsort(split_below(xa, x)),
                             cons(xa, qsort(split_above(xa, x))))

[sortedp: list -> bool]
sortedp(nl) := true
sortedp(cons(xa, nl)) := true
sortedp(cons(xa, cons(ya, x))) := cond((ya < xa), false, sortedp(cons(ya, x)))

]

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
1 2
1 2 3 
left_to_right
y
1 2 3 

prove
0 + x == x

prove
x < y == false if (y < x)


prove
all_gte(xa, append(x, y)) == all_gte(xa, x) and all_gte(xa, y)

prove
all_lte(xa, append(x, y)) == all_lte(xa, x) and all_lte(xa, y)

prove
all_gte(xa, split_below(ya, x)) == true if all_gte(xa, x)

prove
all_lte(xa, split_above(xb, x)) == true if all_lte(xa, x)

prove
all_lte(xa, split_below(xb, x)) == true if all_lte(xa, x)
y
y

prove
all_gte(xa, split_above(ya, x)) == true if all_gte(xa, x)

prove
all_gte(xa, split_below(xa, x)) == true


prove
all_lte(xa, split_above(xa, x)) == true


prove
all_lte(xa, qsort(x)) == true if all_lte(xa, x)
y
y

prove
all_gte(xa, qsort(x)) == true if all_gte(xa, x)


prove
sortedp(append(x, cons(xa, y))) == true if
    sortedp(x) and sortedp(y) and all_gte(xa, x) and all_lte(xa, y)


prove
sortedp(qsort(x))


prove
occur(xa, append(x, y)) == occur(xa, x) + occur(xa, y)
1 3 6 

prove
occur(xa, split_below(xb, x)) == cond((xa < xb), occur(xa, x), 0)
1 4

prove
occur(xa, split_above(xb, x)) == cond((xa < xb), 0, occur(xa, x))


prove
occur(xa, qsort(x)) == occur(xa, x)

