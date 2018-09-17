prove
0 + x == x
y
y

prove
allp(xa, append(x, y), xf) == allp(xa, x, xf) and allp(xa, y, xf)
y
y

prove
allp(xa, split(ya, x, xf1), xf2) == true if allp(xa, x, xf2)
y
y

prove
allp(xa, split(xa, x, xf), xf) == true
y
y

prove
allp(xa, qsort(x), xf) == true if allp(xa, x, xf)
y
y

prove
occur(xa, append(x, y)) == occur(xa, x) + occur(xa, y)
y
y
1 3 6 

prove
occur(xa, split(xb, x, xf)) == cond(eval(xf, xa, xb), occur(xa, x), 0)
y
y
1 4

add
eval(lt, xa, xa) := false
eval(lt, xa, ya) := false if eval(lt, ya, xa)
]
make

prove
sortedp(append(x, cons(xa, y))) == true if
    sortedp(x) and sortedp(y) and allp(xa, x, lt) and allp(xa, y, ge)
y
y

prove
sortedp(qsort(x))
y
y
prove
occur(xa, qsort(x)) == occur(xa, x)
y
y





