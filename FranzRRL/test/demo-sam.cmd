init
option
prove
c
option
crtical
unit
3
option
norm
depth
1
option
reduce
0
option
order
s
add
max(x, 1) == 1
max(x, x) == x
max(x, 0) == x
min(0, x) == 0
min(1, x) == x
min(x, x) == x
min(x, z) == x if z = max(x, y)
max(x, y1) == min(z, x1) if (min(x, z) = x) and (max(x, y) = x1) and 
   (min(y, z) = y1)
max(x, z) = x if z = min(x, y)
max(a, b) == d1
min(a, b) == d2
min(d1, c1) == 0
min(d2, c2) == 0
min(c2, b) == e
min(c2, a) == f
max(c1, e) == g
max(c1, f) == h
min(g, h) = c1 == false
]
option
support
6 7 8 10 11 12 14 16
oper
prec
max min a b e d1 d2 c1 c2 f g h 1 0
oper
ac
min max
akb
