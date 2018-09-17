init
option
prove
e
add
[ 0 : num]
[ suc : num -> num]
[ + : num, num -> num]
[ * : num, num -> num]
1 == suc(0)
2 == suc(suc(0))
x + 0 := x
x + suc(y) := suc(x + y)
x * 0 := 0
x * suc(y) := x + x * y
[gcd : num, num -> num]
gcd(x, 0) := x
gcd(0, y) := y
gcd(x + y, y) := gcd(x, y)
gcd(x, x + y) := gcd(x, y)
]
opera
prec
gcd * + 
oper
constructor
0 suc
y
make
prove
x+y == y+x

prove
gcd(x, y) == gcd(y, x)

prove
(x+y)+z == y+x+z

prove
*(x, y) == *(y, x)

prove
x*(y+z) == (x*y)+(x*z)

prove
gcd((x * z), (y * z)) == (z * gcd(x, y))

add
[nl : list]
[cons : univ, list -> list]
[append : list, list -> list]
append(nl, y) := y
append(cons(x, y), z) := cons(x, append(y, z)) 
]
oper
constructor
nl cons
y
opera
status
append
lr
make

prove
append(append(x, y), z) == append(x, append(y, z)) 

add
[append1: list, univ -> list]
[length : list -> num]
append1(nl, x) := cons(x, nl)
append1(cons(y, z), x) := cons(y, append1(z, x))
length(cons(y, z)) := suc(length(z))
]
make
prove
length(append1(y, x)) := suc(length(y))




