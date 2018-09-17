init
option
prove
e
add
[ 0 : num]
[ suc : num -> num]
[ pre : num -> num]
[ minus : num -> num]
pre(suc(x)) == x
suc(pre(x)) == x
minus(0) := 0
minus(pre(x)) := suc(minus(x))
minus(suc(x)) := pre(minus(x))
]
opera
prec
minus pre suc 0 
oper
constructor
0 suc pre
n
n
make
prove
minus(minus(x)) == x

 

