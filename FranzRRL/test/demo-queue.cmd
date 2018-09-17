init
option
prove
e
add

;; `cond' stands for the three-place if function.
[cond: bool, univ, univ -> univ]
cond(true, x, y) == x
cond(false, x, y) == y
cond(x, y, y) == y

;; equations for circular lists of numbers.
[create : clist]
[insert : clist, univ -> clist]

[isempty : clist -> bool]
isempty(create) := true
isempty(insert(x, y)) := false

[delete: clist -> clist]
delete(create) := create
delete(insert(x, y)) := x

[avalue : clist -> univ]
avalue(insert(x, y)) := y

[right : clist -> clist]
right(create) := create
right(insert(create, x)) := insert(create, x)
right(insert(insert(x, y), z)) := insert(right(insert(x, z)), y)

[join : clist, clist -> clist]
join(x, create) := x
join(x, insert(y, z)) := insert(join(x, y), z)

[qrep : clist -> queue]

[newq : queue]
newq == qrep(create)

[addq : queue, univ -> queue]
addq(qrep(x), y) == qrep(right(insert(x, y)))

[deleteq : queue -> queue]
deleteq(qrep(x)) == qrep(delete(x))

[frontq : queue -> univ]
frontq(qrep(x)) == avalue(x)

[isnewq : queue -> bool]
isnewq(qrep(x)) == isempty(x)

[appendq : queue, queue -> queue]
appendq(qrep(x), qrep(y)) == qrep(join(y, x))

]


option
ordering
l

operator
constructor
create insert qrep
y
y

makerule
1
1 3
1 3
1
1

prove
isnewq(newq)

prove
isnewq(addq(qrep(x), y)) == false


prove
deleteq(newq) == newq

prove
deleteq(addq(qrep(x), y)) == cond(isnewq(qrep(x)), newq, addq(deleteq(qrep(x)), y))
1

prove
frontq(addq(qrep(x), y)) == cond(isnewq(qrep(x)), y, frontq(qrep(x)))
1 3

prove
appendq(qrep(x), newq) == qrep(x)


prove
appendq(qrep(x), addq(qrep(y), z)) == addq(appendq(qrep(x), qrep(y)), z)
2
