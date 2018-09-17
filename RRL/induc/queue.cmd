;; This file contains a simple exercise of representing one abstract data type, queue,
;; by another one, clist.

init

option prove e

add

[create  :  clist]
[insert  :  clist, num -> clist]

[isempty  :  clist -> bool]
isempty(create)  := true
isempty(insert(x, y))  := false

[delete :  clist -> clist]
delete(create)  := create
delete(insert(x, y))  := x

[avalue  :  clist -> univ]
avalue(insert(x, y))  := y

[right  :  clist -> clist]
right(create)  := create
right(insert(create, x))  := insert(create, x)
right(insert(insert(x, y), z))  := insert(right(insert(x, z)), y)

[join  :  clist, clist -> clist]
join(x, create)  := x
join(x, insert(y, z))  := insert(join(x, y), z)

[qrep  :  clist -> queue]

[newq  :  queue]
newq == qrep(create)

[addq  :  queue, univ -> queue]
addq(qrep(x), y) == qrep(right(insert(x, y)))

[deleteq  :  queue -> queue]
deleteq(qrep(x)) == qrep(delete(x))

[frontq  :  queue -> univ]
frontq(qrep(x)) == avalue(x)

[isnewq  :  queue -> bool]
isnewq(qrep(x)) == isempty(x)

[appendq  :  queue, queue -> queue]
appendq(qrep(x), qrep(y)) == qrep(join(y, x))

]

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
n
n

prove
isnewq(addq(qrep(x), y)) == false
y

prove
deleteq(newq) == newq
n
n

prove
deleteq(addq(qrep(x), y)) == cond(isnewq(qrep(x)), newq, addq(deleteq(qrep(x)), y))
2
1 3 5

prove
frontq(addq(qrep(x), y)) == cond(isnewq(qrep(x)), y, frontq(qrep(x)))
1 3

prove
appendq(qrep(x), newq) == qrep(x)

prove
appendq(qrep(x), addq(qrep(y), z)) == addq(appendq(qrep(x), qrep(y)), z)
1
