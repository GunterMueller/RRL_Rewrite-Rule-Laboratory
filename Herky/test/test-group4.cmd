add
;;; Christian 4.
f(f(x, y), z) == f(x, f(y, z))
f(e1, x) == x
f(e2, x) == x
f(e3, x) == x
f(e4, x) == x
f(x, i1(x)) == e1
f(x, i2(x)) == e2
f(x, i3(x)) == e3
f(x, i4(x)) == e4
]

oper
pred
i4 i3 i2 i1 f e4 e3 e2 e1

oper
status
f
lr

kb
