add
;;; Christian 16.
f(f(x, y), z) == f(x, f(y, z))
f(e1, x) == x
f(e2, x) == x
f(e3, x) == x
f(e4, x) == x
f(e5, x) == x
f(e6, x) == x
f(e7, x) == x
f(e8, x) == x
f(x, i1(x)) == e1
f(x, i2(x)) == e2
f(x, i3(x)) == e3
f(x, i4(x)) == e4
f(x, i5(x)) == e5
f(x, i6(x)) == e6
f(x, i7(x)) == e7
f(x, i8(x)) == e8
]

oper
pred
;; i8 i7 i6 i5 i4 i3 i2 i1 f e8 e7 e6 e5 e4 e3 e2 e1
i8 i7 i6 i5 i4 i3 i2 i1 f

oper
status
f
lr

kb
