; option trace 1
; option fastkb block t
; option fastkb left t

add
f(f(x, y), z) == f(x, f(y, z))
f(e1, x) == x
f(e2, x) == x
f(x, i1(x)) == e1
f(x, i2(x)) == e2
]

oper
pred
i2 i1 f e2 e1

oper
status
f
lr

kb
