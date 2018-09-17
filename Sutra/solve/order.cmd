init

add

apply(a1,0,x) == x
apply(a1,x,0) == x
apply(a1,s(x),y) == s(apply(a1,x,y))

apply(a2,0,x) == 0
apply(a2,x,0) == 0
apply(a2,s(x),y) == apply(a1,y,apply(a2,x,y))
]

oper pre a2 a1 apply s 0
oper status apply lr

kb
