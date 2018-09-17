
init
add
ajoin(a, b)
ajoin(a, c)
ajoin(a, d)
ajoin(b, a)
ajoin(b, c)
ajoin(b, d)
ajoin(c, a)
ajoin(c, b)
ajoin(c, d)
ajoin(d, a)
ajoin(d, b)
ajoin(d, c)
not ajoin(x, x) 
map(x1, x2, x3, x4, x5) equ 
  ajoin(x1, x2) and ajoin(x1, x3) and ajoin(x1, x5) and 
  ajoin(x2, x3) and ajoin(x2, x4) and ajoin(x2, x5) and ajoin(x3, x4)
]
option
order
l
narrow
k
map(b, a, x3, x4, x5)
]
narrow
y
narrow
y
narrow
y
