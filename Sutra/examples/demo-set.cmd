init
option
prove
c
option 
order
s
add
mem(u, set2(x, y)) == true if (u = x) and m(u)
mem(u, set2(x, y)) == false if not (u = x) and not (u = y)
m(set2(x, y)) == true
set1(x) == set2(x, x)
pair(x, y) == set2(set1(x), set2(x, y))
m(ax) == true
m(au) == true
pair(ax, ay) == pair(au, av)
au = ax == false
]
kb
1 3
2
n
