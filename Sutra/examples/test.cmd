init
add
(x * e) == x
(x * i(x)) == e
(x * (y * z)) == ((x * y) * z)
]
kb
1 2 
status
*
lr
2
undo
add
x * y == y * x
]
kb
2
init
add
(x + 0) == x
(x + i(x)) == 0
((x * y) * z) == (x * (y * z))
x * i(y) == i(x * y)
i(x) * y == i(x * y)
(x * (y + z)) == ((x * y) + (x * z))
((x + y) * z) == ((x * z) + (y * z))
(x * 0) == 0
(0 * x) == 0
i(x + y) == i(x) + i(y)
i(i(x)) == x
i(0) == 0
]
operator
ac
+ * 
kb
1 
1 
; 2   -- after AC-rpo
1 

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

init
add
[0 : int]
[1 : int]
[+ : int, int -> int]
[* : int, int -> int]
[div2 : int -> int]
[sum : int -> int]
x + 0 == x
x * 0 == 0
x * (y + 1) == (x * y) + x
x * (y + z) == (x * y) + (x * z)
div2(0) == 0
div2(1) == 0
div2(x + x) == x
div2(x + y + y) == div2(x) + y
sum(0) == 0
sum(x + 1) == sum(x) + (x + 1)
]
operator
ac
+ * 
kb
1 
1
lr
y
operator
constructor
0 1 +
suffic
list
prove
sum(x) == div2((x + (x * x)))
y
1 3
y

init
add
(a and b) -> c
(e and k) -> m
r -> (s or t)
(c and d) -> k
r -> (e or n)
(h and l) -> r
(c and m and e) -> false
(s and n and k) -> false
(a and h and r) -> b
(a and d) -> l
(c and t) -> e
a
h
a or b
c or d
e or h
k or l
m or n
r or s
]
kb

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
l
l
l
n

init
option
prove
c
add
[p : univ -> bool]
p(truth(x)) == not(p(liar(x)))
p(says(x, y)) == false if p(y) = p(liar(x))
p(says(x, y)) == false if p(y) = not(p(truth(x)))
p(says(a, notknown)) == true
p(says(b, says(a, liar(a)))) == true
p(says(c, liar(b))) == true
]
option
order
l
opera
prec
p says truth liar a b c notknown
option
reduce
3
kb

q
q
