init
add
;;; the order of the input really matters!!!
x*i(y)==i(x*y)
x*x*x == x
((x * y) * z) == (x * (y * z))
(x + 0) == x
(x + i(x)) == 0
i(x)*y==i(x*y)
(x * (y + z)) == ((x * y) + (x * z))
((x + y) * z) == ((x * z) + (y * z))
(x * 0) == 0
(0 * x) == 0
i(x+y) == i(x)+i(y)
i(i(x))==x
i(0)==0
]

operator
ac-operator
+ 

operator
precedence
* i + 0

operator
divi
+
y
0

operator
status
*
lr

option
critical
rulesize
d

option
prove
f

prove
x * y == y * x
p
p
p
p
p


