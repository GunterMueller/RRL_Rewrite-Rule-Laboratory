init

add

0 < 0 == false
0 < s(0) == true
s(x) < s(y) == x < y
0 < s(x) == true  if (0 < x)

s(x) - y == s(x - y)
x - 0  == x

0 + x == x
s(x) + y == s(x + y)

0 * x == 0
s(x) * y == y + (x * y)

fact(0) == s(0)
fact(x) == x * fact(x - s(0)) if (0 < x)

]

opt order m

kb
lr
lr
lr
lr
lr
lr
lr
lr
lr
lr
lr
rl

