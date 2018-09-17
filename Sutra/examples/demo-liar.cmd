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
p(says(a, liar(b))) == true
]
option
order
l
opera
prec
p says truth liar a b notknown
option
reduce
3
kb

