;; Example defining the Ackermann function and checking
;; sufficient completeness of the definition. - siva 1/31/90

init

add

[0 : int]
[s : int -> int]
[ack : int, int, int -> int]

ack(0, 0, x) == x  
ack(0, s(x), y) == s(ack(0, x, y)) 
ack(s(0), 0, y) == 0  
ack(s(s(x)), 0, y) == s(0)  
ack(s(z), s(x), y) == ack(z, ack(s(z), x, y), y)  

]

oper cons s 0
y

oper pre ack s 0

oper status ack lr

kb

suffic
