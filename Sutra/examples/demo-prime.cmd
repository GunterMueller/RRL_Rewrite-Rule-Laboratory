init
option
prove
e
add
[ 0 : num]
[ suc : num -> num]
[ + : num, num -> num]
[ * : num, num -> num]
1 == suc(0)
2 == suc(suc(0))
x + 0 := x
x + suc(y) := suc(x + y)
x * 0 := 0
x * suc(y) := x + x * y
[< : num, num -> bool]
0 < suc(x) := true
x < 0 := false
suc(x) < suc(y) := x < y
[sub1 : num -> num]
sub1(0) := 0
sub1(suc(x)) := x
[- : num, num -> num]
0 - x := 0
x - 0 := x
suc(x) - suc(y) := x - y
[div : num, num -> num]
div(x, 0) := 0
div(x, y) := 0 if x < y
div(y + x, y) := suc(div(x, y)) if not(0 = y)
[rem : num, num -> num]
rem(x, 0) := x
rem(x, y) := x if x < y
rem(y + x, y) := rem(x, y)
[divides : num, num -> bool]
divides(x, y) := rem(y,x) = 0

[nl : list]
[cons : univ, list -> list]
[append : list, list -> list]
append(nl, y) := y
append(cons(x, y), z) := cons(x, append(y, z)) 
[delete : univ, list -> list]
delete(x, nl) := nl
delete(x, cons(x, y)) := y
delete(x, cons(y, z)) := cons(y, delete(x, z)) if not(x = y)

[prime1 : num, num -> bool]
prime1(x, 0) := false
prime1(x, suc(0)) := true
prime1(x, suc(y)) := not(divides(suc(y), x)) and prime1(x,y) if not(y = 0)
[prime : num -> bool]
prime(0) := false
prime(suc(x)) := prime1(suc(x), x) 
[primelist : list -> bool]
primelist(nl) := true
primelist(cons(x, y)) := prime(x) and primelist(y)
[timelist : list -> num]
timelist(nl) := suc(0)
timelist(cons(x, y)) := x * timelist(y)
[primefac : num -> list]
primefac(0) := nl
primefac(suc(0)) := nl
primefac(x * y) := append(primefac(x), primefac(y)) if not(x = 0) and not(y = 0)
[member : univ, list -> bool]
member(x, nl) := false
member(x, cons(x, z)) := true
member(x, cons(y, z)) := member(x, z) if not(x = y)
[perm : list, list -> bool]

perm(nl, nl) := true
perm(nl, cons(x, y)) := false
perm(cons(x, y), nl) := false
perm(cons(x, y), z) := member(x, z) and perm(y, delete(x, z))
[>= : num, num -> bool]
x >= x := true
0 >= suc(y) := false
suc(x) >= y := x >= y if not(suc(x) = y)
[gcd : num, num -> num]
gcd(x, 0) := x
gcd(0, y) := y
gcd(x + y, y) := gcd(x, y)
gcd(x, x + y) := gcd(x, y)
]
option
ordering
l
option
undo
noundo
oper
constructor
0 suc nl cons
y
y
kb
1 
1 
1 
1 
1 
1 
1 
1 2
status
perm
lr
quit
prove
div(0, y) == 0

prove
rem(0, y) == 0

kb
prove
x+y == y+x

prove
y*div(y+x,y) == y*suc(div(x, y))		

prove
(rem(x, y) + (y * div(x, y))) == x

prove
(y * div(x, y)) == x if divides(y, x)

prove
(x * (y + z)) == ((x * y) + (x * z))

prove
(x * y) * z == x * (y * z)

stat
*
l

prove
x * y == y * x 

prove
0 < x == not(x = 0)

prove
x < suc(0) == x = 0

prove
(x + y) = 0 == (x = 0) and (y = 0)

prove
(x + y) = y == (x = 0)

prove
(x + z) = (y + z) == (x = y)

prove
(x * y) = 0 == (x = 0) or (y = 0)

prove
(x * y) = x == (y = suc(0)) if not(x = 0)

prove
(x * y) = x == (y = suc(0)) or (x = 0)

prove
(x * y) = suc(0) == (x = suc(0)) and (y = suc(0))

prove
div((x * y), x) == y if not((x = 0))

prove
rem((y * x), x) == 0

prove
rem((y * z), x) == 0 if (rem(z, x) = 0) and not(x = 0)

prove
rem(x+y,z) = rem(x, z) if rem(y, z) = 0

prove
(div(x, y) < x) if (not(x = 0)) and (not(y = 0)) and (not(y = suc(0)))
n

prove
divides(x, timelist(y)) == true if member(x, y)

prove
delete(x, y) == y if not member(x, y)

prove
primelist(delete(x, y)) if primelist(y)

prove
y < suc(y)

prove
(x = suc(0)) == false if prime(x)
y

prove
(x = 0) == false if prime(x)
y

prove 
div(z + y, x) == div(z, x) + div(y, x) if divides(x, z) and not(x = 0)
1

prove
div(z * y, x) == y * div(z, x) if divides(x, z) and not(x = 0)
1

prove
timelist(delete(x, y)) == div(timelist(y), x) if (not((x = 0)) and member(x, y))
1

prove
timelist(x) = 0 == false if primelist(x)

prove
timelist(primefac(x)) == x if not(x = 0)

prove
primelist(primefac(x)) if not(x = 0)

prove
0 >= u == u = 0

prove
rem(suc(0), x) == suc(0) if not(x = suc(0))

prove
prime1(w*z, u) == false if not(z = suc(0)) and not(z = 0) and (u >= z) and not(u = suc(0))

prove 
suc(x) < y if (x < y) and not(suc(x) = y)

prove
u >= z == not(u < z)
1

prove
(u * y) < suc(y) == false if not(u = 0) and not(u = suc(0)) and not(y = 0)

prove
sub1(x) < y == x < suc(y) if not(x = 0)
status 
<
l
prove
prime1(x, sub1(x)) == false if not(z = suc(0)) and not(z = x) and not(x = 0) and 
    not(x = suc(0)) and divides(z, x)

prove
rem(x, y) = 0 == false if prime(x) and not(y = suc(0)) and not(x = y)
n

prove
prime(y) == false if (rem(x, y) = 0) and prime(x) and not(x = y)
y

prove
gcd(x, y) == gcd(y, x)

prove
gcd((x * z), (y * z)) == (z * gcd(x, y))
1 

prove
gcd(x*y, z) = y == false if (rem(z, x) = 0) and not(rem(y, x) = 0)

prove
rem(y * z, x) = 0 == false if (gcd(x*y, y*z) = y) and not(y = 0) and not(rem(y, x) = 0)
y

prove
gcd(x, suc(0)) == suc(0) if not((x = 0))

prove
gcd(x, y) == suc(0) if
 (rem(x, gcd(x, y)) = 0) and
 not(x = 0) and not(x = suc(0)) and 
 prime1(x, sub1(x)) and
 not(gcd(x, y) = x) 
y

prove
rem(x, gcd(x, y)) == 0

prove 
gcd(x, y) = x == false if not(rem(y, x) = 0)
y

prove
prime1(x, sub1(x)) == false if not (rem(y, x) = 0) and not(gcd(x,y) = suc(0)) 
y

prove
rem(y * z, x) = 0 == false if prime(x) and not(divides(x, y)) and not(divides(x, z))

prove
member(x, y) if prime(x) and primelist(y) and divides(x, timelist(y))

prove
perm(x, y) == true if (primelist(x) and (primelist(y) and (timelist(x) = timelist(y))))

option
undo
undo
history
