;; This file contains RRL's commands for proving the unique prime factorization
;; theorem in number theory.
init

option prove e

add
;; the constructors for the naturals.
[ 0 : num]
[ suc : num -> num]

1 == suc(0)
2 == suc(suc(0))

[ + : num, num -> num]
x + 0 := x
x + suc(y) := suc(x + y)

[ * : num, num -> num]
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

;; the constructors for the lists.
[null : list]
[cons : univ, list -> list]

[append : list, list -> list]
append(null, y) := y
append(cons(x, y), z) := cons(x, append(y, z)) 

[delete : univ, list -> list]
delete(x, null) := null
delete(x, cons(y, z)) := cond((x = y), z, cons(y, delete(x, z)))

[prime1 : num, num -> bool]
prime1(x, 0) := false
prime1(x, suc(0)) := true
prime1(x, suc(y)) := cond(divides(suc(y), x), false, prime1(x,y)) if not(y = 0)

[prime : num -> bool]
prime(0) := false
prime(suc(x)) := prime1(suc(x), x) 

[primelist : list -> bool]
primelist(null) := true
primelist(cons(x, y)) := cond(prime(x), primelist(y), false)

[timelist : list -> num]
timelist(null) := suc(0)
timelist(cons(x, y)) := x * timelist(y)

[primefac : num -> list]
primefac(0) := null
primefac(suc(0)) := null
primefac(x * y) := append(primefac(x), primefac(y)) if not(x = 0) and not(y = 0)

[member : univ, list -> bool]
member(x, null) := false
member(x, cons(y, z)) := cond((x = y), true, member(x, z))

[perm : list, list -> bool]
perm(null, null) := true
perm(null, cons(x, y)) := false
perm(cons(x, y), null) := false
perm(cons(x, y), z) := cond(member(x, z), perm(y, delete(x, z)), false)

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

oper
constructor
0 suc null cons
y
y

makerule
1 
1 
1
1 2
1 
1 2
1 
1 
1
1 2 3
status
perm
lr

prove div(0, y) == 0

y
y
y
y
y

prove rem(0, y) == 0

kb

prove x + y == y + x

prove (x + y) + z == x + (y + z)

prove (y * div(y + x, y)) == (y * suc(div(x, y)))

prove (rem(x, y) + (y * div(x, y))) == x

prove (y * div(x, y)) == x if divides(y, x)

prove (x * (y + z)) == ((x * y) + (x * z))

prove (x * y) * z == x * (y * z)
stat * l

prove x * y == y * x 

prove 0 < x == not(x = 0)

prove x < suc(0) == x = 0

prove (x + y) = 0 == cond((x = 0), (y = 0), false)
1

prove (x + y) = y == (x = 0)

prove (x + z) = (y + z) == (x = y)

prove (x * y) = 0 == cond((x = 0), true, (y = 0))

prove (x * y) = x == (y = suc(0)) if not(x = 0)

prove (x * y) = x == cond((x = 0), true, (y = suc(0)))

prove (x * y) = suc(0) == cond((x = suc(0)), (y = suc(0)), false)

prove div((x * y), x) == y if not((x = 0))

prove rem((y * x), x) == 0

prove rem((y * z), x) == 0 if divides(x, z) and not(x = 0)

prove rem(x + y,z) = rem(x, z) if divides(z, y)
exit

prove (suc(0) < y) if (not(y = 0)) and (not(y = suc(0)))

prove (div(x, y) < x) if (not(x = 0)) and (not(y = 0)) and (not(y = suc(0)))
n

prove divides(x, timelist(y)) == true if member(x, y)

prove delete(x, y) == y if not member(x, y)

prove primelist(delete(x, y)) if primelist(y)

prove y < suc(y)

prove (x = suc(0)) == false if prime(x)
y

prove (x = 0) == false if prime(x)
y

prove div(z + y, x) == div(z, x) + div(y, x) if divides(x, z) and not(x = 0)
exit
1

prove div(z * y, x) == y * div(z, x) if divides(x, z) and not(x = 0)
1

prove timelist(delete(x, y)) == div(timelist(y), x) if (not((x = 0)) and member(x, y))
1

prove timelist(x) = 0 == false if primelist(x)

prove primelist(append(z, z1)) ---> true  if primelist(z) and primelist(z1)

prove 0 >= u == u = 0

prove rem(suc(0), x) == suc(0) if not(x = suc(0))

prove prime1(w * z, u) == false if not(z = suc(0)) and not(z = 0) and (u >= z) and not(u = suc(0))

prove not(x < suc(y)) if y < x

prove suc(x) < y if (x < y) and not(suc(x) = y)

prove u >= z == not(u < z)
1

prove (u * y) < suc(y) == false if not(u = 0) and not(u = suc(0)) and not(y = 0)

prove sub1(x) < y == x < suc(y) if not(x = 0)
status 
<
l

prove not divides(z, x) if prime1(x, sub1(x)) and not(z = suc(0)) and not(z = x) and 
                          not(x = 0) and not(x = suc(0)) 
y

prove rem(x, y) = 0 == false if prime(x) and not(y = suc(0)) and not(x = y)
n

prove (rem(x, y) = 0) == false if prime(y) and prime(x) and not(x = y)
y

prove gcd(x, y) == gcd(y, x)

prove gcd((x * z), (y * z)) == (z * gcd(x, y))
1 

prove gcd(x * y, z) = y == false if (rem(z, x) = 0) and not(rem(y, x) = 0)

prove rem(y * z, x) = 0 == false if (gcd(x * y, y * z) = y) and not(y = 0) and not(rem(y, x) = 0)
y

prove gcd(x, suc(0)) == suc(0) if not((x = 0))

prove gcd(x, y) == suc(0) if
 (rem(x, gcd(x, y)) = 0) and
 not(x = 0) and not(x = suc(0)) and 
 prime1(x, sub1(x)) and
 not(gcd(x, y) = x) 
y

prove rem(x, gcd(x, y)) == 0

prove gcd(x, y) = x == false if not(rem(y, x) = 0)
y

prove gcd(x,y) == suc(0) if prime1(x, sub1(x)) and not(rem(y, x) = 0)
y

prove rem(y * z, x) = 0 == false if prime(x) and not(divides(x, y)) and not(divides(x, z))

prove member(x, y) if prime(x) and primelist(y) and divides(x, timelist(y))

prove timelist(delete(x, y)) == div(timelist(y), x) if divides(x, timelist(y)) and prime(x) and primelist(y)
y

prove timelist(primefac(x)) == x if not(x = 0)

prove primelist(primefac(x)) if not(x = 0)

prove perm(x, y) == true if (primelist(x) and (primelist(y) and (timelist(x) = timelist(y))))

list
