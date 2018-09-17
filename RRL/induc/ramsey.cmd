;; This file contains RRL's commands for proving Ramsey's theorem (finite
;; version of two components) in graph theory.

init 
option prove e

add
[0 : num]
[suc : num -> num]

[null : list]
[cons : univ, list -> list]

[mkpair : univ, univ -> pair]

[+ : num, num -> num]
  x + 0 := x
  x + suc(y) := suc(x + y)

[>= : num, num -> bool]
  x >= 0 := true
  0 >= suc(x) := false
  suc(x) >= suc(y) := x >= y

[length : list -> num]
  length(null) := 0
  length(cons(x, y)) := suc(length(y))

[member : univ, list -> bool]
  member(x, null) := false
  member(x, cons(y, z)) := cond((x = y), true, member(x, z))

[distinct : list -> bool]
  distinct(null) := true
  distinct(cons(x, y)) := cond(member(x, y), false, distinct(y))

[subsetp : list, list -> bool]
  subsetp(null, W) := true
  subsetp(cons(x, y), W) := cond(member(x, W), subsetp(y, W), false)

[membership : bool, univ, univ -> bool]
  membership(true, x, y) := member(x, y)
  membership(false, x, y)  == not(member(x, y))

[ split  : num, list, list, bool  -> list]
  split(v, null, Z, xf)  := null
  split(v, cons(u, W), Z, xf)  :=
         cond(membership(xf, mkpair(v, u), Z),
              cons(u, split(v, W, Z, xf)), 
              split(v, W, Z, xf))
    
T(v, W, Z) == split(v, W, Z, true)
S(v, W, Z) == split(v, W, Z, false)

[homo : num, list, list, bool -> bool]
  homo(v, null, Z, xf) := true
  homo(v, cons(u, W), Z, xf) := membership(xf, mkpair(v, u), Z) and homo(v, W, Z, xf)

[homoset : list, list, bool -> bool]
  homoset(null, Z, xf) := true
  homoset(cons(v, W), Z, xf) := homo(v, W, Z, xf) and homoset(W, Z, xf)

clique(V, Z) == homoset(V, Z, true)
indep(V, Z) == homoset(V, Z, false)

[ramsey : num, num -> num]
  ramsey(0, y) := suc(0)
  ramsey(x, 0) := suc(0)
  ramsey(suc(x), suc(y)) := ramsey(suc(x), y) + ramsey(x, suc(y))

[flag : list, list, num, num -> bool]
  flag(null, Z, x, y) := true
  flag(cons(v, W), Z,  0, y) := true
  flag(cons(v, W), Z, suc(x), 0) := false
  flag(cons(v, W), Z, suc(x), suc(y)) :=
             cond((length(S(v, W, Z)) >= ramsey(suc(x), y)),
                  flag(S(v, W, Z), Z, suc(x), y), 
                  flag(T(v, W, Z), Z, x, suc(y)))
    
[soln : list, list, num, num -> list]
  soln(null, Z, x, y) := null
  soln(cons(v, W), Z, 0, y) := null
  soln(cons(v, W), Z, suc(x), 0) := null
  soln(cons(v, W), Z, suc(x), suc(y)) :=
             cond(flag(S(v, W, Z), Z, suc(x), y), 
                  soln(S(v, W, Z), Z, suc(x), y), 
                  cons(v, soln(S(v, W, Z), Z, suc(x), y))) if
          (length(S(v, W, Z)) >= ramsey(suc(x), y))
  soln(cons(v, W), Z, suc(x), suc(y)) :=
             cond(flag(T(v, W, Z), Z, x, suc(y)), 
                  cons(v, soln(T(v, W, Z), Z, x, suc(y))), 
                  soln(T(v, W, Z), Z, x, suc(y))) if
          not(length(S(v, W, Z)) >= ramsey(suc(x), y))
]

operator
precedence
soln flag S T split subsetp distinct indep clique homoset homo ramsey length membership member cond >= +

operator constructor 0 suc null cons mkpair
y
y
y

operator status flag rl
operator status soln rl

makerule

prove suc(x) + y == suc(x + y)

y

prove 0 >= x == x = 0

prove (y + z) >= x if (y >= x)

prove not(suc(x + u) >= (y + v)) if not(x >= y) and not(u >= v)

prove (y >= suc(x)) == not(x >= y)

prove (length(S(u, V, Z)) >= ramsey(suc(x), y)) if
         (suc(length(S(u, V, Z)) + length(T(u, V, Z))) >= ramsey(suc(x), suc(y))) and
          not(length(T(u, V, Z)) >= ramsey(x, suc(y)))
y

prove not(0  >= ramsey(x, y))

prove length(S(u, V, Z)) + length(T(u, V, Z)) == length(V)

prove subsetp(x, cons(y, z)) if subsetp(x, z)

prove member(x, y) if member(x, z) and subsetp(z, y)

prove not member(u, split(v, W, Z, xf)) if 
               not(member(u, W)) and subsetp(split(v, W, Z, xf), W)
y

prove not member(u, soln(V, Z, x, y)) if 
               not(member(u, V)) and subsetp(soln(V, Z, x, y), V)
y

prove subsetp(x, y) if subsetp(x, z) and subsetp(z, y)

prove subsetp(soln(split(v, W, Z, xf), Z, x, y), cons(u, W)) if
          subsetp(soln(split(v, W, Z, xf), Z, x, y), split(v, W, Z, xf)) and
          subsetp(split(v, W, Z, xf), cons(u, W))
y

prove subsetp(split(u, V, Z, xf), V)

prove membership(xf, mkpair(v, u), Z) if homo(v, W, Z, xf) and member(u, W)

prove homo(u, V1, Z, xf) if homo(u, V, Z, xf) and subsetp(V1, V)

prove homo(u, soln(split(u, V, Z, xf), Z, x, y), Z, xf) if
                homo(u, split(u, V, Z, xf), Z, xf) and 
                subsetp(soln(split(u, V, Z, xf), Z, x, y), split(u, V, Z, xf))
y

prove homo(u, split(u, V, Z, xf), Z, xf)

prove distinct(split(u, V, Z, xf)) if distinct(V)

prove subsetp(soln(V, Z, x, y), V) 

prove distinct(soln(V, Z, x, y)) if distinct(V)

prove cond(flag(V, Z, x, y), clique(soln(V, Z, x, y), Z), indep(soln(V, Z, x, y), Z))
n
n

prove cond(flag(V, Z, x, y), 
           (length(soln(V, Z, x, y)) >= x), 
           (length(soln(V, Z, x, y)) >= y)) if (length(V) >= ramsey(x, y))
n
n

list


