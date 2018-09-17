From overbeek@antares.mcs.anl.gov Thu Jul 19 07:44:56 1990
Received: from antares1.mcs.anl.gov by herky.cs.uiowa.edu (5.59/890725) 
	  on Thu, 19 Jul 90 07:44:43 CDT id AA25743
Received: from clone.mcs.anl.gov by antares.mcs.anl.gov (4.1/SMI-DDN)
	id AA14048; Thu, 19 Jul 90 07:43:55 CDT
Received: by clone.mcs.anl.gov (4.0/GCF-5.2)
	id AA02160; Thu, 19 Jul 90 07:42:25 CDT
Date: Thu, 19 Jul 90 07:42:25 CDT
From: overbeek@antares.mcs.anl.gov
Message-Id: <9007191242.AA02160@clone.mcs.anl.gov>
To: mccune@antares.mcs.anl.gov, lusk@antares.mcs.anl.gov,
        rbutler@antares.mcs.anl.gov, zhangh@antares.mcs.anl.gov,
        stevens@antares.mcs.anl.gov, wos@antares.mcs.anl.gov
Subject: Cade 11 compretition
Status: R

I have been extremely negligent in getting my competition proposal into
acceptable shape.  I am attaching the current draft.  It needs a little work;
in particular, I need to make sure that I have not screwed up the equality
problems, so I would appreciate it if you could read them carefully (and
quickly, since I need to get this corrected and into Rusty's hands by
tomorrow.  Thanks.

-----------------------------------------------------------------------------
			 A Proposal for a Competition


In the past, people have discussed the idea of starting theorem-proving
competitions, but we were never able to formulate an acceptable mechanism
for comparing different systems.  I propose that we have a number of small
competitions on constrained aspects of automated deduction, with no pretense
that the winning sytems will have to be "best" in any overall sense.  The
notion of such competitions would be to allow researchers to focus on
well-defined, relevant issues and investigate alternative technologies in a
limited context.

To this end, I offer two $1000 prizes -- one for a competition in basic
components of resolution theorem-proving and one for problems based on
equality.   Here are the details of the two competitions:

---------------------------------------------------------------

		Basic Components of Resolution Theorem Proving

This competition will be to produce proofs of the following seven problems
(the first five appeared in "Subsumption, a Sometimes Undervalued Procedure" by
Wos, Overbeek, and Lusk).

Theorems:
1.  In a group, if (for all elements x) the square of x is the identity e, then 
    the group is commutative.

2.  In a group, if (for all x) the cube of x is the identity e, then the 
    equation [[x,y],y]=e holds, where [x,y] is the product of x, y, 
    the inverse of x, and the inverse of y (i.e., [x,y] is the commutator of
    x and y).

3.  In a ring, if (for all x) the cube of x is x, then the ring is commutative.

4.  The formula XGK = e(x,e(e(y,e(z,x)),e(z,y)))) is a shortest single axiom 
    for the equivalential calculus.

5.  The formula i(i(i(x,y),z),i(i(z,x),i(u,x))) is a shortest single axiom 
    of the implicational calculus.

6-7.  Two theorems from a calculus closely related to the implicational calculus
    (think of i(x,y) as "x implies y" and n(x) as "the negation of x").



Clauses for each problem:

Theorem 1:   
  
    % P(x,y,z) means that the product of x and y is z.

    % e is a two-sided identity
    P(e,x,x).
    P(x,e,x).
  
    % g(x) is a two-sided inverse for x
    P(g(x),x,e).
    P(x,g(x),e).
  
    % closure
    P(x,y,f(x,y)).
  
    % associativity
    -P(x,y,u) | -P(y,z,v) | -P(u,z,w) | P(x,v,w).
    -P(x,y,u) | -P(y,z,v) | -P(x,v,w) | P(u,z,w).
  
    % product is well-defined
    -P(x,y,u) | -P(x,y,v) | eq(u,v).
  
    % equality axioms
    eq(x,x).
    -eq(x,y) | eq(y,x).
    -eq(x,y) | -eq(y,z) | eq(x,z).
  
    % equality substitution axioms
    -eq(u,v) | -P(u,x,y) | P(v,x,y).
    -eq(u,v) | -P(x,u,y) | P(x,v,y).
    -eq(u,v) | -P(x,y,u) | P(x,y,v).
    -eq(u,v) | eq(f(u,x),f(v,x)).
    -eq(u,v) | eq(f(x,u),f(x,v)).
    -eq(u,v) | eq(g(u),g(v)).
  
      % the square of every x is the identity
    P(x,x,e).
    
    % Denial: there exist two elements that do not commute
    P(a,b,c).
    -P(b,a,c).
  
Theorem 2:
  
    % e is a two-sided identity
    P(e,x,x).
    P(x,e,x).
  
    % g(x) is a two-sided inverse for x
    P(g(x),x,e).
    P(x,g(x),e).
  
    % closure
    P(x,y,f(x,y)).
  
    %associativity
    -P(x,y,u) | -P(y,z,v) | -P(u,z,w) | P(x,v,w).
    -P(x,y,u) | -P(y,z,v) | -P(x,v,w) | P(u,z,w).
  
    % product is well-defined
    -P(x,y,u) | -P(x,y,v) | eq(u,v).
  
    % equality axioms
    eq(x,x).
    -eq(x,y) | eq(y,x).
    -eq(x,y) | -eq(y,z) | eq(x,z).
  
    % equality substitution axioms
    -eq(u,v) | -P(u,x,y) | P(v,x,y).
    -eq(u,v) | -P(x,u,y) | P(x,v,y).
    -eq(u,v) | -P(x,y,u) | P(x,y,v).
    -eq(u,v) | eq(f(u,x),f(v,x)).
    -eq(u,v) | eq(f(x,u),f(x,v)).
    -eq(u,v) | eq(g(u),g(v)).
  
    % x cubed is e
    -P(x,x,y) | P(x,y,e).
    -P(x,x,y) | P(y,x,e).

    % Denial: for some a and b, [[a,b],b] is not e
    P(a,b,c).
    P(c,g(a),d).
    P(d,g(b),h).
    P(h,b,j).
    P(j,g(h),k).
    -P(k,g(b),e).
  
Theorem 3:
  
    % 0 is an additive identity 
    S(0,x,x).
    S(x,0,x).
  
    % g(x) is an additive inverse for x
    S(g(x),x,0).
    S(x,g(x),0).
  
    % closure of addition
    S(x,y,j(x,y)).
  
    % associativity of addition
    -S(x,y,u) | -S(y,z,v) | -S(u,z,w) | S(x,v,w).
    -S(x,y,u) | -S(y,z,v) | -S(x,v,w) | S(u,z,w).
    
    % addition is well-defined
    -S(x,y,u) | -S(x,y,v) | eq(u,v).
  
    % equality axioms    
    eq(x,x).
    -eq(x,y) | eq(y,x).
    -eq(x,y) | -eq(y,z) | eq(x,z).
  
    % equality substitution axioms
    -eq(u,v) | -S(u,x,y) | S(v,x,y).
    -eq(u,v) | -S(x,u,y) | S(x,v,y).
    -eq(u,v) | -S(x,y,u) | S(x,y,v).
    -eq(u,v) |  eq(j(u,x),j(v,x)).
    -eq(u,v) |  eq(j(x,u),j(x,v)).
    -eq(u,v) |  eq(g(u),g(v)).
  
    % commutativity of addition
    -S(x,y,z) | S(y,x,z).
  
    % multiplication by 0
    P(0,x,0).
    P(x,0,0).
  
    % closure for multiplication
    P(x,y,f(x,y)).
  
    % associativity of multiplication
    -P(x,y,u) | -P(y,z,v) | -P(u,z,w) | P(x,v,w).
    -P(x,y,u) | -P(y,z,v) | -P(x,v,w) | P(u,z,w).
  
    % distributive laws
    -P(x,y,v1) | -P(x,z,v2) | -S(y,z,v3) | -P(x,v3,v4) | S(v1,v2,v4).
    -P(x,y,v1) | -P(x,z,v2) | -S(y,z,v3) | -S(v1,v2,v4) | P(x,v3,v4).
    -P(y,x,v1) | -P(z,x,v2) | -S(y,z,v3) | -P(v3,x,v4) | S(v1,v2,v4).
    -P(y,x,v1) | -P(z,x,v2) | -S(y,z,v3) | -S(v1,v2,v4) | P(v3,x,v4).
  
    % multiplication is well-defined
    -P(x,y,u) | -P(x,y,v) | eq(u,v).
  
    -eq(u,v) | -P(u,x,y) | P(v,x,y).
    -eq(u,v) | -P(x,u,y) | P(x,v,y).
    -eq(u,v) | -P(x,y,u) | P(x,y,v).
    -eq(u,v) | eq(f(u,x),f(v,x)).
    -eq(u,v) | eq(f(x,u),f(x,v)).
  
    % the square of every x is x
    P(x,x,x).

    % Denial:  there exist elements that don't commute
    P(a,b,c).
    -P(b,a,c).


Theorem 4:
  
    % condensed detachment
    -P(x) | -P(e(x,y)) | P(y).
  
    % the formula XGK
    P(e(x,e(e(y,e(z,x)),e(z,y)))).

    % the negation of PYO, which is a known single axiom
    -P(e(e(e(a,e(b,c)),c),e(b,a))).
  

Theorem 5:
    % condensed detachemt
    -P(x) | -P(i(x,y)) | P(y).
    
    % formula suspected of being a single axiom    
    P(i(i(i(x,y),z),i(i(z,x),i(u,x)))).

    % the negation of a known single axiom
    -P(i(i(a,b),i(i(b,c),i(a,c)))).


Theorem 6:
    % condensed detachemt
    -P(x) | -P(i(x,y)) | P(y).

    P(i(x,i(y,x))).

    P(i(i(x,y),i(i(y,z),i(x,z)))).

    P(i(i(i(x,y),y),i(i(y,x),x))).

    P(i(i(n(x),n(y)),i(y,x))).

    -P(i(i(a,b),i(i(c,a),i(c,b)))).

Theorem 7:
    % condensed detachemt
    -P(x) | -P(i(x,y)) | P(y).

    P(i(x,i(y,x))).

    P(i(i(x,y),i(i(y,z),i(x,z)))).

    P(i(i(i(x,y),y),i(i(y,x),x))).

    P(i(i(n(x),n(y)),i(y,x))).

    -P(i(i(a,b),i(n(b),n(a)))).

  

Systems must accept as input only the clauses (in whatever format is most
convenient); no parameters, designation of set-of-support, or weighting
templates are allowed.

Systems must be run during CADE-11, either at the site of the conference or
over networks.  They may be run on any machines.  

Systems may not be "over specialized"; for example, a system that simply
printed the proofs of the above problems would be unacceptable.  A system that
had builtin mechanisms for weighting just the terms that were known to appear
in these proofs would also be unacceptable.  I find it difficult to make this
notion precise, so I will simply say that the competitors can vote on any
serious question that comes up (and I will trust to their basic decency and
goodwill in settling any disagreements).

Grading of systems will be done as follows:

	1. All systems will be run, and the times for deriving the seven
	   proofs will be noted.  A system must prove  all problems 
           to win, unless no system successfully proves them all.

	2. A system will receive points for placing in the top three for each
	   of the problems -- three points for 1st, two points for 2nd, and
           one point for 3rd.

	3. The system with the highest score wins the prize.


I offer this prize, since there are many exciting opportunities offered by
current developments in massively-parallel machines, compilation technology,
and indexing technology.  There are well-known advocates of a variety of
alternative approaches.  I encourage everyone to compete in this fairly
circumscribed context in a friendly, common exploration.  There will probably
be at least two competing systems formed by my friends at Argonne (who hold
somewhat differing views on detailed issues).  I will attempt to build a
system around the use of FDB (a set of C routines that implement the basic
operations), Strand (a committed-choice logic programming language), and
distributed memory multiprocessors.  I would prefer to implement this approach
in cooperation with a group at some university.  In any event, I would happily
share my current views, code, and outlook with anyone that wished to build a
competing system.  Access to high-performance hardware will clearly be useful,
and I will attempt to make sure that any team that develops a system gets
access to large SIMD or MIMD machines.
----------------------------------------------------------------------

			   Equality-based Deduction

There are a number of good equality-based systems that have emerged over the
last five years.  This competition will be based on the following set of
problems:


PROBLEM 1: In a group, if x * x * x = e for all x in the group, then
the commutator h(h(x, y), y) = e for all x and y, where h(x, y) is defined
as x * y * g(x) * g(y).

Axioms: 

1  f(e, x) = x
2  f(g(x), x) = e
3  f(f(x, y), z) = f(x, f(y, z))
4  h(x, y) = f(x, f(y, f(g(x), g(y))))

5  f(x, f(x, x)) = e
6  h(h(a, b), b) != e


PROBLEM 2: In a Robbins algebra, if there exists c, such that
o(c, c) = c, then o(x, n(o(x, n(x)))) = x for all x.

Axioms:

1  o(x, y) = o(y, x)
2  o(o(x, y), z) = o(x, o(y, z))
3  n(o(n(o(x, y)), n(o(x, n(y))))) = x

4  o(c, c) = c
5  o(a, n(o(a, n(a)))) != a


PROBLEM 3: In a ternary Boolean algebra with the third axiom removed,
it is true that f(x, g(x), y) = y for all x and y.

Axioms:

1  f(f(v, w, x), y, f(v, w, z)) = f(v, w, f(x, y, z))
2  f(y, x, x) = x
4  f(x, x, y) = x
5  f(g(y), y, x) = x

6  f(a, g(a), b) != b


PROBLEM 4: The group theory specified by the axiom 
x * i((i(i(y) * (i(x) * w)) * z) * i(y * z)) = w 
implies the associativity of *.

Axioms:

1  f(x, i(f(f(i(f(i(y), f(i(x), w))), z), i(f(y, z))))) = w

2  f(a, f(b, c)) != f(f(a, b), c)


PROBLEM 5: The Wajsberg algebra formulation of a conjecture by
Lukasiewicz.
           
Axioms:

1 i(T,x) = x
2 i(i(x,y),i(i(y,z),i(x,z))) = T
3 i(i(x,y),y) = i(i(y,x),x)
4 i(i(n(x),n(y)),i(y,x)) = T

5 i(i(i(a,b),i(b,a)),i(b,a)) != T


PROBLEM 6: Find a fixed-point combinator in {B,W,M}
           
Axioms:

1 a(a(a(B,x),y),z) = a(x,a(y,z))
2 a(a(W,x),y) = a(a(x,y),y)
3 a(M,x) = a(x,x)

4 a(y,f(y)) != a(f(y),a(y,f(y)))


PROBLEM 7:  A ring in which x * x * x = x is commutative.

Axioms:

1  j(x, y) = j(y, x)
2  j(j(x, y), z) = j(x, j(y, z))
3  j(x, 0) = x
4  j(x, i(x)) = 0
5  f(x, j(y, z)) = j(f(x, y), f(x, z))
6  f(j(y, z), x) = j(f(y, x), f(z, x))
7  f(f(x, y), z) = f(x, f(y, z))

8  f(x, f(x,x)) = x
9  f(a,b) != f(b,a)

 


PROBLEM 8: Find a fixed-point combinator in {B,W}
           
Axioms:

1 a(a(a(B,x),y),z) = a(x,a(y,z))
2 a(a(W,x),y) = a(a(x,y),y)

3 a(y,f(y)) != a(f(y),a(y,f(y)))


PROBLEMS 9-10

Common Axioms for 9 and 10.

1 j(x,y) = j(y,x)                     * Commutativity for addition 
2 j(x,j(y,z)) = j(j(x,y),z)           * Associativity for addition 
3 j(x,0) = x                          * Additive identity 
4 j(0,x) = x
5 j(x,g(x)) = 0                       * Additive inverse 
6 j(g(x),x) = 0
7 g(0) = 0                             * Inverse of zero
8 j(x,j(g(x),y)) = y
9 g(j(x,y)) = j(g(y),g(x))
10 g(g(x)) = x                          
11 f(x,0) = 0
12 f(0,x) = 0
13 f(g(x),g(y)) = f(x,y)
14 g(f(x,y)) = f(g(x),y)
15 g(f(x,y)) = f(x,g(y))
16 f(x,j(y,z)) = j(f(x,y),f(x,z))     * Distributivity of addition 
17 f(j(x,y),z) = j(f(x,z),f(y,z))     * Distributivity of addition 
18 f(f(x,y),y) = f(x,f(y,y))          * Right alternative law 
19 f(f(x,x),y) = f(x,f(x,y))          * Left alternative law 
20 a(x,y,z) = j(f(f(x,y),z),g(f(x,f(y,z))))       * Associator
21 c(x,y) = j(f(y,x)),g(f(x,y))                  * Commutator 
22 f(w,x,y,z) = j(j(a(f(w,x),y,z),g(f(x,a(w,y,z)))),g(f(a(x,y,z),w)))  
   * Definition of f
23 f(f(a(x,x,y),x),a(x,x,y)) = 0                       
   * Middle associator identity 

Problem	9. 

	Show that the three Moufang identities imply the
	skew-symmetry of f(w,x,y,z) = (w*x,y,z) - x*(w,y,z) - (x,y,z)*w.

The following clauses are needed for proving problem 10.

24 f(x,f(y,f(z,y)) = f(c(f(x,y),z),y))                 * Right Moufang
25 f(f(y,f(z,y)),x) = f(y,c(z,f(y,x)))                 * Left Moufang
26 f(f(x,y),f(z,x)) = f(f(x,f(y,z)),x)                 * Middle Moufang

27a f(x,y,z,w) != g(f(y,x,z,w))                        * Denial of 9.
 
For problem 10 you should use the same axioms as above excepting 19,
22 and 27a with the addition of 27b.


Problem 10.
  Show in a right alternative ring (just the right alternative axiom) that       (((x,x,y)*x)*(x,x,y)) = 0.	


27b	  f(f(a(a,a,b),b),a(a,a,b))) != 0 	       * Denial of 10.


Note that (x,y,z) is an abbreviation for the associator a(x,y,z)
defined above.

----------------------------------------------------------------------

The basic rules for this competition are the same as in the previous
competition, except that programs are allowed to accept as input a term
ordering for each of the problems.  





