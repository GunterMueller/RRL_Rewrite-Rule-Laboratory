;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

(defun lrpo (t1 t2) 
   (if (or $induc (null $ac))
       (pure-lrpo t1 t2)
       (aclrpo t1 t2)))

; This file contains the functions for lexicographic recursive path ordering.

(defun pure-lrpo (t1 t2)
  ; Compares two terms, T1 and T2, using LRPO with equivalent
  ; operators.  Returns T if T1 > T2 using LRPO.
  ; First check if either T1 or T2 is a variable.  If not, then compare
  ; root operators and handle the three cases of equivalent, greater,
  ; and neither equivalent nor greater in the precedence relation on
  ; function symbols.
  (cond	((variablep t1) nil)
        ((variablep t2) (is-subt t2 t1))
        (t (cond ((eqops (op-of t1) (op-of t2)) 
		  (cond ((null (args-of t2)) (args-of t1))
	  	        ((and (get-status (op-of t1))
			      (eq (length t1) (length t2)))
			 (rpost t1 t2))
		        (t (rpomult t1 t2))))
		 ((grt-prec (op-of t1) (op-of t2))
		  (if (args-of t2)
		    then (loop for xb in (args-of t2) 
				always (pure-lrpo t1 xb))
		    else t))
		 (t (loop for xa in (args-of t1) 
			thereis (or (pure-lrpo xa t2) (equiv xa t2))))))))

(defun equiv (t1 t2)
  ;  Tests if the two terms, T1 and T2, are equivalent.
  ;	    (let t = f(t1,t2,...,tn) and s = g(s1,s2,...sm)
  ;	     t is equivalent to s iff f ~ g in precedence, n = m and
  ;	     there is a permutation on 1...n such that t1 ~ sj where
  ;	     i is mapped to j.
  ;	     If, however, f and g have status then s1 ~ ti for i = 1,2,...,n
  ;	     Equivalent means same upto permutation of arguments.)
  (cond ((variablep t1) (equal t1 t2))
	((variablep t2) nil)
	((and (eqops (op-of t1) (op-of t2)) 
	      (equal (length (args-of t1)) (length (args-of t2))))
	 (if (get-status (op-of t1)) 
	    then (loop for xa in (args-of t1)
		        as ya in (args-of t2) always (equiv xa ya))
	    elseif (args-of t1) 
	    then (equiv-list (args-of t1) (args-of t2))
	    else t))))

; The following are local functions.

(defun equiv-list (l1 l2)
  ; Suppose l1 = {t1, t2, ..., tn) and l2 = {s1, s2, ..., sn}.
  ; Return t iff there is a permutation on 1...n such that 
  ;    equiv(ti, sj) where i is mapped to j.
  (let ((l3 t) xb)
    (loop for xa in l1 do
	(setq l3 l2 l2 nil)
	(loop while l3 do 
	    (setq xb (pop l3))
	    (if (equiv xa xb)
		then (setq l2 (nconc l2 l3) l3 t) (return)
		else (setq l2 (append1 l2 xb))))
	(if (null l3) then (return)))
    l3))

(defun rpomult (t1 t2)
  ;  Called when the top-level operators, T1 and T2, are equivalent
  ;	    and have multiset status.  Returns T if T1 > T2.
  (let (l1 l2)
    (setq l2 (mult-diff (mult-form (args-of t1)) (mult-form (args-of t2)))
	  l1 (pop l2))
    (cond ((null l2) l1)
	  ((null l1) nil)
	  (t (loop for xa in l2 always
		   (loop for xb in l1 thereis (pure-lrpo xb xa)))))))

(defun rpost (t1 t2)
  ; Called when T1 and T2 have equivalent operators at the top
  ; level and those operators have status.  Compares the list of
  ; arguments from left-to-right or right-to-left and decides if T1 > T2.
  (let ((lis1 (args-of t1)) (lis2 (args-of t2)))
;    (if (null (cdr lis2)) 
;        then (setq lis2 (car lis2))
;	     (if (null (cdr lis1))
;		 then (pure-lrpo (car lis1) lis2)
;		 else (loop for xa in lis1 thereis
;			    (or (pure-lrpo xa lis2) (equiv xa lis2))))
;	elseif (eq (get-status (op-of t1)) 'rl)
    (if (eq (get-status (op-of t1)) 'rl)
	then (lexico-comp t1 t2 (reverse lis1) (reverse lis2))
	else (lexico-comp t1 t2 lis1 lis2))))

(defun lexico-comp (t1 t2 lis1 lis2)
    (loop while (and lis1 lis2) do
	(if (equiv (car lis1) (car lis2)) 
	    then (pop lis1) (pop lis2)
	    else (return)))
    (cond ((null lis1) nil)
	  ((null lis2) t)
	  ((pure-lrpo (pop lis1) (pop lis2))
	   (loop for xb in lis2 always (pure-lrpo t1 xb)))
	  (t (loop for xa in lis1 thereis
		   (or (equiv xa t2) (pure-lrpo xa t2))))))
