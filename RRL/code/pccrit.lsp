;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")


#+franz (declare (special $detachment-ops))
(setq $detachment-ops nil)

(defun pred-superposition (rule1 rule2)
  ; Find a superposition of rule1 and rule2, where both of these 
  ; are predicates.  Right now, the only overlaps that are found are overlaps
  ; with one atomic formula.  We don't try overlaps with zero atomic formulae
  ; yet.
  ; $idem = 1     : do idemponcy superpositions
  ;         2     : do non-unit superpositions
  ;         3     : do unit superpositions
  ;         4     : do input superpositions
  (cond ((= (ruleno rule1) (ruleno rule2)) 
	 (if* (= $idem 1) then (idem-superposition rule1))) 
	((and (nequal (rhs rule1) (rhs rule2))
	      (or (< $idem 3) (unitp rule1) (unitp rule2)))
	 (pred-super (canonicalize (lhs rule1)) (canonicalize (lhs rule2))
		     rule1 rule2))))

(defun pred-super (lhs1 lhs2 rule1 rule2 &aux subst)
  ; This function tries to superpose two polynomials
  ; It does this by trying to unify two atomic formulae
  ; If it comes across an atomic formula that is an eq,
  ; then depending on the flag $paramodulate it will try to paramodulate
  ; rule1 on rule2 using the eq atomic formula.
  (sloop for mon1 in (cdr lhs1) do
     (sloop for mon2 in (cdr lhs2) do
	(sloop for atom1 in (cdr mon1) do
	   (if* (eq (op-of atom1) 'eq) 
             then (sloop for atom2 in (cdr mon2)
			if (and (same-op atom1 atom2) 
				(= (nargs atom1) (nargs atom2))
			        (not (< (length atom1) (length atom2)))) 
			  ; try to unify two "eq" atomic formulas.
			  do (if* (setq subst (cdr (set-unification (args-of atom2) 
								   (args-of atom1))))
				 then (pred-critical-pair
					;mon1 mon2
					(remonce atom1 mon1)
					(remonce atom2 mon2)
					(decanon-xor (remonce mon1 lhs1))
					(decanon-xor (remonce mon2 lhs2)) 
					rule1 rule2 subst))
			do (if* (eq $paramodulate 'y) then 
			       (paramodulate lhs1 lhs2 rule1 rule2 atom1 mon2 atom2)))
             else (sloop for atom2 in (cdr mon2) do
		    (sloop for subs in (unifiers atom1 atom2)
			  do (pred-critical-pair
			       (remonce atom1 mon1)
			       (remonce atom2 mon2)
			       (decanon-xor (remonce mon1 lhs1))
			       (decanon-xor (remonce mon2 lhs2)) 
			       rule1 rule2 subs))))))))

(defun pred-func-superposition (predrule domrule &optional flag)
  ; Find all superpositions between a predicate rule and a domain rule.
  ; flag denotes whether domrule is ac-rooted: 1 then yes, otherwise no.
  ; for efficiency, the extension of domrule will not be used, though
  ; this causes the incompleteness.
  (if* (nequal flag 1) then
      (let ((lhs1 (canonicalize (copy (lhs predrule))))
	    (lhss (commune-terms (lhs domrule))))
	(sloop for mon in (args-of lhs1) do
	  (sloop for pred in (args-of mon) do
	    (if* (nonvarp pred) then
		(sloop for subs on (args-of pred) do
		  (if* (nonvarp (car subs)) then
		      (pred-func-sup lhs1 subs predrule domrule lhss)))))))))

(defun pred-func-sup (lhs1 subs prule drule lhss &aux saved_sub ass)
  ; lhs1 is the lhs of prule.
  ; sub is a subterm we are currently unifying with the lhs of drule.
  ; prule is the rule whose left hand side is equal to term. 
  ; drule is the rule whose left hand side ought to unify; with subterm.
  ; lhss are the equaivalent terms of the lhs of drule.
  (sloop for lhs2 in lhss do
    (sloop for subst in (unifiers (car subs) lhs2) do
      (setq saved_sub (car subs)
            $ncritpr (1+ $ncritpr)
	    ass (list (rhs prule) (progn (setf (car subs) (rhs drule)) (copy lhs1)))
	    ass (if* (member0 '(true) ass) then (delete0 '(true) ass 1) else (cons '(true) ass))
	    ass (applysubst subst (make-term 'xor ass)))

      (if* (well-typed ass) 
       then (if* (= $trace_flag 3) then 
		(trace-crit (list (ruleno prule) (ruleno drule)) ass t))
       (process-ass-simple (flat-term ass) (list (ruleno prule) (ruleno drule)))
       (setf (car subs) saved_sub)))

    (sloop for xas on (args-of (car subs)) 
	  if (nonvarp (car xas)) 
	    do (pred-func-sup lhs1 xas prule drule lhss)))

  (sloop for xas on (args-of subs) if (nonvarp (car xas)) do
         (pred-func-sup lhs1 xas prule drule lhss)))

(defun idem-superposition (rule)
  ; Find some of the idempotent superpositions of a rule with itself.
  (let ((lhs (canonicalize (lhs rule)))
	(ruleno (ruleno rule)) l1)

    (if* (or (memq (setq l1 (op-of (lhs rule))) $commutative)
	    (and (eq l1 'eq) (null (cdddr (lhs rule)))))
	then (idem-super-commu rule))

     (setq ruleno (list 'idem ruleno))

     (if* (memq (op-of (lhs rule)) '(and xor)) then
	   (both-add-predicate rule lhs ruleno))

     (sloop with z1 for x1 in (args-of lhs) do
         (sloop for y1 on (args-of x1) do
	    (setq z1 (car y1))
  
  	    ; Computing critical pairs with EQ predicate.
	    (if* (eq (op-of z1) 'eq) (idem-eq-critical rule (args-of z1) ruleno))

 	    (sloop for z11 in (cdr y1) do
		(sloop for z2 in (unifiers z1 z11) do
	           (setq $ncritpr (1+ $ncritpr)
	  	         z2 (applysubst z2 
				`(xor (true) ,(lhs rule) ,(rhs rule))))
		   (if* (well-typed z2) then
		       (if* (= $trace_flag 3) then (trace-crit ruleno z2 t))
		       (process-ass-simple (flat-term z2) ruleno))))))))

(defun idem-super-commu (rule &aux r2)
  (setq r2 (make-new-rule (lhs rule) (rhs rule) (ctx rule) 
			  (rule-source rule) (ruleno rule)))
  (if* (nequal (rhs rule) (rhs r2)) then
      (sloop for lhs in (commune-terms (lhs rule))
	    if (nequal lhs (lhs rule))
	      do (sup-term2 r2 rule lhs lhs nil))))

(defun both-add-predicate (rule lhs ruleno)
   (sloop for x1 in (args-of lhs) do
     (sloop for y1 in (args-of x1) do
        (setq $ncritpr (1+ $ncritpr)
  	      y1 `(xor (true) (and ,y1 ,(lhs rule)) (and ,y1 ,(rhs rule))))
        (if* (= $trace_flag 3) then (trace-crit ruleno y1 t))
	(process-ass-simple (flat-term y1) ruleno))))

(defun pred-critical-pair (m1 m2 lhs1 lhs2 rule1 rule2 subst &aux common)
  ; m1 is the term of lhs1 that atom1 appears in, with the atomic formula 
  ;	that unified removed.
  ; m2 is the term of lhs2 that atom2 appears in, with the atomic formula
  ;	that unified removed.
  ; lhs1 is the left side of rule1 with m1 removed
  ; lhs2 is the left side of rule2 with m2 removed
  ; rule1 and rule2 are the rules that we have found a superposition.
  ; subst is the substitution that unifies atom1 and atom2.
  (setq m1 (applysubst subst m1)
	m2 (applysubst subst m2)
	common (intersection (cdr m1) (cdr m2)))

  ; The common part of atoms in m1 and m2 must be removed to produce a prime
  ; superposition. The counter-example by Stillman is known if this common part is not
  ; removed.
  ; The input of the counter-example: 
  ;     1. a1 xor b1
  ;     2. a2 xor b2
  ;     3. (a1 and a2) -> a3
  ;     4. (b1 and b2) -> b3
  (if* common 
      (setq m1 (set-diff m1 common)
	    m2 (set-diff m2 common)))

  (setq m1 (decanon-and m1)
	m2 (decanon-and m2)
        m1 `(xor (true)
	     (and ,m2 ,(applysubst subst (rhs rule1)))
	     (and ,m1 ,(applysubst subst lhs2))
	     (and ,m2 ,(applysubst subst lhs1))
	     (and ,m1 ,(applysubst subst (rhs rule2))))
        $ncritpr (1+ $ncritpr))
  (if* (well-typed (setq m2 (flat-term m1))) then
      (if* (= $trace_flag 3) 
	  (trace-crit (list (ruleno rule1) (ruleno rule2)) m1 t))
      (process-ass-simple m2 (list (ruleno rule1) (ruleno rule2)))))


(defun detachment-rule (rule)
  (and (null (ctx rule))
       (eq (op-of (lhs rule)) 'thm)
       (nonvarp (setq rule (first-arg (lhs rule))))
       (memq (op-of rule) $detachment-ops)))

(defun detachment-critical (rule)
  (let ((l2 (ruleno rule)) (arg1 (first-arg (lhs rule))) l1)

    (if* (truep (rhs rule)) then

	; separate i(x, y) into not (y) => not (x).
	(setq $ncritpr (1+ $ncritpr)	
	      l1 (make-eqn
		   (list 'thm (first-arg arg1))
		   '(false)
		   (list 'xor '(true) (list 'thm (second-arg arg1)))
		   (list 'detach l2)))
	(process-critpair l1)

	; add a new variable as t becomes not(i(z)) => not(i(t, z)).
	(setq $ncritpr (1+ $ncritpr)	
	      l1 (make-eqn
		   (list 'thm (list 'i arg1 (setq l1 (make-new-variable 'v))))
		   '(false)
		   (list 'xor '(true) (list 'thm l1))
		   (list 'detach l2)))
	(process-critpair l1)

;	else
;	; add a new variable as not(t) becomes i(z) => not(i(z, t)).
;	(setq $ncritpr (1+ $ncritpr)	
;	      l1 (make-eqn
;		   (list 'thm (list 'i (setq l1 (make-new-variable 'u)) arg1))
;		   '(false)
;		   (list 'thm l1)
;		   (list 'detach l2)))
;	(process-critpair l1)
	)))

(defun detachment-super (rule1 rule2 arg1)
  ;
  (when (eq (op-of (lhs rule1)) 'thm) 
    (let ((source (list (ruleno rule1) (ruleno rule2))) l1)
    (when (= (ruleno rule1) (ruleno rule2))
      (setq rule1 (make-new-rule (lhs rule1) (rhs rule1) (ctx rule1) 
                                 (rule-source rule1) (ruleno rule1))))
    (if* (truep (rhs rule1)) then
	(sloop for subst in (unifiers (first-arg (lhs rule1)) (first-arg arg1)) do
	  (if* (or (ctx rule1) (ctx rule2)) 
	      (setq l1 (handle-conditions (ctx rule1) (ctx rule2) subst)))
	  (if* (not-falsep l1) then
	      (setq $ncritpr (1+ $ncritpr)	
		    l1 (make-eqn
			  (list 'thm (applysubst subst (second-arg arg1)))
			  '(true)
			  l1 		      
			  source))
	      (if* (well-typed-eqn l1) (process-critpair l1 subst))))
	elseif (falsep (rhs rule1)) then
	(sloop for subst in (unifiers (first-arg (lhs rule1)) (second-arg arg1)) do
	  (if* (or (ctx rule1) (ctx rule2)) 
	      (setq l1 (handle-conditions (ctx rule1) (ctx rule2) subst)))
	  (if* (not-falsep l1) then
	      (setq $ncritpr (1+ $ncritpr)	
		    l1 (make-eqn
			 (list 'thm (applysubst subst (first-arg arg1)))
			 '(false)
			  l1 		      
			  source))
	      (if* (well-typed-eqn l1) (process-critpair l1 subst))))))))


