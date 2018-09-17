;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")


(defun reduce-eq-term (term &optional rules &aux res)
  ;; This function first tries to find a rule whose lhs is an eq
  ;; with the same number of arguments as "term".
  ;; If it can use such a rule for rewriting then it will do so.
  ;; Otherwise it looks for a rule wth eq that will rewrite some
  ;; subset of the args of "term" to false in this case it returns false.
  ;; otherwise it returns nil.  
  (setq rules (or rules 
		  (rules-with-op 'eq
				 (if* (and $narrow $goal-reduce)
				     then (append $op_rules $op_goal_rules)
				     else $op_rules))))
  (if* (setq res (reduce-eq-exactly term rules)) then res else
      (sloop with largs = (length term)
	    with desired = nil
	    with rest-args = nil
	    for args = (args-of term)
		     then ; Deleting an arg from "args", 
		(sloop for arg in args 
		      if (not (memq arg rest-args)) 
			return (remq arg args 1)
		      finally (cdr args))
	    while (and (null desired) (cdr args)) ; If more than one args left,
	    do
	(setq $false-rhs nil
	      desired
	      (sloop for rule in rules
		    with sigma
		    with temp
		    if (and (< (length (lhs rule)) largs) (not (falsep (rhs rule))))
		      do
			(if* (setq sigma (match-set (lhs rule) (make-term 'eq args))) 
			    ;; Structure of the value returned by match-set:
			    ;;    (rest-of-args . substitution)
			    then (setq rest-args (car sigma)
				       sigma (cdr sigma)
				       temp (norm-ctx (flat-term 
							(applysubst sigma (rhs rule)))))
			    (if* (falsep temp) then
				(if* $trace-proof then
				    (push (ruleno rule) $used-rule-nums))
				(return temp)))
		    finally (return nil)))
            ; desired is non nil only if it is false.
	    finally (return desired))))

(defun reduce-eq-exactly (term rules)
  ; Returns nil if there doese not exist a rule
  ; whose lhs is of the form: (eq t1, ..., tn)
  ; where n is the length of args and there is a sigma, 
  ; st sigma(lhs) = term. 
  ; if there is such a rule then this returns sigma(rhs).
  (sloop	with largs = (length term)
	with res-subst
	for rule in rules
	as lhs = (lhs rule)
	as llhs = (length lhs)
	when (and (>= largs llhs)
		  (or (setq $false-rhs (falsep (rhs rule)))
		      (eq largs llhs))
		  (setq res-subst (eq-match lhs term))
		  (if* $trace-proof then
		      (push (ruleno rule) $used-rule-nums) else t))
	return (norm-ctx (flat-term (applysubst res-subst (rhs rule))))))

(defun eq-tr (terms)
  ;  Returns term with arguments passed through the eq-find and
  ;  the transitive closure algorithms.
  (let (others eqlist trlist)
     (sloop for term in terms do
            (cond ((eq (op-of term) 'eq) (push term eqlist))
                  ((member0 (op-of term) $translist) 
                   (setq trlist (add-associate-list
					(op-of term) (copylist term) trlist)))
                  (t (push term others))))
     (append (if* eqlist (eq-find eqlist)) 
	     (if* trlist (tr-find trlist)) others)))

(defun eq-find (eq-pairs)
  ; Control function for the union find algorithm.
  ; Returns terms with appropriate eq's joined.
  (sloop with eqlists = nil for xa in eq-pairs 
	do (setq eqlists (eq-add (args-of xa) eqlists))
	finally (return (sloop for xa in eqlists collect
		         (cond ((null (cdr xa)) '(true))
	                       (t (make-term 'eq (sort xa 'total-order))))))))

(defun eq-add (elist eqlists)
  ; Adds a set of equivalent terms to the equivalent classes for the
  ; eq-find algorithm. Returns the new equaivalence classes.
  ; The union function is also used to filter out doubles.
  (cond ((null eqlists) (ncons (rem-dups elist)))
        ((intersection (car eqlists) elist)
         (eq-join (union (car eqlists) elist) elist (cdr eqlists)))
        (t (cons (car eqlists) (eq-add elist (cdr eqlists))))))

(defun eq-join (elist1 elist2 eqlists)
  ; Looks for possible union of equivalence classes do to elist2.
  ; Returns new list of equivalence classes.
  (cond ((null eqlists) (list elist1))
        ((have-common (car eqlists) elist2)
         (eq-join (union (car eqlists) elist1) elist2 (cdr eqlists)))
        (t (cons (car eqlists) (eq-join elist1 elist2 (cdr eqlists))))))

(defun tr-find (op-trlist &aux trlists op)
  ;  Control function for the transitive closure algorithm.
  ;         Returns terms with closured transitive predicates.
  ;         $translist is the list of transitive operators.
  (sloop for terms in op-trlist nconc
    (progn (setq op (pop terms) 
		 trlists nil)
	(sloop for xa in terms do
	     (setq trlists (tr-add (args-of xa) trlists)))
	(sloop for tlist in (tr-closure trlists) nconc
	     (tr-term op (car tlist) (cdr tlist))))))

(defun tr-add (args trlists)
  ; Adds a related pair to the strcuture for the transitive closure algorithm.
  (let ((l1 (assoc0 (car args) trlists)))
    (if* l1 then (rplacd l1 (union (cdr l1) (cdr args))) trlists
           else (cons args trlists))))

(defun tr-closure (trlists)
  ;  Does the actual transitive closure algotrithm.
  (let (unmarked adns)
    (sloop for current in trlists do
      (setq unmarked (remove0 current trlists) adns t)
      (sloop while adns do
        (setq adns nil
              unmarked (sloop for x in unmarked 
                        if (if* (member0 (car x) (cdr current)) 
	                        then (rplacd current (union (cdr current) 
							    (cdr x)))
	                             (setq adns t)
	                              nil
	                        else t)
	                 collect x))))
   trlists))

(defun tr-term (oper left tlist)
  ;  Takes a list of the transitive closure association list,
  ;         and returns a the appropriate list of terms.
  ;         returns false if a cycle is found and OPER is irreflexive.
  (cond ((member0 left tlist)
         (cond ((get oper 'irreflexive) '((false)))
               ((setq tlist (delete0 left tlist)) 
                (sloop for x in tlist collect (make-term oper (list left x))))
               (t '((true)))))
        (t (sloop for x in tlist collect (make-term oper (list left x))))))

(defun idem-eq-critical (rule l1 ruleno &aux l2)
   ; Computing critical pairs with EQ predicate.
   (sloop while (cdr l1) do
      (setq l2 (pop l1))
      (sloop for xa in l1 do
          (add-time $unif_time (setq xa (unifier l2 xa)))
	  (if* xa then
	     (setq $ncritpr (1+ $ncritpr)
  	           xa (applysubst xa `(xor (true) ,(lhs rule) ,(rhs rule))))
  	     (if* (eq $trace_flag 3) then (trace-crit ruleno xa t))
	     (process-ass-simple (make-flat xa) ruleno)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; from paramod.lsp

(defun paramodulate (lhs1 lhs2 rule1 rule2 atom1 mon2 atom2)
  ; This function performs paramodulation of rule1 on rule2
  ; lhs1 is the lhs of rule1
  ; lhs2 is the lhs of rule2
  ; atom1 is an atomic formula in lhs1 of the form eq(s1, ..., sn)
  ; atom2 is some atomic formula in lhs2
  ; we are going to try to unify some si with some subterm in atom2
  ; if the unification succeeds and i > 1 then the superposition is formed by replacing si with s1.
  ; if i = 1 then we have to do the replacing with all the si's.
  (if* (and (falsep (rhs rule1)) (null (cdr (args-of lhs1))))	; rule1 is of the form mon == false.
      then nil					; paramodulation will not yield any thing in this case.
      else (sloop with atom1-args = (args-of atom1)	; these are the si's
		 with s1 = (car atom1-args)
		 for s in (cdr atom1-args)
		 do
	     (para-sup-term s atom2 atom2 nil nil s1
			    mon2 lhs1 lhs2 rule1 rule2)
	     (para-sup-term s1 atom2 atom2 nil nil s
			    mon2 lhs1 lhs2 rule1 rule2))))
					  
(defun para-sup-term (term1 atom2 sub2 pos root term1prime mon2 lhs1 lhs2 rule1 rule2)
  ; sub2 is a subterm of the atomic formula atom2.
  ; pos is the position of sub2 in atom2.
  ; This function will try to unify sub2 and all its subterms with term1.
  ; para-sup-term2 will do all the real work in forming the superposition.
  (if* (and root (nonvarp sub2)) then
      (para-sup-term2 term1 atom2 sub2 pos term1prime mon2 lhs1 lhs2 rule1 rule2))
  (if* (nonvarp sub2) then
      (sloop for xa in (args-of sub2) as l1 from 1
	    do
	(para-sup-term term1 atom2 xa (append1 pos l1) t term1prime mon2 lhs1 lhs2 rule1 rule2))))

(defun para-sup-term2 (term1 atom2 sub2 pos term1prime mon2 lhs1 lhs2 rule1 rule2 &aux subst)
  ; If sub2 unifies with term1 using substitution sigma, then the new superposition becomes:
  ; sigma(lhs2[sub2<-term1prime] xor rhs2) and
  ; sigma(lhs1(without monomials containing eq(term1 term1prime)) xor
  ;    rhs1(without monomials containing eq(term1 term1prime)))
  (if* (setq subst (add-time $unif_time (unifier term1 sub2)))
      then (let* ((new-atom2 (rplat-in-by pos atom2 term1prime))
		  (new-mon2 `(and ,new-atom2 ,(remonce atom2 mon2)))
		  (new-lhs2 `(xor ,new-mon2 ,(remonce mon2 lhs2)))
		  (new-ass-2 (applysubst subst `(xor ,(rhs rule2) ,new-lhs2)))
		  (new-lhs1-args (sloop for mon in (args-of lhs1)
				       when (not (eq-in-monomial term1 term1prime mon))
					 collect mon))
		  (new-lhs1 (make-term 'xor new-lhs1-args))
		  (new-rhs1-args (sloop for mon in (args-of (canonicalize (rhs rule1)))
					when (not (eq-in-monomial term1 term1prime mon))
					  collect mon))
		  (new-rhs1 (make-term 'xor new-rhs1-args))
		  (new-ass-1 (applysubst subst `(xor ,new-lhs1 ,new-rhs1)))
		  (new-ass `(xor (true) (and ,new-ass-1 ,new-ass-2))))
	     (if* (well-typed new-ass) then
		 (setq new-ass (flat-term new-ass))
		 (if* (> $trace_flag 2) then
		     (trace-para (list (ruleno rule1) (ruleno rule2)) new-ass))
		 (process-ass-simple new-ass (list (ruleno rule1) (ruleno rule2)))))))

(defun eq-in-monomial (t1 t2 mon)
  ; returns true if mon contains an eq whose arguments contain both t1 and t2.
  (sloop for atom in (half-canonicalize mon)
	thereis
	  (and (eq (op-of atom) 'eq)
	       (sloop with t1in = nil
		     with t2in = nil
		     for s in (args-of atom)
		     do
		 (cond ((equal s t1) (setq t1in t))
		       ((equal s t2) (setq t2in t)))
		     finally (return (and t1in t2in))))))

(defun trace-para (rns crit)
    (terpri) (princ (uconcat "    Rule [" (car rns) 
			     "] paramodulates on [" (cadr rns)
		  	     "] yielding the following critical pair: "))
    (terpri) (princ "    ")
    (write-assertion `(,rns . ,crit)))
