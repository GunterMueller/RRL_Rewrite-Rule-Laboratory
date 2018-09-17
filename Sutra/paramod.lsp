;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "RRL")

(defun paramodulate (lhs1 lhs2 rule1 rule2 atom1 mon2 atom2)
  ; This function performs paramodulation of rule1 on rule2
  ; lhs1 is the lhs of rule1
  ; lhs2 is the lhs of rule2
  ; atom1 is an atomic formula in lhs1 of the form eq(s1, ..., sn)
  ; atom2 is some atomic formula in lhs2
  ; we are going to try to unify some si with some subterm in atom2
  ; if the unification succeeds and i > 1 then the superposition is formed by replacing si with s1.
  ; if i = 1 then we have to do the replacing with all the si's.
  (if (and (falsep (rhs rule1)) (null (cdr (args-of lhs1))))	; rule1 is of the form mon == false.
      then nil					; paramodulation will not yield any thing in this case.
      else (loop with atom1-args = (args-of atom1)	; these are the si's
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
  (if (and root (nonvarp sub2)) then
      (para-sup-term2 term1 atom2 sub2 pos term1prime mon2 lhs1 lhs2 rule1 rule2))
  (if (nonvarp sub2) then
      (loop for xa in (args-of sub2) as l1 from 1
	    do
	(para-sup-term term1 atom2 xa (append1 pos l1) t term1prime mon2 lhs1 lhs2 rule1 rule2))))

(defun para-sup-term2 (term1 atom2 sub2 pos term1prime mon2 lhs1 lhs2 rule1 rule2 &aux subst)
  ; If sub2 unifies with term1 using substitution sigma, then the new superposition becomes:
  ; sigma(lhs2[sub2<-term1prime] xor rhs2) and
  ; sigma(lhs1(without monomials containing eq(term1 term1prime)) xor
  ;    rhs1(without monomials containing eq(term1 term1prime)))
  (if (setq subst (add-time $unif_time (unifier term1 sub2)))
      then (let* ((new-atom2 (rplat-in-by pos atom2 term1prime))
		  (new-mon2 `(and ,new-atom2 ,(remonce atom2 mon2)))
		  (new-lhs2 `(xor ,new-mon2 ,(remonce mon2 lhs2)))
		  (new-ass-2 (applysubst subst `(xor ,(rhs rule2) ,new-lhs2)))
		  (new-lhs1-args (loop for mon in (args-of lhs1)
				       when (not (eq-in-monomial term1 term1prime mon))
					 collect mon))
		  (new-lhs1 (make-term 'xor new-lhs1-args))
		  (new-rhs1-args (loop for mon in (args-of (canonicalize (rhs rule1)))
					when (not (eq-in-monomial term1 term1prime mon))
					  collect mon))
		  (new-rhs1 (make-term 'xor new-rhs1-args))
		  (new-ass-1 (applysubst subst `(xor ,new-lhs1 ,new-rhs1)))
		  (new-ass `(xor (true) (and ,new-ass-1 ,new-ass-2))))
	     (if (well-typed new-ass) then
		 (setq new-ass (flat-term new-ass))
		 (if (> $trace_flag 2) then
		     (trace-para (list (ruleno rule1) (ruleno rule2)) new-ass))
		 (process-ass-simple new-ass (list (ruleno rule1) (ruleno rule2)))))))

(defun eq-in-monomial (t1 t2 mon)
  ; returns true if mon contains an eq whose arguments contain both t1 and t2.
  (loop for atom in (half-canonicalize mon)
	thereis
	  (and (eq (op-of atom) 'eq)
	       (loop with t1in = nil
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
