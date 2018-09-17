;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "RRL")

#+franz (declare (special $gene))

(defun abstract-proof (eqn num step &aux neweqns l2)
  (if (and (neq (car (eqn-source eqn)) 'gene)
	   (setq neweqns (abstraction eqn))) then
      (loop for n from 1 
	    for new in neweqns do
	(if (> $trace_flag 1) then
	    (terpri) 
	    (princ "Generalize") (write-seq-eqn num eqn) 
	    (princ "    to") (write-seq-eqn (append1 num n) new))
	(setq new (reduction-proof new (append1 num n)))
	(if (null new) then (return t)
	    elseif (not (falsep (lhs new))) then
	    ;(setq new (remove-irrelevant2 new ))
	    (setq l2 (one-induction new step (append1 num n)))
	    (if (> $trace_flag 1) then
		(trace-generated-result l2 (append1 num n) new num eqn))
	    (if l2 then (return t)))
	finally (return nil))))

(defun abstraction (eqn &aux eqns subs eqns2)
  ;; Find a common subterm in both sides of "eqn" and replace it by a
  ;; variable.
  ;; Return new eqn if "eqn" is generazible. Otherwise, nil.

  ; If lhs and rhs share common subterm, generalize it.
  (loop for sub in (setq subs (sub-nonvars (rhs eqn))) do
    (if (is-subterm sub (lhs eqn)) then
	(push (cons sub (subst-eqn sub (make-new-variable)   
				   eqn (list 'gene (inc $gene-num))))
	      eqns)))

  ; If premises share subterm with lhs or rhs, then generalize it.
  (if (ctx eqn) then
      (loop for sub in (pre-sub-nonvars (cdr (ctx eqn))) 
	    if (not (member sub subs))
	      do (if (or (is-subterm sub (lhs eqn)) 
			 (is-subterm sub (rhs eqn))) then
		     (push (cons sub (subst-eqn sub (make-new-variable)   
						eqn (list 'gene (inc $gene-num))))
			   eqns))))
  (if eqns then
      (if (cdr eqns) then 
	  (setq eqns (sort eqns 'car-lower))
	  (setq subs (mapcar 'car eqns)
		eqns (mapcar 'cdr eqns))

	  (loop with eqn1 = (first eqns)
		with sub1 = (first subs)
		for sub in (cdr subs) do
	    (if (not (is-subterm sub sub1)) then 
		(setq eqn (subst-eqn sub (make-new-variable)
				     eqn1 (list 'gene (inc $gene-num))))
		(push-end eqn eqns2)
		(return)))

	  (pop subs)
	  (loop with eqn1 = (first eqns2)
		with sub1 = (first subs)
		for sub in (cdr subs) do
	    (if (not (is-subterm sub sub1)) then 
		(setq eqn (subst-eqn sub (make-new-variable)
				     eqn1 (list 'gene (inc $gene-num))))
		(push-end eqn eqns2)
		(return)))
	  (append (reverse eqns2) eqns)
	  else
	  (ncons (cdar eqns)))))

(defun car-lower (s1 s2) (is-higher-term (car s1) (car s2)))

(defun trace-generated-result (done num2 new num eqn)
   (terpri)
   (if done 
     then (princ "Generated lemma is proven: ") (terpri) 
          (princ "   ") (write-seq-eqn num2 new)
     else (princ "Fail to prove the generated lemma: ") (terpri)
          (princ "   ") (write-seq-eqn num2 new)
	  (princ " of") (write-seq-eqn num eqn)))

(defun subst-eqn (old new eqn &optional parents &aux lhs rhs ctx) 
  (setq lhs (flat-term (subst new old (lhs eqn)))
	rhs (flat-term (subst new old (rhs eqn)))
	ctx (subst new old (ctx eqn)))
  (if (nequal ctx (ctx eqn)) then (setq ctx (remake-premises ctx)))
  (make-eqn lhs rhs ctx (if parents then parents else (eqn-source eqn))))

(defun eqn-sub-nonvars (eqn)
   (rem-dups (nconc (sub-nonvars2 (lhs eqn)) (sub-nonvars2 (rhs eqn))
		    (if (ctx eqn) then 
			(if (eq (car (ctx eqn)) '&&)
			    then (pre-sub-nonvars (cdr (ctx eqn)))
			    else (sub-nonvars2 (ctx eqn)))))))

(defun pre-sub-nonvars (pres)
   (rem-dups (loop for pre in pres append (sub-nonvars2 (car pre)))))

(defun sub-nonvars (term) (rem-dups (sub-nonvars2 term t)))

(defun sub-nonvars2 (term &optional top &aux res)
  (if (variablep term) then nil
      elseif (null (all-vars term)) then nil
      else (setq res (mapcan 'sub-nonvars2 (args-of term)))
      (if (or top (memq (op-of term) $free-constructors))
	  then res else (append1 res term))))

(defun is-higher-term (t1 t2)
  ; Return t iff ti is higher than t2.
  (if (is-subterm t1 t2) then nil
      elseif (is-subterm t2 t1) then t
      else (lessp (position (op-of t2) $operlist)
		  (position (op-of t1) $operlist))))

(defun position (e lis)
  (loop for xa in lis for n from 1 if (equal xa e) return n finally (return 0)))
