;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

#+franz (declare (special $gene))

#|
;; This function is in x_rrl.lsp
(defun abstract-proof (eqn num step &aux neweqns l2)
  (if* (and num ;; Don't generalize user's input. HZ: 8/5/91.
	   (neq (car (eqn-source eqn)) 'gene)
	   (setq neweqns (abstraction eqn))) then
      (sloop for n from 1 
	    for new in neweqns do
	(if* (> $trace_flag 1) then
	    (terpri) 
	    (princ "Generalize") (write-seq-eqn num eqn) 
	    (princ "    to") (write-seq-eqn (append1 num n) new))
	(setq new (reduction-proof new (append1 num n)))
	(if* (null new) then (return t)
	    elseif (not (falsep (lhs new))) then
	    ;(setq new (remove-irrelevant2 new ))
	    (setq l2 (cover-proof-process new step (append1 num n)))
	    (if* (> $trace_flag 1) then
		(trace-generated-result l2 (append1 num n) new num eqn))
	    (if* l2 then (return t)))
	finally (return nil))))
|#

(defun abstraction (eqn &aux subs used-subs)
  ;; Find a common subterm in both sides of "eqn" and replace it by a
  ;; variable.
  ;; Return new eqn if "eqn" is generazible. Otherwise, nil.

  ; If lhs and rhs share common subterm, generalize it.
  (setq subs (sub-nonvars (rhs eqn)))

  (sloop for sub in subs do
    (if* (and (is-subterm sub (lhs eqn))
	     (not (sloop for xa in used-subs thereis (is-subterm sub xa))))
	then
	(setq eqn (subst-eqn sub (make-new-variable)   
			     eqn (list 'gene (inc $gene-num))))
	(push sub used-subs)))

  ; If premises share subterm with lhs or rhs, then generalize it.
  (if* (ctx eqn) then
      (sloop for sub in (pre-sub-nonvars (cdr (ctx eqn)))
	    do (if* (and (not (sloop for xa in used-subs 
				   thereis (is-subterm sub xa)))
			(or (member0 sub subs)
			    (is-subterm sub (lhs eqn)) 
			    ))
		   then
		 (setq eqn (subst-eqn sub (make-new-variable)   
				      eqn (list 'gene (inc $gene-num))))
		 (push sub used-subs))))

  (when used-subs (ncons eqn)))

(defun car-lower (s1 s2) (is-higher-term (car s1) (car s2)))

#|
;; in xrrl.lsp
(defun trace-generated-result (done num2 new num eqn)
   (terpri)
   (if* done 
     then (princ "Generated lemma is proven: ") (terpri) 
          (princ "   ") (write-seq-eqn num2 new)
     else (princ "Fail to prove the generated lemma: ") (terpri)
          (princ "   ") (write-seq-eqn num2 new)
	  (princ " of") (write-seq-eqn num eqn)))
|#

(defun subst-eqn (old new eqn &optional parents &aux lhs rhs ctx) 
  (setq lhs (flat-term (subst0 new old (lhs eqn)))
	rhs (flat-term (subst0 new old (rhs eqn)))
	ctx (subst0 new old (ctx eqn)))
  (if* (nequal ctx (ctx eqn)) then (setq ctx (remake-premises ctx)))
  (make-eqn lhs rhs ctx (if* parents then parents else (eqn-source eqn))))

(defun eqn-sub-nonvars (eqn)
   (rem-dups (nconc (sub-nonvars2 (lhs eqn)) (sub-nonvars2 (rhs eqn))
		    (if* (ctx eqn) then 
			(if* (eq (car (ctx eqn)) '*&*)
			    then (pre-sub-nonvars (cdr (ctx eqn)))
			    else (sub-nonvars2 (ctx eqn)))))))

(defun pre-sub-nonvars (pres)
   (rem-dups (sloop for pre in pres append (sub-nonvars2 (car pre)))))

(defun sub-nonvars (term) (rem-dups (sub-nonvars2 term t)))

(defun sub-nonvars2 (term &optional top &aux res)
  (if* (variablep term) then nil
      elseif (not (is-ground term))
      then
      (setq res (mapcan 'sub-nonvars2 (args-of term)))
      (if* (or top (memq (op-of term) $constructors))
	  then res else (cons term res))))

(defun is-higher-term (t1 t2)
  ; Return t iff ti is higher than t2.
  (if* (is-subterm t1 t2) then nil
      elseif (is-subterm t2 t1) then t
      else (lessp (op-position (op-of t2) $operlist)
		  (op-position (op-of t1) $operlist))))

(defun op-position (e lis)
  (sloop for xa in lis for n from 1 if (equal xa e) return n finally (return 0)))
