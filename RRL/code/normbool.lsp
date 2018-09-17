;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")



(defun norm-ctx (term &aux new) 
  (if* (or (variablep term) (truep term) (falsep term)) then term 
      elseif (and $instant (is-poly term))
      then (norm-poly term)
      else

      (if* $var-premises (setq term (subst-var-premises term)))

      (setq $false-rhs nil
	    new (if* (predicatep (op-of term)) 
		    then (norm-bool-innermost term)
		    else (norm-term term)))

      (if* (and $condi-dominate-rules (eq $condi-dominate 2))
	  (setq new (or (reduce-at-root-by-extra-prevars-rules new) new)))

      (if* (equal new term) then term
	  elseif (equal (setq term (flat-term new)) new) then new
	  else (norm-ctx term))))

(defun norm-ctx-and (t1 t2)
  ; Normalize conjunction of T1 and T2 if different.
  ; Return T1 if equal, T1 is in normalized form.
  (cond ((truep t2) t1)
	((truep t1) (norm-ctx t2))
	((falsep t1) t1)
	((equal t1 t2) (norm-ctx t1))
        (t (norm-ctx (simp-and (list t1 t2))))))

(defun norm-bool-innermost (b-term &aux nb-term)
  (setq $reduce-times $reduce-bound)
  (if* (or (truep b-term) (variablep b-term) (falsep b-term)) 
      then b-term
      else
    (case (op-of b-term)
	  (and (setq b-term (or (norm-and-args b-term) b-term))
	       (setq nb-term (bool-rewrite-at-root b-term)))

	  (or (setq b-term (or (norm-or-args b-term) b-term))
	      (setq nb-term (bool-rewrite-at-root b-term)))

	  (xor (setq b-term (or (norm-xor-term b-term) b-term))
	       (setq nb-term (bool-rewrite-at-root b-term)))

	  (= (setq nb-term		       
		   (if (and $induc (null (cdddr b-term)))
		       (simplify-my-eq-term b-term)
		     (bool-rewrite-at-root
		      (setq b-term (or (norm-eq-args (args-of b-term)) b-term))))))

	  (t (if (and (is-type-predicate (op-of b-term))
		       (not (well-typed3 b-term)))
		 (setq b-term $false-term)
	       (setq b-term (norm-term b-term)))
	     (if (and (nonvarp nb-term) 
		      (memq (op-of nb-term) '(xor or and =)))
		 (setq nb-term b-term)))
	  )
    (if nb-term (norm-bool-innermost nb-term) b-term))
  )

(defun norm-eq-args (eq-args)
  (setq eq-args (rem-dups (sort (mapcar 'norm-term eq-args) 'total-order)))
  (if (cdr eq-args)
       (make-term 'eq eq-args)
    $true-term))

(defun norm-xor-term (xor-term &aux new-args reducible)
  (setq new-args (sloop for arg in (args-of xor-term)
		       as new-arg = (norm-bool-innermost arg)
		       if (nequal new-arg arg) 
			 do  (setq reducible t)
		       collect new-arg))
  (if* reducible then (simp-xor new-args)))

(defun norm-or-args (or-term &aux new-args reducible)
  (setq new-args (sloop for arg in (args-of or-term)
			as new-arg = (norm-bool-innermost arg)
			if (nequal new-arg arg) 
			do (setq reducible t)
			collect new-arg))
  (if reducible (ba-simp-or new-args)))

(defun norm-and-args (and-term &aux new-args reducible)
  (setq new-args (sloop for arg in (args-of and-term)
			as new-arg = (norm-bool-innermost arg)
			if (nequal new-arg arg) 
			do (setq reducible t)
			collect new-arg))
  (if reducible (ba-simp-and new-args)))

(defun bool-rewrite-at-root (b-term)
  ; Returns rewritten term iff b-term can be rewritten.
  (or 
   (selectq (op-of b-term)
	    (xor (reduce-xor-term (args-of b-term)))
	    (and (reduce-and-term b-term))
	    (eq (reduce-eq-term b-term))
	    (t nil))
   (reduce-by-premises-at-root b-term (cdr $premises-set))))

(defun reduce-at-root-bool (term rule &aux l1)
  ; return the reduced term by rule.
  (if* (same-op term (lhs rule)) then
      (selectq (op-of term)
	(and (flat-term (reduce-and-term term (ncons rule))))
	(xor (flat-term (reduce-xor-term (args-of term) (ncons rule))))
;	(= (reduce-eq-term term (ncons rule)))
	(eq (reduce-eq-term term (ncons rule)))
	(t (if* (setq l1 (applies (lhs rule) term 
				 (polish-premises (ctx rule) rule))) then
	       (flat-term (add-to-args rule l1)))))))

(defun reduce-xor-term (args &optional rules)
  ; This operation is not integrated with AC because its high
  ; complexicity and rare usage.
  ; lhs of most rules are not rooted by "xor".
  (sloop for rule in (or rules 
			(rules-with-op
			  'xor
			  (if* (and $narrow $goal-reduce)
			      then (append $op_rules $op_goal_rules)
			      else $op_rules)))
	with rest-of-xor-args
	with rest-of-and-args
	with match-res
	with new
	do 
    (setq $false-rhs nil)
    (if* (and (null (ctx rule))
	     (setq match-res (match-bool-xor (args-of (lhs rule)) 
					     args (= $fast-match 2))))
	then (if* $trace-proof then (push (ruleno rule) $used-rule-nums))
	;; Structure of the value returned by match-bool-xor is
	;;    (rest-of-xor-args rest-of-and-args . substitution)
	(setq rest-of-xor-args (pop match-res)
	      rest-of-and-args (pop match-res)
	      new (applysubst match-res (rhs rule))
	      new (make-term 'and (if* (equal '(nil) rest-of-and-args)
				      then (ncons new)
				      else (cons new rest-of-and-args)))
	      new (make-term 'xor (cons new rest-of-xor-args)))
	(return new))))

(defun reduce-and-term (term &optional rules)
  ; "term" is rooted by "and". 
  ; If "term" is reducible at the root, then return the reduced term.
  ; Otherwise, nil.
  (sloop for rule in (or rules (rules-with-op 'and
				 (if* (and $narrow $goal-reduce)
				     then (append $op_rules $op_goal_rules)
				     else $op_rules)))
	with rest-of-args
	with match-res
	with res
	do
    (setq $false-rhs (falsep (rhs rule)))
    (if* (and (null (ctx rule))
	     (setq match-res (match-set (lhs rule) term (= $fast-match 2))))
	;; Structure of the value returned by match-set is
	;;    (rest-of-args . substitution)
	then (if* $trace-proof then (push (ruleno rule) $used-rule-nums))
	     (setq rest-of-args (pop match-res)
		   res (flat-term (applysubst match-res (rhs rule))))
	     (if* (null rest-of-args) 
		 then (return res)
		 else (return (simp-and (cons res rest-of-args)))))))

