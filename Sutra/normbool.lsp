;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "RRL")



(defun norm-ctx (old &aux new) 
  (if (variablep old) then old 
      elseif (and $instant (is-poly old))
      then (norm-poly old)
      else
      (setq $false-rhs nil
	    new (if (predicatep (op-of old)) 
		    then (norm-bool-innermost old)
		    else (norm-term old)))
      (if (equal new old) then old
	  elseif (equal (setq old (flat-term new)) new) then new
	  else (norm-ctx old))))

(defun norm-ctx-and (t1 t2)
  ; Normalize conjunction of T1 and T2 if different.
  ; Return T1 if equal, T1 is in normalized form.
  (cond ((truep t2) t1)
	((truep t1) (norm-ctx t2))
	((falsep t1) t1)
	((equal t1 t2) (norm-ctx t1))
        (t (norm-ctx (simp-and (list t1 t2))))))

(defun norm-bool-innermost (b-term &aux nb-term sub-nb-term top-nb-term)
  (setq $reduce-times $reduce-bound)
  (cond ((or (truep b-term) (variablep b-term) (falsep b-term)) b-term)
	((selectq 
	  (op-of b-term)
	  (xor (setq nb-term
		     (bool-rewrite-at-root
		      (if (setq sub-nb-term (norm-xor-term b-term))
			  then sub-nb-term
			  else (setq sub-nb-term b-term)))))
	  (and (setq nb-term
		     (bool-rewrite-at-root
		      (if (setq sub-nb-term (norm-and-args b-term))
			  then sub-nb-term
			  else (setq sub-nb-term b-term)))))
	  (eq (setq nb-term		       
		    (if (and $induc (null (cdddr b-term)))
			then (simplify-my-eq-term b-term)
			else
			(bool-rewrite-at-root
			 (setq sub-nb-term
			       (let ((eq-args (rem-dups
					       (sort (mapcar 'norm-term
							     (args-of b-term)) 
						     'total-order))))
				 (if (cdr eq-args)
				     then (make-term 'eq eq-args)
				     else '(true))))))))
	  (t (if (and (is-type-predicate (op-of b-term))
		      (not (well-typed3 b-term)))
		 then (setq sub-nb-term '(false)) nil
		 else
		 (setq sub-nb-term (brt-if (norm-term b-term) b-term)
		       nb-term sub-nb-term)
		 (if nb-term then
		   (and (nonvarp nb-term) 
			(memq (op-of nb-term) '(xor and eq)))))))
	 (if (setq top-nb-term (norm-bool-innermost nb-term))
	     then top-nb-term
	     else nb-term))
	(t sub-nb-term)))

(defun norm-xor-term (xor-term &aux new-args reducible)
  (setq new-args (loop for arg in (args-of xor-term)
		       as new-arg = (norm-bool-innermost arg)
		       if (nequal new-arg arg) 
			 do  (setq reducible t)
		       collect new-arg))
  (if reducible then (simp-xor new-args)))

(defun norm-and-args (and-term &aux new-args continue reducible)
  (setq new-args (loop for arg in (args-of and-term)
		       as new-arg = (norm-bool-innermost arg)
		       if (nequal new-arg arg) 
			 do (if (eq (op-of new-arg) 'xor)
				then (setq continue t)
				else (setq reducible t))
		       collect new-arg))
  (if continue
      then (norm-bool-innermost (simp-and new-args))
      elseif reducible then (simp-and new-args)))

(defun bool-rewrite-at-root (b-term)
  ; Returns rewritten term iff b-term can be rewritten.
  (selectq (op-of b-term)
    (xor (reduce-xor-term (args-of b-term)))
    (and (reduce-and-term b-term))
    (eq (reduce-eq-term b-term))
    (t nil)))

(defun reduce-at-root-bool (term rule &aux l1)
  ; return the reduced term by rule.
  (if (same-op term (lhs rule)) then
      (selectq (op-of term)
	(and (flat-term (reduce-and-term term (ncons rule))))
	(xor (flat-term (reduce-xor-term (args-of term) (ncons rule))))
	(eq (reduce-eq-term term (ncons rule)))
	(t (if (setq l1 (applies (lhs rule) term 
				 (polish-premises (ctx rule) (lhs rule)))) then
	       (flat-term (add-to-args rule l1)))))))

(defun reduce-xor-term (args &optional rules)
  ; This operation is not integrated with AC because its high
  ; complexicity and rare usage.
  ; lhs of most rules are not rooted by "xor".
  (loop for rule in (or rules 
			(rules-with-op
			  'xor
			  (if (and $narrow $goal-reduce)
			      then (append $op_rules $op_goal_rules)
			      else $op_rules)))
	with rest-of-xor-args
	with rest-of-and-args
	with match-res
	with new
	do 
    (setq $false-rhs nil)
    (if (and (null (ctx rule))
	     (setq match-res (match-bool-xor (args-of (lhs rule)) 
					     args (= $fast-match 2))))
	then (if $trace-proof then (push (ruleno rule) $used-rule-nums))
	;; Structure of the value returned by match-bool-xor is
	;;    (rest-of-xor-args rest-of-and-args . substitution)
	(setq rest-of-xor-args (pop match-res)
	      rest-of-and-args (pop match-res)
	      new (applysubst match-res (rhs rule))
	      new (make-term 'and (if (equal '(nil) rest-of-and-args)
				      then (ncons new)
				      else (cons new rest-of-and-args)))
	      new (make-term 'xor (cons new rest-of-xor-args)))
	(return new))))

(defun reduce-and-term (term &optional rules)
  ; "term" is rooted by "and". 
  ; If "term" is reducible at the root, then return the reduced term.
  ; Otherwise, nil.
  (loop for rule in (or rules (rules-with-op 'and
				 (if (and $narrow $goal-reduce)
				     then (append $op_rules $op_goal_rules)
				     else $op_rules)))
	with rest-of-args
	with match-res
	with res
	do
    (setq $false-rhs (falsep (rhs rule)))
    (if (and (null (ctx rule))
	     (setq match-res (match-set (lhs rule) term (= $fast-match 2))))
	;; Structure of the value returned by match-set is
	;;    (rest-of-args . substitution)
	then (if $trace-proof then (push (ruleno rule) $used-rule-nums))
	     (setq rest-of-args (pop match-res)
		   res (flat-term (applysubst match-res (rhs rule))))
	     (if (null rest-of-args) 
		 then (return res)
		 else (return (simp-and (cons res rest-of-args)))))))

