;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "RRL")



;-- file containing normalization procedures for non-ac, ac and conditional.
;-- Ac has no separate functions. innermost and outermost are same.
;-- Have removed use of global variables like mbinds for some
;-- procedures. Same needs to be done for conditional etc.

#+franz (declare (special $avoid-rules $deep-condi))

#+franz (setq $avoid-rules nil
	      $deep-condi 3)

(defun is-normal (term) (not (reducible term)))

(defun check-norm (eqn &aux eqn2)
  ; If eqn is composed of two assertions, then using the predicate equ.
  ; Check if the normal forms are the same.
  (cond ((equal-term (lhs eqn) (rhs eqn)) nil)
	($induc
	 (if (and (setq eqn2 (induc-checkeq eqn)) (car eqn2)) 
	     then eqn2))
	((and (is-assertion eqn)
	      (eq (op-of (lhs eqn)) 'eq) 
	      (null (cdddr (lhs eqn))))
	 (setq eqn2 (make-eqn (first-arg (lhs eqn)) 
			      (second-arg (lhs eqn)) nil (eqn-source eqn)))
	 (if (= $trace_flag 3) then
	     (terpri) (princ "Transform assertion ") (write-eqn eqn)
	     (princ "  to equation ") (write-eqn eqn2))
	 (checkeq-normal eqn2))
	((is-assertion eqn) eqn)
	((is-prop-eqn eqn)
	 (setq eqn2 (ass2eqn (eqn2assertion eqn) (eqn-source eqn)))
	 (if (= $trace_flag 3) then
	     (terpri) (princ "Transform equation ") (write-eqn eqn)
	     (princ "  to assertion ") (write-eqn eqn2))
	 eqn2)
	(t (checkeq-normal eqn))))

(defun checkeq-normal (eqn &optional consistent &aux lhs rhs)
  ; Checks if a critical pair is trivial.  Returns NIL if after
  ; normalizing both sides of EQN they are equal; otherwise,
  ; returns a new equation of the normalized form of both sides.
  ; Normalize both sides of EQN using the strategy set by the user in the
  ; flag NORM_STR, then see if they are equal.

  ; avoiding rules bite one's own tails.
  (setq $avoid-rules nil)

  (if (not (equal (lhs eqn) (rhs eqn))) then
      (setq $used-rule-nums nil
	    lhs (norm-ctx (lhs eqn))
	    rhs (norm-rhs (rhs eqn)))
      (if (and $induc (nonvarp rhs) (nonvarp lhs)) then
	  (if (and (truep rhs) (eq (op-of lhs) '=)
		   (is-subset (all-vars (second-arg lhs)) (all-vars (first-arg lhs))))
	      then (setq rhs (second-arg lhs)
			 lhs (first-arg lhs))
	      elseif (and (eq (op-of lhs) 'xor) (member '(true) lhs))
	      then (setq lhs (negate-predicate lhs)
			 rhs (negate-predicate rhs))))
		     
      (if (equal-term lhs rhs) then nil else
	  (setq eqn (make-eqn lhs rhs nil 
			      (append (eqn-source eqn)
				      (if $trace-proof (rem-dups $used-rule-nums))))
		$used-rule-nums nil)
	  (if (not consistent) then (last-consistency-check eqn) else eqn))))

(defun pure-checkeq-normal (eqn &optional consistent &aux lhs rhs)
  ; Checks if a critical pair is trivial.  Returns NIL if after
  ; normalizing both sides of EQN they are equal; otherwise,
  ; returns a new equation of the normalized form of both sides.
  ; Normalize both sides of EQN using the strategy set by the user in the
  ; flag NORM_STR, then see if they are equal.
  (setq $used-rule-nums nil
	lhs (pure-norm (lhs eqn))
	rhs (pure-norm (rhs eqn)))
  (if (equal lhs rhs) then nil else
      (setq eqn (make-eqn lhs rhs nil 
			  (append (eqn-source eqn)
				  (if $trace-proof (rem-dups $used-rule-nums))))
	    $used-rule-nums nil)
      (if (not consistent) then (last-consistency-check eqn) else eqn)))

(defun last-consistency-check (eqn)
  (if (and (not (is-oneway eqn)) (lrpo (rhs eqn) (lhs eqn)))
      then (setq eqn (exchange-lr eqn)))
  (if (and (nonvarp (lhs eqn))
	   (eq (op-of (lhs eqn))'=)
	   (null (all-vars (rhs eqn)))
	   (not (consistent-pair (args-of (lhs eqn))
				 (var-consistency (lhs eqn)))))
      then (if (falsep (rhs eqn)) then (setq eqn nil)
	       else (setq eqn (change-lhs eqn '(false))))
      else eqn))

(defun norm-term (term)
  ; Normalize TERM using the strategy set by the user in the flag NORM_STR.
  (setq $reduce-times $reduce-bound)
  (if (or $premises-set $var-premises) 
      (setq term (normalize-by-premises term)))
  (norm-outermost term))

(defun pure-norm (term)
  ; Normalize TERM using the strategy set by the user in the flag NORM_STR.
  (setq $reduce-times $reduce-bound)
  (selectq $norm_str
	   (e (pure-norm-inn term))
	   (o (pure-norm-outermost term))
	   (i (pure-norm-innermost term))
	   (m (pure-norm-mixed term))))

(defun reducible (term)
  ; Try left-most outermost reduction on TERM. Return "t" iff TERM
  ; is reducible.
  (cond ((variablep term) nil)
        ((loop for rule in (get-rules-with-op (op-of term) nil)
	       thereis (applies (lhs rule) term 
				(polish-premises (ctx rule) (lhs rule)))) t)
        (t (loop for t1 in (args-of term) thereis (reducible t1)))))

(defun guide-reducible (guide term)
  ;  Try left-most outermost reduction on TERM. Return "t" iff TERM
  ;  is reducible.
  (cond ((variablep guide) nil)
        ((loop for rule in (get-rules-with-op (op-of term) nil)
	       thereis (applies (lhs rule) term)) t)
        (t (loop for t1 in (args-of term) 
	         as g1 in (args-of guide) thereis (guide-reducible g1 t1)))))

(defun rewrite-at-root (term &optional op-rules)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (if (nonvarp term) 
      (let ((op (op-of term)))
	(cond 
	  ((memq op '(false true 0)) nil)
	  ((eq op '=) (simplify-my-eq-term term))
	  ((and (memq op $ac)
		(loop for xa in $character-rules 
		      if (eq op (caddr xa))
			return (reduce-by-character xa term))))
	  ((and (memq op $ac)
		(loop for xa in $p-commut-rules 
		      if (eq op (cadr xa))
			return (reduce-by-p-commut xa term))))
	  ((and $cycle-rule (assoc op $cycle-op-rules)
		(cycle-rewrite-at-root 
		 term (rules-with-op op $cycle-op-rules))))
	  ((and $polynomial (memq op '(+ *))) 
	   (poly-reduce-at-root term op-rules))
	  (t (reduce-at-root term op-rules))))))
				
(defun reduce-at-root (term op-rules)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (loop with subst = nil 
	for rule in (get-rules-with-op (op-of term) op-rules)
	if (setq subst (try-one-rule rule term))
	return (if (cycle-check term)
		   (if $ac
		       (add-to-args rule subst)
		       (c-permu (sublis subst (rhs rule)))))
	finally (return (if (cdr $premises-set) 
			    (reduce-by-premises-at-root term (cdr $premises-set))))))

(defun try-one-rule (rule term &aux subst used-rules)
  (if (ctx rule) then 
      (if (= $deep-condi 0)
	  then nil
	  else
	  (setq $deep-condi (sub1 $deep-condi)
		used-rules $used-rule-nums 
		$used-rule-nums nil
		subst (applies (lhs rule) term
			       (polish-premises (ctx rule) (lhs rule)))
		$deep-condi (1+ $deep-condi))
	  (setq $used-rule-nums (if subst
				    then (append $used-rule-nums 
						 (cons (ruleno rule) used-rules))
				    else used-rules))
	  subst)
      elseif (setq subst (applies (lhs rule) term))
      then (if $trace-proof (push (ruleno rule) $used-rule-nums))
      subst))

(defun reduce-at-root-one-rule (term rule &aux subst)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (if (setq subst (try-one-rule rule term)) then
      (if $trace-proof then (push (ruleno rule) $used-rule-nums))
  (flat-term (add-to-args rule subst))))

(defun simplify-my-eq-term (term &aux l1 t1 t2)
  (setq t1 (first-arg term)
	t2 (second-arg term))
  (if (equal t1 t2) then '(true)
      elseif (setq l1 (reduce-at-root term nil))
      then l1
      else
      (setq t1 (norm-outermost t1)
	    t2 (norm-outermost t2))
      (if (equal t1 t2) then '(true)
	  elseif (not (setq l1 (consistent-pair (list t1 t2) t)))
	  then '(false)
	  elseif (and (neq l1 t) (neq (car l1) 'and))
	  then (make-term '= l1)
	  else
	  (if (total-order t1 t2) then (setq l1 t1 t1 t2 t2 l1))      
	  (setq l1 (list '= t1 t2))
	  (if (nequal l1 term) then l1 
	      elseif (cdr $premises-set)
	      then (reduce-by-premises-at-root term (cdr $premises-set))))))

(defun var-consistency (term)
  ; Return t iff the pair like x = f(y) or x = 0 is a consistent relation.
  (and $premises-set
       (related-vars 
	 (mapcar 'pre-vars (cdr $premises-set)) (all-vars term))))

(defun add-to-args (rule subst)
  (if (assq '$extra subst)
      then (add-rest-args (applysubst subst (rhs rule)) 
			  (cdr (assq '$extra subst)))
      else (apply-to (rhs rule) subst)))

(defun add-rest-args (arg t1)
  (if t1 then 
      (if (or (variablep arg) (not (same-op t1 arg)))
         then (make-term (op-of t1) (cons arg (args-of t1)))
         else (make-term (op-of t1) (append (args-of t1) (args-of arg))))
     else arg))

(defun rewonce-at-root (term &aux t2)
   (if (setq t2 (rewrite-at-root term)) then t2 else term))

(defun normalize ()
  ; Lets the user normalize a term with the current set of rules.
  ; It has its own sub-toplevel for related options.
  ; Assumes norm-cterm returns a list of conditional terms.
  (terpri)
  (princ "Please use `prove' to get a normal form of a term.") (terpri)
  (princ "    Input <TERM> == result to RRL after typing 'prove',") (terpri)
  (princ "    RRL will return the normal form of <TERM>.") (terpri)
  (princ "Sorry for inconvenience.") (terpri) (terpri))

(defun cycle-check (term)
  ; retrun t iff there is no cycle.;
  ; return nil iff there is a possible cycle and $abk_flag is on.
  ; reset iff there is a possible cycle and $akb_flag is off.
  (if (= 0 (setq $reduce-times (sub1 $reduce-times))) then
    (terpri) (princ "There is a possible loop in the rewriting system.") 
    (terpri) (princ (uconcat "One term after " $reduce-bound " rewrites is "))
    (setq $reduce-times $reduce-bound)
    (loop for i from 1 to 10 do
      (terpri) (princ "         ") (write-term term)
      (setq term (reduce-by-rules term $rule-set))
      (if (null term) (return)))
    (terpri)
    (if term 
	(princ "         ... ...") 
      (princ
       "The system is terminating; please set a bigger normalization bound."))
    (terpri)
    (if $akb_flag nil (reset))
    else
    t))

(defun ac-compress (op args)
  (cond
     ($ac (compress-flat op args))
     ((commutativep op)	(make-term op (commu-exchange args)))
     (t (make-term op args))))

(defun reduce-by-rules (term rules &aux t2)
  ; Return the reduced form of term if  rules can reduce it. Otherwise, nil.
  (loop for rule in rules do
        (if (setq t2 (reduce-by-one-rule term rule)) then (return t2))))

(defun reduce-by-one-rule (term rule)
  ; Tries to rewrite TERM at some position using RULE.
  (cond ((variablep term) nil)
        ((and (same-root term (lhs rule)) (reduce-by-one-at-root term rule)))
        ((loop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (reduce-by-one-rule xa rule)))
	     return (flat-term (rplnthsubt-in-by i term xa))
	   finally (return nil)))))

(defun reduce-by-one-at-root (term rule &optional pres &aux l1)
  ; Tries to rewrite TERM at some position using RULE.
  (setq $premises-set pres)
  (cond ((variablep term) nil)
        ((setq l1 (if $polynomial
		      then (poly-reduce-at-root-one-rule term rule)
		      elseif (ctx rule) 
		      then (reduce-at-root-one-rule term rule)
		      else (reduce-at-root-bool term rule))) l1)
	(t nil)))

(defun pure-reduce-by-one-rule (term rule)
  ; Tries to rewrite TERM at some position using RULE.
  (cond ((variablep term) nil)
        ((and (same-root term (lhs rule)) 
	      (pure-reduce-by-one-at-root term rule)))
        ((loop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (pure-reduce-by-one-rule xa rule)))
	     return (rplnthsubt-in-by i term xa)
	   finally (return nil)))))

(defun pure-reduce-by-one-at-root (term rule &aux subst)
  ; Tries to rewrite TERM at some position using RULE.
  (cond ((variablep term) nil)
	((if (setq subst (pure-match (lhs rule) term)) then
	     (if $trace-proof then (push (ruleno rule) $used-rule-nums))
	     (sublis subst (rhs rule))))
	(t nil)))

(defun polish-premises (pres term &aux vars (old $deep-condi))
  ; Return (intersection of vars in pres and that of term . pres)
  ; if pres is not nil.
  (if (and $induc pres (cdr pres)) then 
      (if (setq vars (mapcan 'pre-vars (cdr pres))) 
	  then (cons (intersection (var-list term) vars) pres)
	  else
	  (setq $deep-condi 0)
	  (if (premises-are-true pres) 
	      then (setq $deep-condi old) nil
	      else (setq $deep-condi old) 'fail))))

(defun norm-rhs (rhs)
  ; normalize "rhs" as a rhs of equation.
  ; if $induc is on and the root of "rhs" is "and", then normalize
  ; the arguments of "rhs" only.
  (if (not $induc)
      then (norm-ctx rhs)
      elseif (variablep rhs)
      then (subst-var-premises rhs)
      elseif (eq (op-of rhs) 'and)
      then (simp-and-simp (mapcar 'norm-ctx (args-of rhs)))
      else (norm-ctx rhs)))

(defun each (l &optional f) 
  (loop for xa in l 
	do (terpri) (if f then (funcall f xa) else (princ xa))))
