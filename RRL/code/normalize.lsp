;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

(in-package "USER")

;-- file containing normalization procedures for non-ac, ac and conditional.
;-- Ac has no separate functions. innermost and outermost are same.
;-- Have removed use of global variables like mbinds for some
;-- procedures. Same needs to be done for conditional etc.

(defun is-normal (term) (not (reducible term)))

(defun normalize (eqn &aux eqn2)
  ; If eqn is composed of two assertions, then using the predicate equ.
  ; Check if the normal forms are the same.
  (cond ((equal-term (lhs eqn) (rhs eqn)) nil)
	($induc
	 (if (and (setq eqn2 (cover-normalize eqn)) (car eqn2)) eqn2))
	((setq eqn2 (assertion2equation eqn))
	 (checkeq-normal eqn2))
	((is-assertion eqn) eqn)
	((and (not $induc)
	      (is-prop-eqn eqn) 
	      (or (eq (op-of (lhs eqn)) 'xor)
		  (eq (op-of (rhs eqn)) 'xor)))
	 (setq eqn2 (ass2eqn (eqn2assertion eqn) (eqn-source eqn)))
	 (if* (eq $trace_flag 3) then
	     (terpri) (princ "Transform equation ") (write-eqn eqn)
	     (princ "  to assertion ") (write-eqn eqn2))
	 eqn2)
	(t (checkeq-normal eqn))))

(defun assertion2equation (eqn &aux eqn2)
  ;; return the reformulated equation if possible.
  ;; return nil if no reformulation is done.
  (when (and (is-assertion eqn)
	     (or (eq (op-of (lhs eqn)) 'eq) 
		 (eq (op-of (lhs eqn)) '=) )
	     (null (cdddr (lhs eqn))))
	(setq eqn2 (make-eqn (first-arg (lhs eqn)) 
			     (second-arg (lhs eqn)) nil (eqn-source eqn)))
	(if* (eq $trace_flag 3) then
	  (terpri) (princ "Transform assertion ") (write-eqn eqn)
	  (princ "  to equation ") (write-eqn eqn2))
	eqn2))

(defun checkeq-normal (eqn &optional consistent &aux lhs rhs)
  ; Checks if a critical pair is trivial.  Returns NIL if after
  ; normalizing both sides of EQN they are equal; otherwise,
  ; returns a new equation of the normalized form of both sides.
  ; Normalize both sides of EQN using the strategy set by the user in the
  ; flag NORM_STR, then see if they are equal.

  ; avoiding rules bite one's own tails.
  (setq $avoid-rules nil)

  (if* (not (equal (lhs eqn) (rhs eqn))) then
      (setq $used-rule-nums nil
	    lhs (norm-ctx (lhs eqn))
	    rhs (norm-rhs (rhs eqn)))
      (if* (and $induc (nonvarp rhs) (nonvarp lhs)) then
	  (if* (and (truep rhs) (eq (op-of lhs) '=)
		   (is-subset (all-vars (second-arg lhs)) (all-vars (first-arg lhs))))
	      then (setq rhs (second-arg lhs)
			 lhs (first-arg lhs))
	      elseif (and (eq (op-of lhs) 'xor) (member0 $true-term lhs))
	      then (setq lhs (negate-predicate lhs)
			 rhs (negate-predicate rhs))))
		     
      (if* (equal-term lhs rhs) then nil else
	  (setq eqn (make-eqn lhs rhs nil 
			      (append (eqn-source eqn)
				      (if* $trace-proof (rem-dups $used-rule-nums))))
		$used-rule-nums nil)
	  (if* (not consistent) then (last-consistency-check eqn) else eqn))))

(defun pure-checkeq-normal (eqn &optional consistent &aux lhs rhs)
  ; Checks if a critical pair is trivial.  Returns NIL if after
  ; normalizing both sides of EQN they are equal; otherwise,
  ; returns a new equation of the normalized form of both sides.
  ; Normalize both sides of EQN using the strategy set by the user in the
  ; flag NORM_STR, then see if they are equal.
  (setq $used-rule-nums nil
	lhs (pure-norm (lhs eqn))
	rhs (pure-norm (rhs eqn)))
  (if* (equal lhs rhs) then nil else
      (setq eqn (make-eqn lhs rhs nil 
			  (append (eqn-source eqn)
				  (if* $trace-proof (rem-dups $used-rule-nums))))
	    $used-rule-nums nil)
      (if* (not consistent) then (last-consistency-check eqn) else eqn)))

(defun last-consistency-check (eqn)
  (if* (and (not (is-oneway eqn)) (lrpo (rhs eqn) (lhs eqn)))
      then (setq eqn (exchange-lr eqn)))
  (if* (and (nonvarp (lhs eqn))
	   (eq (op-of (lhs eqn))'=)
	   (null (all-vars (rhs eqn)))
	   (not (consistent-pair (first-arg (lhs eqn)) (second-arg (lhs eqn))
				 (var-consistency (lhs eqn)))))
      then (if* (falsep (rhs eqn)) then (setq eqn nil)
	       else (setq eqn (change-lhs eqn $false-term)))
      else eqn))

(defun norm-term (term)
  ; Normalize TERM using the strategy set by the user in the flag NORM_STR.
  (setq $reduce-times $reduce-bound)
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
        ((sloop for rule in (get-rules-with-op (op-of term) nil)
	       thereis (applies (lhs rule) term 
				(polish-premises (ctx rule) rule))) t)
        (t (sloop for t1 in (args-of term) thereis (reducible t1)))))

(defun guide-reducible (guide term)
  ;  Try left-most outermost reduction on TERM. Return "t" iff TERM
  ;  is reducible.
  (cond ((variablep guide) nil)
        ((sloop for rule in (get-rules-with-op (op-of term) nil)
	       thereis (applies (lhs rule) term)) t)
        (t (sloop for t1 in (args-of term) 
	         as g1 in (args-of guide) thereis (guide-reducible g1 t1)))))

(defun rewrite-at-root (term &optional op-rules)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (if* (nonvarp term) 
      (let ((op (op-of term)))
	(cond 
	  ((memq op '(false true 0)) nil)
	  ((eq op '=) (simplify-my-eq-term term))
	  ((eq op 'cond) (simplify-cond-term term))
	  ((and (memq op $ac)
		(sloop for xa in $character-rules 
		      if (eq op (caddr xa))
			return (reduce-by-character xa term))))
	  ((and (memq op $ac)
		(sloop for xa in $p-commut-rules 
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
  (or (and (cdr $premises-set) 
	   (reduce-by-premises-at-root term (cdr $premises-set)))
      (sloop with subst = nil 
	    for rule in (get-rules-with-op (op-of term) op-rules)
	    if (and (not (member rule $avoid-rules))
		    (setq subst (try-one-rule rule term)))
	    return (when (cycle-check term)
;			 (mark term (ruleno rule))
		       (if $ac
			   (add-to-args rule subst)
			 (c-permu (applysubst subst (rhs rule)))))
	    )))

(defun reduce-at-root-by-extra-prevars-rules (term)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (sloop with sigma = nil 
	for rule in $condi-dominate-rules
	if (setq sigma (try-one-condi-rule rule term))
	return (if* (cycle-check term)
		   (if* $ac
		       (add-to-args rule sigma)
		     (c-permu (applysubst sigma (rhs rule)))))))

(defun try-one-rule (rule term &aux subst used-rules)
  (if* (ctx rule) then 
      (if* (eq $deep-condi 0)
	  then nil
	  else
	  (decf $deep-condi)
	  (setq used-rules $used-rule-nums 
		$used-rule-nums nil
		subst (applies (lhs rule) term
			       (polish-premises (ctx rule) rule)))
	  (incf $deep-condi)
	  (setq $used-rule-nums 
		(if* subst
		    then (append $used-rule-nums 
				 (cons (ruleno rule) used-rules))
		    else used-rules))
	  subst)
      elseif (setq subst (applies (lhs rule) term))
      then (if* $trace-proof (push (ruleno rule) $used-rule-nums))
      subst))

(defun try-one-condi-rule (rule term &aux sigma used-rules)
  (when (> $deep-condi 0)
	(decf $deep-condi)
	(setq used-rules $used-rule-nums 
	      $used-rule-nums nil
	      sigma (applies (lhs rule) term))

	(when sigma (setq sigma (try-one-extra-var-rule rule sigma)))
	(incf $deep-condi)
	(setq $used-rule-nums 
	      (if* sigma
		  (append $used-rule-nums (cons (ruleno rule) used-rules))
		used-rules))
	sigma
	))

(defun try-one-extra-var-rule (rule sigma)
  (let ((pres (cdr (ctx rule))) 
	(avoids (sloop for xa in sigma collect (cdr xa)))
	newsigma flag)
    ;; try to match pres in (ctx rule) against that in $premises-set.
    (sloop for pre1 in pres do
	   (sloop for pre2 in (cdr $premises-set) do
		  (when (and (equal (cadr pre1) (cadr pre2))
			     (setq newsigma 
				   (match (car pre1) (car pre2) sigma))
			     (sloop for xa in (ref-extra-pre-variables rule)
				    always (not (member0 (cdr (assoc xa sigma))
							 avoids)))
			     )
		    (setq flag t
			  pres (remove0 pre1 pres)
			  sigma newsigma)
		    )))

  (if (and flag
	   (sloop for xa in (ref-extra-pre-variables rule)
		  always (assoc xa sigma))
	   (premises-are-true (applysubst sigma (cons '*&* pres))))
      sigma)))

(defun reduce-at-root-one-rule (term rule &aux subst)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (when (setq subst (try-one-rule rule term)) 
	(if $trace-proof (push (ruleno rule) $used-rule-nums))
	(flat-term (add-to-args rule subst))))

(defun simplify-my-eq-term (term &aux l1 t1 t2)
  (setq t1 (first-arg term)
	t2 (second-arg term))

  (if* (equal t1 t2) then $true-term
      elseif (truep t1) then t2
      elseif (truep t2) then t1
      elseif (falsep t1) then (ba-simp-not t2)
      elseif (falsep t2) then (ba-simp-not t1)
      elseif (setq l1 (reduce-at-root term $op_rules)) then l1
      else
      (setq t1 (norm-ctx t1)
	    t2 (norm-ctx t2))
      (if* (equal t1 t2) then $true-term
	  elseif (not (setq l1 (consistent-pair t1 t2 t)))
	  then $false-term
	  elseif (and (neq l1 t) (eq (car l1) 'and))
	  then (make-term 'and (sloop for xa in (args-of l1) 
				     collect (make-term '= xa)))
	  elseif (neq l1 t) 
	  then (make-term '= l1)
	  else
	  (arrange-eq-args t1 t2)
	  (setq l1 (list '= t1 t2))
	  (if* (nequal l1 term) then l1 
	      elseif (cdr $premises-set)
	      then (reduce-by-premises-at-root term (cdr $premises-set))))))

(defun var-consistency (term)
  ; Return t iff the pair like x = f(y) or x = 0 is a consistent relation.
  (and $premises-set
       (related-vars 
	 (mapcar 'pre-vars (cdr $premises-set)) (all-vars term))))

(defun add-to-args (rule subst)
  (if* (eq subst *empty-sub*)
      then (rhs rule)
      elseif (assq '$extra subst)
      then (add-rest-args (applysubst subst (rhs rule)) 
			  (cdr (assq '$extra subst)))
      else (apply-to (rhs rule) subst)))

(defun add-rest-args (arg t1)
  (if t1 
      (if (or (variablep arg) (not (same-op t1 arg)))
	 (make-term (op-of t1) (cons arg (args-of t1)))
	(make-term (op-of t1) (append (args-of t1) (args-of arg))))
    arg))

(defun rewonce-at-root (term) (or (rewrite-at-root term) term))

(defun normalize-one-eqn ()
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
  (if* (eq 0 (setq $reduce-times (sub1 $reduce-times))) then
    (terpri) (princ "There is a possible loop in the rewriting system.") 
    (terpri) (princ (uconcat "One term after " $reduce-bound " rewrites is "))
    (setq $reduce-times $reduce-bound)
    (sloop for i from 1 to 10 do
      (terpri) (princ "         ") (write-term term)
      (setq term (reduce-by-rules term $rule-set))
      (if* (null term) (return)))
    (terpri)
    (if* term 
	(princ "         ... ...") 
      (princ
       "The system is terminating; please set a bigger normalization bound."))
    (terpri)
    (if* $akb_flag nil (reset))
    else
    t))

(defun ac-compress (op args)
  (cond
     ($ac (compress-flat op args))
     ((commutativep op)	(make-term op (commu-exchange args)))
     ((member op '(or xor and)) 
      (if $induc
	  (ba-simplify (make-term op args))
	(brt (make-term op args))))
     (t (make-term op args))))

(defun reduce-by-rules (term rules &aux t2)
  ; Return the reduced form of term if  rules can reduce it. Otherwise, nil.
  (sloop for rule in rules 
	 if (setq t2 (reduce-by-one-rule term rule)) 
	 return t2))

(defun reduce-by-one-rule (term rule)
  ; Tries to rewrite TERM at some position using RULE.
  (cond ((variablep term) nil)
        ((and (same-root term (lhs rule)) (reduce-by-one-at-root term rule)))
        ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (reduce-by-one-rule xa rule)))
	     return (flat-term (rplnthsubt-in-by i term xa))
	   finally (return nil)))))

(defun reduce-by-one-at-root (term rule &optional pres &aux l1)
  ; Tries to rewrite TERM at some position using RULE.
  (if pres (setq $premises-set pres))
  (cond ((variablep term) nil)
        ((setq l1 (if* $polynomial
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
        ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (pure-reduce-by-one-rule xa rule)))
	     return (rplnthsubt-in-by i term xa)
	   finally (return nil)))))

(defun pure-reduce-by-one-at-root (term rule &aux subst)
  ; Tries to rewrite TERM at some position using RULE.
  (cond ((variablep term) nil)
	((if* (setq subst (pure-match (lhs rule) term)) then
	     (if* $trace-proof then (push (ruleno rule) $used-rule-nums))
	     (applysubst subst (rhs rule))))
	(t nil)))

(defun polish-premises (pres rule &aux vars) ; ((old $deep-condi))
  ; Return (intersection of vars in pres and that of term . pres)
  ; if pres is not nil.
  (if (and $induc pres (cdr pres))
      (if (and (setq vars (if (nthcdr 5 rule) (ref-pres-vars rule) (all-pre-vars (cdr pres))))
	       (not (eq vars t)))
	  (cons vars pres)
	(cons nil pres))))

;; delete the following: 5/25/92.
;	  (setq $deep-condi 0)
;	  (if* (premises-are-true pres) 
;	      then (setq $deep-condi old) nil
;	      else (setq $deep-condi old) 'fail)

(defun norm-rhs (rhs)
  ; normalize "rhs" as a rhs of equation.
  ; if $induc is on and the root of "rhs" is "and", then normalize
  ; the arguments of "rhs" only.
  (if* (not $induc)
      then (norm-ctx rhs)
      elseif (variablep rhs)
      then (subst-var-premises rhs)
      elseif (eq (op-of rhs) 'and)
      then (simp-and-simp (mapcar 'norm-ctx (args-of rhs)))
      else (norm-ctx rhs)))

(defun each (l &optional f) 
  (sloop for xa in l 
	do (terpri) (if* f then (funcall f xa) else (princ xa))))

(defun reduce-cond-term (term)
  (let ((condi (first-arg term))) 
    (cond
     ((truep condi) (second-arg term))
     ((falsep condi) (cadddr term))
     ((equal (caddr term) (cadddr term)) (caddr term))
     ((and (truep (caddr term)) (falsep (cadddr term))) condi)
     ((and (truep (cadddr term)) (falsep (caddr term))) 
      (ba-simp-not condi))
     ((and (nonvarp condi) (eq (op-of condi) 'not))
      (list 'cond (first-arg condi) (cadddr term) (caddr term)))
     ((equal condi (first-arg term)) ;; condi is unchanged.
      (reduce-at-root term $op_rules))
     (t (list 'cond condi (caddr term) (cadddr term)))
     )))

(defun simplify-cond-term (term)
  (let ((condi (cover-norm-term (first-arg term))) 
	(first (second-arg term))
	(second (cadddr term)))
    (cond
     ((truep condi) (cover-norm-term first))
     ((falsep condi) (cover-norm-term second))
     (t (setq first (cover-norm-term first))
	(setq second (cover-norm-term second))
	(cond ((and (truep first) (falsep second)) condi)
	      ((and (truep second) (falsep first))
	       (ba-simp-not condi))
	      ((equal first second) first)
	      (t 
	       (if (and (nonvarp condi) (eq (op-of condi) 'not))
		   (psetq condi (ba-simp-not condi)
			  first second
			  second first))

	       (cond ((equal condi first) (setq first $true-term))
		     ((equal condi second) (setq second $false-term)))

	       (setq condi (list 'cond condi first second))

	       (if (not (equal condi term))
		   condi ;; term has been changed.
		 (reduce-at-root term $op_rules)) ;; reduce term by user's rules.
	       ))))))

;Outermost strategy
(defun norm-outermost (term)
  ; Does left-most outermost normalization on TERM.
  (cond ((variablep term) term)
        ((sloop with tmp1 = term 
	      if (setq tmp1 (rwonce-outermost term))
	      do (setq term tmp1)
	      else return term))))

(defun pure-norm-outermost (term)
  ; Does left-most outermost normalization on TERM.
  (cond ((variablep term) term)
        ((sloop with tmp1 = term 
	      if (setq tmp1 (pure-rwonce-outermost term))
		do (setq term tmp1)
	       else return term))))

(defun rwonce-outermost (term &optional op-rules)
  ; Rewrites TERM once at the first possible leftmost-outermost position.
  (cond ((variablep term) nil)
        ((rewrite-at-root term op-rules))
        ((outred1 term op-rules))))

(defun pure-rwonce-outermost (term)
  ; Rewrites TERM once at the first possible leftmost-outermost position.
  (cond ((variablep term) nil)
        ((pure-rewrite-at-root term))
        ((pure-outred1 term))))

(defun outred1 (term op-rules &aux margs)
  ; Called when term cannot be rewritten at root.  Try to rewrite
  ; the children in leftmost-outermost order.
  (cond 
   ((member (op-of term) '(= cond)) nil)
   ((ac-root term)
     (setq margs (mult-form (args-of term)))
     (cond 
       ((sloop for mxa in margs as xa = (car mxa)
	      if (and (nonvarp xa) (setq xa (rewrite-at-root xa op-rules)))
		return (nconc (ncons (op-of term)) (ntimes (cdr mxa) xa)
			      (remove0 (car mxa) (args-of term) (cdr mxa)))
	      finally (return nil)))
       ((sloop for mxa in margs as xa = (car mxa)
	      if (and (nonvarp xa) (setq xa (outred1 xa op-rules)))
		return (nconc (ncons (op-of term)) (ntimes (cdr mxa) xa)
			      (remove0 (car mxa) (args-of term) (cdr mxa)))
	      finally (return nil)))))
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (rewrite-at-root xa op-rules)))
	   return (rplnthsubt-in-by i term xa)
	   finally (return nil)))
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (outred1 xa op-rules)))
	   return (rplnthsubt-in-by i term xa)
	   finally (return nil)))))

(defun pure-outred1 (term)
  ; Called when term cannot be rewritten at root.  Try to rewrite
  ; the children in leftmost-outermost order.
  (cond 
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (pure-rewrite-at-root xa)))
	     return (rplnthsubt-in-by i term xa)
	   finally (return nil)))
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (pure-outred1 xa)))
	     return (rplnthsubt-in-by i term xa)
	   finally (return nil)))))

;Innermost strategy
(defun pure-norm-innermost (term &aux t1)
  ; Does leftmost-innermost normalization on TERM.
  ; First normalizes children of TERM, then try to rewrite at root.
  ; (This is a single recursive procedure.)
  (cond
     ((variablep term) term)
     ((setq t1 (pure-rewrite-at-root
		 (setq term (make-term (op-of term)
				       (mapcar 'pure-norm-innermost (args-of term))))))
      (pure-norm-innermost t1))
     (t term)))

;Efficient Innermost strategy
(defun pure-norm-inn (term &aux ans)
  ;  Does Gallier-Book modification of leftmost-innermost normalization
  ;  on TERM.  It is more efficient than NORM-INNERMOST.
  ;  First normalize children, then rewrite at root.  But remember
  ;  that bindings now are already in normal-form.
  (if* (variablep term) then term else
    (setq ans (make-term (op-of term) 
			 (mapcar 'norm-inn (args-of term))))
    (sloop for rule in (rules-with-op (op-of term) $op_rules)
	  as subs = (pure-match (lhs rule) ans)
    	  if subs return (if* (cycle-check ans) then
		                (if* $trace-proof then (push (ruleno rule) $used-rule-nums))
				(pure-norm-with-bin (rhs rule) subs))
	  finally (return ans))))

(defun norm-inn (term &aux ans)
  ;  Does Gallier-Book modification of leftmost-innermost normalization
  ;  on TERM.  It is more efficient than NORM-INNERMOST.
  ;  First normalize children, then rewrite at root.  But remember
  ;  that bindings now are already in normal-form.
  (if* (variablep term) then term else
    (setq ans (make-term (op-of term) 
			 (mapcar 'norm-inn (args-of term))))
    (sloop for rule in (rules-with-op (op-of term)
				     (if* (and $narrow $goal-reduce)
				        then (append $op_rules $op_goal_rules)
					else $op_rules))
	  as subs = (applies (lhs rule) ans (polish-premises (ctx rule) rule))
    	  if subs return (if* (cycle-check ans) then
		                (if* $trace-proof then (push (ruleno rule) $used-rule-nums))
				(norm-with-bin (rhs rule) subs))
	  finally (return ans))))

(defun norm-with-bin (term binds &aux l1 l2)
  ;  Works for non-ac, non-commutative only now.
  ;  Used by NORM-INN.  The variables in TERM are bound.
  (if* (variablep term) then (cdr (assq term binds)) else
     (setq l1 (make-term (op-of term)
			 (sloop for xa in (args-of term) collect
				         (norm-with-bin xa binds))))
     (sloop for rule in (rules-with-op (op-of l1)
				      (if* (and $narrow $goal-reduce)
					then (append $op_rules $op_goal_rules)
					else $op_rules))
	   if (setq l2 (applies (lhs rule) l1 (polish-premises (ctx rule) rule)))
	   return (if* (cycle-check l1) then
		      (if* $trace-proof then (push (ruleno rule) $used-rule-nums))
		      (norm-with-bin (rhs rule) l2))
	   finally (return l1))))

(defun pure-norm-with-bin (term binds &aux l2)
  ;  Works for non-ac, non-commutative only now.
  ;  Used by NORM-INN.  The variables in TERM are bound.
  (if* (variablep term)
      then (cdr (assq term binds)) 
      else
      (setq term (make-term (op-of term)
			    (sloop for xa in (args-of term) 
				  collect (pure-norm-with-bin xa binds))))
      (sloop for rule in (rules-with-op (op-of term) $op_rules)
	    if (setq l2 (pure-match (lhs rule) term))
	      return (if* (cycle-check term) then
			 (if* $trace-proof then (push (ruleno rule) $used-rule-nums))
			 (pure-norm-with-bin (rhs rule) l2))
	    finally (return term))))

;Mixed strategy
(defun pure-norm-mixed (term &aux t2)
  ;  Apply mixed-strategy normalization on TERM.
  (if* (setq t2 (pure-mixed-reduce term)) then t2 else term))

(defun pure-mixed-reduce (term &aux reduced l2)
  ; Recursive function called by norm-mixed.
  ; Return nil if TERM is in normal form.
  (if* (nonvarp term) then
      (sloop with t2 = term 
	    if (and (nonvarp term) (setq t2 (pure-rewrite-at-root term)))
	      do (setq term t2 reduced t)
	    else return term)
      (if* (nonvarp term) then
	  (setq term (make-term (op-of term)
				(sloop with xb for xa in (args-of term) 
				      collect (if* (setq xb (pure-mixed-reduce xa)) 
						  then (setq l2 t) xb
						  else xa))))
	
	  (if* l2 then
	      (sloop for rule in (rules-with-op (op-of term) $op_rules)
		    if (setq l2 (pure-match (lhs rule) term))
                return (if* (cycle-check term) then
			   (if* $trace-proof then (push (ruleno rule) $used-rule-nums))
			   (pure-norm-with-bin (rhs rule) l2))
		    finally (return term))
	      elseif reduced then term)
	  elseif reduced then term)))

(defun pure-rewrite-at-root (term)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (sloop with subst = nil 
	with op = (op-of term)
	for rule in (get-rules-with-op op $op_rules)
	if (setq subst (pure-match (lhs rule) term))
	  return (if* (cycle-check term)
		     (applysubst subst (rhs rule)))
	  finally (if* (and $cycle-rule (assoc op $cycle-op-rules))
		      (return (cycle-rewrite-at-root 
			       term (rules-with-op op $cycle-op-rules))))))





