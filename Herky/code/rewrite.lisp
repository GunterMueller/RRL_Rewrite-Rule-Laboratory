(in-package "USER")

(defun reducible (term)
  ; Try left-most outermost reduction on TERM. Return "t" iff TERM
  ; is reducible.
  (cond ((variablep term) nil)
        ((sloop for rule in (get-rules-with-op (op-of term) nil)
	       thereis (applies (lhs rule) term)))
        (t (sloop for t1 in (args-of term) thereis (reducible t1)))))

(defun guide-reducible (guide term)
  ;  Try left-most outermost reduction on TERM. Return "t" iff TERM
  ;  is reducible.
  (cond ((variablep guide) nil)
        ((sloop for rule in (get-rules-with-op (op-of term) nil)
	       thereis (applies (lhs rule) term)) t)
        (t (sloop for t1 in (args-of term) 
	         as g1 in (args-of guide) thereis (guide-reducible g1 t1)))))

(defun rewrite-at-root (term &optional (op-rules $op-rules))
  ; returns nil if term cant be rewritten at root else rewritten term.
  ; not using polynomial rules.
  ;; (mark term "rewrite-at-root")
  (when (nonvarp term) 
    (let ((op (op-of term)) op-term unity)
      (cond 
	((memq op *true*false*) nil)
	((eq op *0*) nil)
	((and (eq op *=*) (reduce-at-eq-root term)))
	;((and (eq op *cond*) t) (princ "HANDLE COND") (terpri))
	((and (setq op-term (assoc op $divisible))
	      (third op-term)
	      (member0 (setq unity (ncons (third op-term))) (args-of term)))
	 (setq term (remove0 unity term))
	 (if* (null (args-of term)) then unity
	      elseif (null (cddr term)) then (first-arg term)
	      else term))
	((and (memq op $ac)
	      (sloop for xa in $nilpotent-rules 
		     if (eq op (caddr xa))
		     return (reduce-by-nilpotent xa term))))
	((and (memq op $ac)
	      (sloop for xa in $p-commut-rules 
		     if (eq op (cadr xa))
		     return (reduce-by-p-commut xa term))))
	((and $polynomial (or (is-rooted-+ term) (is-rooted-* term)))
	 (poly-reduce-at-root term op-rules))
	((ac-reduce-at-root term op-rules))
;	((and $condi (condi-rewrite-at-root term op-rules)))
	))))

(defun reduce-by-p-commut (char term)
  (when (equal (cadr char) (op-of term))
    ;;(write-term term) (mark "<---- input to reduce-by-p-commut")
    (sloop with succ with l1 with sort
	   with n-op = (caddr char)
	   with num = (cadddr char)
	   with margs = (mult-form (args-of term))
	   for xa in margs
	   as sub = (car xa)
	   if (and (>= (cdr xa) num)
		   (nonvarp sub)
		   (eq n-op (op-of sub)))
	   do 
	   (unless (is-sorted-under-op (op-of sub) (args-of sub))
	     (setq margs (deleten xa margs 1)
		   sort (sort-op-args sub)
		   l1 (quotient (cdr xa) num))
	     (setq succ (nconc succ (ntimes (setq l1 (times l1 num)) sort)
			       (ntimes (- (cdr xa) l1) sub))))
	   finally (return 
		     (when succ
		       (remember-used-rule-num (car char))
		       (setq succ (nconc succ (demult-form margs)))
		       (setq succ
			     (if (cdr succ) 
				 (make-term (cadr char) succ)
				 (car succ)))
		       ;;(write-term succ)
		       ;;(mark "<---- output to reduce-by-p-commut") 
		       ;(make-flat succ)
		       succ
		       )))))

(defun reduce-by-p-commut2 (char coef term)
  (let ((n-op (caddr char))
	(num (cadddr char)) sort neg)
    (if (< coef 0) (setq neg t coef (- coef)))

    (when (and (>= coef num)
	       (nonvarp term)
	       (eq n-op (op-of term))
	       (not (is-sorted-under-op (op-of term) (args-of term))))
      (setq sort (sort-op-args term)
	    char (times num (quotient coef num)))
      (setq term (if (eq char coef) 
		     (ncons (cons sort char))
		   (list (cons term (- coef char)) (cons sort char))))
      (if neg (sloop for xa in term do (setf (cdr xa) (- (cdr xa)))))
      term
      )))

(defun pure-rewrite-at-root (term &aux (op (op-of term)))
  ; returns nil if term cant be rewritten at root else rewritten term.
  (cond	((memq op *true*false*) nil)
	((and (eq op *=*) (reduce-at-eq-root term)))
	(t 
	 (sloop with subst = nil 
		for rule in (rules-with-op op $op-rules)
		if (setq subst (pure-match (lhs rule) term))
		return (if* (loop-check term) then
			    (remember-used-rule-num (ruleno rule))
			    (applysigma subst (rhs rule)))
		))))
				
(defun ac-reduce-at-root (term op-rules)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (sloop with subst = nil 
	 for rule in (rules-with-op (op-of term) op-rules)
	 if (and (null (ctx rule))
		 (setq subst (applies (lhs rule) term)))
	 return (when (loop-check term)
		      (remember-used-rule-num (ruleno rule))
		      (if $ac
			  (add-to-args rule subst)
			(c-permu (applysigma subst (rhs rule)))))
	 finally (return nil)))

(defun reduce-at-root-one-rule (term rule &aux subst)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (if (setq subst ; (if (ctx rule) (try-condi-rule rule term) )
	    (applies (lhs rule) term))
      (remember-used-rule-num (ruleno rule))
      (add-to-args rule subst)))

(defun reduce-at-eq-root (term &aux l1
				 (t1 (first-arg term))
				 (t2 (second-arg term)))
  (if* (equal t1 t2) then *trueterm*
       elseif (not (setq l1 (consistent-pair (list t1 t2) t)))
       then *falseterm*
       elseif (and (neq l1 t) (neq (car l1) *and*))
       then (make-term *=* l1)
       else
       (if* (total-term-ordering t2 t1) (psetq t1 t2 t2 t1))
       (setq l1 (list *=* t1 t2))
       (if (nequal l1 term) l1)))

(defun add-to-args (rule subst)
  (if (empty-sub subst)
      (rhs rule)
    (if (assq '$extra subst)
	(add-rest-args (flat-applysigma subst (rhs rule)) 
		       (cdr (assq '$extra subst)))
      (flat-applysigma subst (rhs rule)))))

(defun add-rest-args (arg t1)
  (if t1
      (if (or (variablep arg) (not (same-root t1 arg)))
	  (make-term (op-of t1) (insert-list arg (args-of t1) 'total-term-ordering))
	  (make-term (op-of t1) 
		     (merge-list (args-of arg) (args-of t1) 'total-term-ordering)))
      arg))

(defun rewonce-at-root (term &aux t2)
   (if* (setq t2 (rewrite-at-root term)) t2 term))

(defun loop-check (term &aux old-trace-proof)
  ; retrun t iff there is no cycle.;
  ; reset iff there is a possible cycle and $akb-flag is off.
  (decf $reduce-times)
  (if* (= $reduce-max 0)
      then t
      elseif (eq $trace-proof 'loop-check)
      then (princ "    ") (write-term term) (terpri)
           (if (= 0 $reduce-times) (throw 'loop-check t))
      elseif (= 0 $reduce-times) then
      (terpri) (princ "There is a possible loop in the rewriting system.") 
      (format t "~%One term after ~d rewrites is ~%" $reduce-max)
      (setq $reduce-times 10
	    $used-rule-nums nil
	    old-trace-proof $trace-proof
	    $trace-proof 'loop-check)
      (catch 'loop-check (norm-term term))
      (princ "    ... ...") (terpri)
      (terpri)
      (princ "Involved rules are:") (terpri)
      (dolist (xa $used-rule-nums) 
	      (write-rule (pick-out-rule xa)))
      (setq $trace-proof old-trace-proof
	    $reduce-times $reduce-max)
      (reset)
      else
      t))

(defun reduce-by-rules (term rules &aux t2)
  ; Return the reduced form of term if  rules can reduce it. Otherwise, nil.
  (sloop for rule in rules do
        (if (setq t2 (reduce-by-one-rule term rule)) (return t2))))

(defun reduce-by-one-rule (term rule)
  ; Tries to rewrite TERM at some position using RULE.
  (cond ((variablep term) nil)
;	($condi (flat-term (condi-reduce-by-one-rule term rule)))
	($fopc (flat-term (bool-reduce-by-one-rule term rule)))
	($polynomial (poly-simplify (poly-reduce-by-one-rule term rule)))
	($ac (make-flat (ac-reduce-by-one-rule term rule)))
	($commutative (make-flat (ac-reduce-by-one-rule term rule)))
	(t (pure-reduce-by-one-rule term rule))
	))

(defun ac-reduce-by-one-rule (term rule)
  ; Tries to rewrite TERM at some position using RULE.
  (or (and (same-root term (lhs rule))
	   (ac-reduce-by-one-at-root term rule))
      (sloop for xa in (args-of term) for i from 1
	     if (and (nonvarp xa) (setq xa (ac-reduce-by-one-rule xa rule)))
	     return (replace-nth-arg i term xa)
	     finally (return nil))))

(defun pure-reduce-by-one-rule (term rule)
  ; Tries to rewrite TERM at some position using RULE.
  (cond ((variablep term) nil)
        ((and (same-root term (lhs rule)) 
	      (pure-reduce-by-one-at-root term rule)))
        ((sloop for xa in (args-of term) for i from 1
		if (and (nonvarp xa) 
			(setq xa (pure-reduce-by-one-rule xa rule)))
		return (replace-nth-arg i term xa)
		finally (return nil)))))

(defun ac-reduce-by-one-at-root (term rule)
  (when (setq term (applies (lhs rule) term))
	(remember-used-rule-num (ruleno rule))
	(add-to-args rule term)))

(defun pure-reduce-by-one-at-root (term rule)
  ; Tries to rewrite TERM at some position using RULE.
  (when (and (setq term (pure-match (lhs rule) term)) 
	     (or (is-reduction rule) 
		 (satisfy-order-condition rule term)))
	(remember-used-rule-num (ruleno rule))
	(applysubst term (rhs rule))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Functions to normalize equations.
;;; Tricks for handling a special kind of equations 
;;; should go to functions for that kind of equations.
;;; Don't mess up everything when adding some new stuffs.

(defmacro check-norm-eqn (eqn)
  ; If eqn is composed of two assertions, then using the predicate equ.
  ; Check if the normal forms are the same.
  `(cond ((equal (lhs ,eqn) (rhs ,eqn)) 
	  (setq $used-rule-nums-old $used-rule-nums 
		$used-rule-nums nil))
;	 ($condi (condi-normal-eqn ,eqn))
;	 ($guha (bool-normal-eqn ,eqn))
	 ($fopc (bool-normal-eqn ,eqn))
	 ((and $polynomial *-*) (poly-normal-eqn ,eqn))
	 ($ac (ac-normal-eqn ,eqn))
	 ($commutative (ac-normal-eqn (flatten-eqn ,eqn)))
	 ((eq $kb '*distree*) (distree-normal-eqn ,eqn))
	 ($pure (pure-normal-eqn ,eqn))
	 (t (norm-normal-eqn ,eqn))
	 ))

(defmacro check-normalized-lhs-rhs ()
  `(if* (equal lhs rhs) 
	then
	(setq $used-rule-nums-old $used-rule-nums $used-rule-nums nil)
	else
	(change-lhs-rhs eqn lhs rhs)
	(if $trace-proof (update-used-rules eqn))
	eqn))

(defun norm-normal-eqn (eqn &aux lhs rhs)
  ; Checks if an equation is trivial.  Returns NIL if after
  ; normalizing both sides of EQN are equal; otherwise,
  ; returns a new equation of the normalized form of both sides.
  (setq lhs (norm-term (lhs eqn))
	rhs (norm-term (rhs eqn)))
  (check-normalized-lhs-rhs)
  )

(defun pure-normal-eqn (eqn &aux lhs rhs)
  (setq lhs (pure-norm-term (lhs eqn))
	rhs (pure-norm-term (rhs eqn)))
  (check-normalized-lhs-rhs)
  )

(defun norm-term (term)
  (cond ; ($condi (norm-ctx-term term))
	($fopc (norm-bool-term term))
	($polynomial (norm-poly-term term))
	($ac (norm-ac-term term))
	($commutative (norm-ac-term (c-permutation term)))
	((eq $kb '*distree*) (distree-norm-term term))
	(t (pure-norm-term term))))

(defun norm-bool-term (old &aux new) 
  (setq $reduce-times $reduce-max)
  (if* (variablep old) then old 
       elseif (and $fopc (predicatep (op-of old)))
       then
       (setq new (norm-bool-innermost old))
       (if* (equal new old) then old
	    elseif (equal (setq old (brt new)) new) then new
	    else (norm-bool-term old))
       elseif $polynomial
       then (norm-poly-term old)
       elseif $ac
       then (norm-ac-term old)
       else (pure-norm-term old)))

(defun pure-norm-term (term)
  ; Normalize TERM using the strategy set by the user in the flag NORM-STR.
  (setq $reduce-times $reduce-max)
  (selectq $norm-str
	   (e (pure-norm-inn term))
	   (o (pure-norm-outermost term))
	   (i (pure-norm-innermost term))
	   (m (pure-norm-mixed term))))

#|
(defun rwonce-outermost (term &optional op-rules)
  ; Rewrites TERM once at the first possible leftmost-outermost position.
  (cond ((variablep term) nil)
        ((rewrite-at-root term op-rules))
        ((outred1 term op-rules))))

;Outermost strategy
(defun norm-outermost (term)
  ; Does left-most outermost normalization on TERM.
  (cond ((variablep term) term)
        ((sloop with tmp1 = term 
	      if (setq tmp1 (rwonce-outermost term))
	      do (setq term tmp1)
	      else return term))))
|#

(defmacro rwonce-outermost (term op-rules)
  ; Rewrites TERM once at the first possible leftmost-outermost position.
  `(cond ((rewrite-at-root ,term ,op-rules))
	 ((outred1 ,term ,op-rules))))

(defun norm-outermost (term &optional (op-rules $op-rules))
  ; Does left-most outermost normalization on TERM.
  (sloop while (and (nonvarp term) 
		    (or (not $polynomial) (not (is-rooted-+ term))))
	 for term2 = (rwonce-outermost term op-rules)
	 if term2 do
	 ;(setq term (flat-term term2))
	 (setq term term2)
	 else return nil)
  term)

(defmacro pure-rwonce-outermost (term)
  ; Rewrites TERM once at the first possible leftmost-outermost position.
  `(cond ((pure-rewrite-at-root ,term))
	 ((pure-outred1 ,term))))

(defun pure-norm-outermost (term &aux term2)
  ; Does left-most outermost normalization on TERM.
  (while (and (nonvarp term)
	      (setq term2 (pure-rwonce-outermost term)))
    (setq term term2))
  term)

(defun outred1 (term op-rules &aux margs)
  ; Called when term cannot be rewritten at root.  Try to rewrite
  ; the children in leftmost-outermost order.
  ;(write-term term) (mark "!" "TERM")
  (cond 
    ((ac-root term)
     (setq margs (mult-form (args-of term)))
     (cond 
       ((sloop for mxa in margs as xa = (car mxa)
	      if (and (nonvarp xa) (setq xa (rewrite-at-root xa op-rules)))
		return (nconc (ncons (op-of term)) (ntimes (cdr mxa) xa)
			      (remove2 (car mxa) (args-of term) (cdr mxa)))
	      finally (return nil)))
       ((sloop for mxa in margs as xa = (car mxa)
	      if (and (nonvarp xa) (setq xa (outred1 xa op-rules)))
		return (nconc (ncons (op-of term)) (ntimes (cdr mxa) xa)
			      (remove2 (car mxa) (args-of term) (cdr mxa)))
	      finally (return nil)))))
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (rewrite-at-root xa op-rules)))
	     return (replace-nth-arg i term xa)
	   finally (return nil)))
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (outred1 xa op-rules)))
	     return (replace-nth-arg i term xa)
	   finally (return nil)))))

(defun pure-outred1 (term)
  ; Called when term cannot be rewritten at root.  Try to rewrite
  ; the children in leftmost-outermost order.
  (cond 
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (pure-rewrite-at-root xa)))
	     return (replace-nth-arg i term xa)
	   finally (return nil)))
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (pure-outred1 xa)))
	     return (replace-nth-arg i term xa)
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
				       (mapcar 'pure-norm-innermost
					       (args-of term))))))
      (pure-norm-innermost t1))
     (t term)))

#|
(defmacro norm-innermost (term)
  ;; rerturn a normalized, flattended term.
  `(cond ((variable ,term) term)
	 ((norm-inn ,term))
	 (t ,term)))

(defun norm-inn (term &aux ans args done)
  ;; Efficient Innermost strategy for ac-terms.
  ;; the input term is flattended and is not a variable.
  ;; return a flattened one if it's rewriten at least once.
  ;; otherwise, return nil.
  (setq args (sloop with new
		    for arg in (args-of term) 
		    collect (cond ((variablep arg) arg)
				  ((setq new (norm-inn arg))
				   (setq done t)
				   new)
				  (t arg))))
  (cond 
    ((ac-root term)
     (setq margs (mult-form (args-of term)))
     (cond 
       ((sloop for mxa in margs as xa = (car mxa)
	      if (and (nonvarp xa) (setq xa (rewrite-at-root xa op-rules)))
		return (nconc (ncons (op-of term)) (ntimes (cdr mxa) xa)
			      (remove2 (car mxa) (args-of term) (cdr mxa)))
	      finally (return nil)))
       ((sloop for mxa in margs as xa = (car mxa)
	      if (and (nonvarp xa) (setq xa (outred1 xa op-rules)))
		return (nconc (ncons (op-of term)) (ntimes (cdr mxa) xa)
			      (remove2 (car mxa) (args-of term) (cdr mxa)))
	      finally (return nil)))))
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (rewrite-at-root xa op-rules)))
	     return (replace-nth-arg i term xa)
	   finally (return nil)))
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (outred1 xa op-rules)))
	     return (replace-nth-arg i term xa)
	   finally (return nil)))))

    (sloop for rule in (rules-with-op (op-of term) $op-rules)
	  as subs = (pure-match (lhs rule) ans)
    	  if subs return
	  (if* (loop-check ans) then
	       (remember-used-rule-num (ruleno rule))
	       (pure-norm-with-bin (rhs rule) subs))
	  finally (return ans))))

(defun norm-with-bin (term binds &aux l2)
  ;  Works for non-ac, non-commutative only now.
  ;  Used by NORM-INN.  The variables in TERM are bound.
  (if* (variablep term)
      then (cdr (assq term binds)) 
      else
      (setq term (make-term (op-of term)
			    (sloop for xa in (args-of term) 
				  collect (pure-norm-with-bin xa binds))))
      (sloop for rule in (rules-with-op (op-of term) $op-rules)
	    if (setq l2 (match (lhs rule) term))
	    return (progn
		     (loop-check term) 
		     (remember-used-rule-num (ruleno rule))
		     (norm-with-bin (rhs rule) l2))
	    finally (return term))))
|#

(defun pure-norm-inn (term &aux ans)
  ; Efficient Innermost strategy
  ;  Does Gallier-Book modification of leftmost-innermost normalization
  ;  on TERM.  It is more efficient than NORM-INNERMOST.
  ;  First normalize children, then rewrite at root.  But remember
  ;  that bindings now are already in normal-form.
  (if* (variablep term) then term else
    (setq ans (make-term (op-of term) 
			 (mapcar 'pure-norm-inn (args-of term))))
    (sloop for rule in (rules-with-op (op-of term) $op-rules)
	  as subs = (pure-match (lhs rule) ans)
    	  if subs return
	  (if* (loop-check ans) then
	       (remember-used-rule-num (ruleno rule))
	       (pure-norm-with-bin (rhs rule) subs))
	  finally (return ans))))

(defun pure-norm-with-bin (term binds &aux l2)
  ;  Works for non-ac, non-commutative only now.
  ;  Used by NORM-INN.  The variables in TERM are bound.
  (if* (variablep term)
      then (cdr (assq term binds)) 
      else
      (setq term (make-term (op-of term)
			    (sloop for xa in (args-of term) 
				  collect (pure-norm-with-bin xa binds))))
      (sloop for rule in (rules-with-op (op-of term) $op-rules)
	    if (setq l2 (pure-match (lhs rule) term))
	    return (progn
		     (loop-check term) 
		     (remember-used-rule-num (ruleno rule))
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
	      (sloop for rule in (rules-with-op (op-of term) $op-rules)
		    if (setq l2 (pure-match (lhs rule) term))
                return (progn 
			 (loop-check term) 
			 (remember-used-rule-num (ruleno rule))
			 (pure-norm-with-bin (rhs rule) l2))
		finally (return term))
	      elseif reduced then term)
	  elseif reduced then term)))

(defun normalize ()
  ; Lets the user normalize a term with the current set of rules.
  ; It has its own sub-toplevel for related options.
  ; Assumes norm-cterm returns a list of conditional terms.
  (terpri)
  (princ "Please use `prove' to get a normal form of a term.") (terpri)
  (princ "    Input <TERM> == result to RRL after typing 'prove',") (terpri)
  (princ "    RRL will return the normal form of <TERM>.") (terpri)
  (princ "Sorry for inconvenience.") (terpri) (terpri))

(defmacro is-normal (term) `(not (reducible ,term)))


