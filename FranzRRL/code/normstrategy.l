;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

;Outermost strategy
(defun norm-outermost (term)
  ; Does left-most outermost normalization on TERM.
  (cond ((variablep term) term)
        ((loop with tmp1 = term 
	      if (setq tmp1 (rwonce-outermost term))
	      do (setq term tmp1)
	      else return term))))

(defun pure-norm-outermost (term)
  ; Does left-most outermost normalization on TERM.
  (cond ((variablep term) term)
        ((loop with tmp1 = term 
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
    ((ac-root term)
     (setq margs (mult-form (args-of term)))
     (cond 
       ((loop for mxa in margs as xa = (car mxa)
	      if (and (nonvarp xa) (setq xa (rewrite-at-root xa op-rules)))
		return (nconc (ncons (op-of term)) (ntimes (cdr mxa) xa)
			      (remove (car mxa) (args-of term) (cdr mxa)))
	      finally (return nil)))
       ((loop for mxa in margs as xa = (car mxa)
	      if (and (nonvarp xa) (setq xa (outred1 xa op-rules)))
		return (nconc (ncons (op-of term)) (ntimes (cdr mxa) xa)
			      (remove (car mxa) (args-of term) (cdr mxa)))
	      finally (return nil)))))
    ((loop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (rewrite-at-root xa op-rules)))
	     return (rplnthsubt-in-by i term xa)
	   finally (return nil)))
    ((loop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (outred1 xa op-rules)))
	     return (rplnthsubt-in-by i term xa)
	   finally (return nil)))))

(defun pure-outred1 (term)
  ; Called when term cannot be rewritten at root.  Try to rewrite
  ; the children in leftmost-outermost order.
  (cond 
    ((loop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (pure-rewrite-at-root xa)))
	     return (rplnthsubt-in-by i term xa)
	   finally (return nil)))
    ((loop for xa in (args-of term) for i from 1
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
  (if (variablep term) then term else
    (setq ans (make-term (op-of term) 
			 (mapcar 'norm-inn (args-of term))))
    (loop for rule in (rules-with-op (op-of term) $op_rules)
	  as subs = (pure-match (lhs rule) ans)
    	  if subs return (if (cycle-check ans) then
		                (if $trace-proof then (push (ruleno rule) $used-rule-nums))
				(pure-norm-with-bin (rhs rule) subs))
	  finally (return ans))))

(defun norm-inn (term &aux ans)
  ;  Does Gallier-Book modification of leftmost-innermost normalization
  ;  on TERM.  It is more efficient than NORM-INNERMOST.
  ;  First normalize children, then rewrite at root.  But remember
  ;  that bindings now are already in normal-form.
  (if (variablep term) then term else
    (setq ans (make-term (op-of term) 
			 (mapcar 'norm-inn (args-of term))))
    (loop for rule in (rules-with-op (op-of term)
				     (if (and $narrow $goal-reduce)
				        then (append $op_rules $op_goal_rules)
					else $op_rules))
	  as subs = (applies (lhs rule) ans (polish-premises (ctx rule) (lhs rule)))
    	  if subs return (if (cycle-check ans) then
		                (if $trace-proof then (push (ruleno rule) $used-rule-nums))
				(norm-with-bin (rhs rule) subs))
	  finally (return ans))))

(defun norm-with-bin (term binds &aux l1 l2)
  ;  Works for non-ac, non-commutative only now.
  ;  Used by NORM-INN.  The variables in TERM are bound.
  (if (variablep term) then (cdr (assq term binds)) else
     (setq l1 (make-term (op-of term)
			 (loop for xa in (args-of term) collect
				         (norm-with-bin xa binds))))
     (loop for rule in (rules-with-op (op-of l1)
				      (if (and $narrow $goal-reduce)
					then (append $op_rules $op_goal_rules)
					else $op_rules))
	   if (setq l2 (applies (lhs rule) l1 (polish-premises (ctx rule) (lhs rule))))
	   return (if (cycle-check l1) then
		      (if $trace-proof then (push (ruleno rule) $used-rule-nums))
		      (norm-with-bin (rhs rule) l2))
	   finally (return l1))))

(defun pure-norm-with-bin (term binds &aux l2)
  ;  Works for non-ac, non-commutative only now.
  ;  Used by NORM-INN.  The variables in TERM are bound.
  (if (variablep term)
      then (cdr (assq term binds)) 
      else
      (setq term (make-term (op-of term)
			    (loop for xa in (args-of term) 
				  collect (pure-norm-with-bin xa binds))))
      (loop for rule in (rules-with-op (op-of term) $op_rules)
	    if (setq l2 (pure-match (lhs rule) term))
	      return (if (cycle-check term) then
			 (if $trace-proof then (push (ruleno rule) $used-rule-nums))
			 (pure-norm-with-bin (rhs rule) l2))
	    finally (return term))))

;Mixed strategy
(defun pure-norm-mixed (term &aux t2)
  ;  Apply mixed-strategy normalization on TERM.
  (if (setq t2 (pure-mixed-reduce term)) then t2 else term))

(defun pure-mixed-reduce (term &aux reduced l2)
  ; Recursive function called by norm-mixed.
  ; Return nil if TERM is in normal form.
  (if (nonvarp term) then
      (loop with t2 = term 
	    if (and (nonvarp term) (setq t2 (pure-rewrite-at-root term)))
	      do (setq term t2 reduced t)
	    else return term)
      (if (nonvarp term) then
	  (setq term (make-term (op-of term)
				(loop with xb for xa in (args-of term) 
				      collect (if (setq xb (pure-mixed-reduce xa)) 
						  then (setq l2 t) xb
						  else xa))))
	
	  (if l2 then
	      (loop for rule in (rules-with-op (op-of term) $op_rules)
		    if (setq l2 (pure-match (lhs rule) term))
                return (if (cycle-check term) then
			   (if $trace-proof then (push (ruleno rule) $used-rule-nums))
			   (pure-norm-with-bin (rhs rule) l2))
		    finally (return term))
	      elseif reduced then term)
	  elseif reduced then term)))

(defun pure-rewrite-at-root (term)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (loop with subst = nil 
	with op = (op-of term)
	for rule in (get-rules-with-op op $op_rules)
	if (setq subst (pure-match (lhs rule) term))
	  return (if (cycle-check term)
		     (sublis subst (rhs rule)))
	  finally (if (and $cycle-rule (assoc op $cycle-op-rules))
		      (return (cycle-rewrite-at-root 
			       term (rules-with-op op $cycle-op-rules))))))





