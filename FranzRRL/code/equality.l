;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

(defun reduce-eq-term (term &optional rules &aux res)
  ;; This function first tries to find a rule whose lhs is an eq
  ;; with the same number of arguments as "term".
  ;; If it can use such a rule for rewriting then it will do so.
  ;; Otherwise it looks for a rule wth eq that will rewrite some
  ;; subset of the args of "term" to false in this case it returns false.
  ;; otherwise it returns nil.  
  (setq rules (or rules 
		  (rules-with-op 'eq
				 (if (and $narrow $goal-reduce)
				     then (append $op_rules $op_goal_rules)
				     else $op_rules))))
  (if (setq res (reduce-eq-exactly term rules)) then res else
      (loop with largs = (length term)
	    with desired = nil
	    with rest-args = nil
	    for args = (args-of term)
		     then ; Deleting an arg from "args", 
		(loop for arg in args 
		      if (not (memq arg rest-args)) 
			return (remq arg args 1)
		      finally (cdr args))
	    while (and (null desired) (cdr args)) ; If more than one args left,
	    do
	(setq $false-rhs nil
	      desired
	      (loop for rule in rules
		    with sigma
		    with temp
		    if (and (< (length (lhs rule)) largs) (not (falsep (rhs rule))))
		      do
			(if (setq sigma (match-set (lhs rule) (make-term 'eq args))) 
			    ;; Structure of the value returned by match-set:
			    ;;    (rest-of-args . substitution)
			    then (setq rest-args (car sigma)
				       sigma (cdr sigma)
				       temp (norm-ctx (flat-term 
							(applysubst sigma (rhs rule)))))
			    (if (falsep temp) then
				(if $trace-proof then
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
  (loop	with largs = (length term)
	with res-subst
	for rule in rules
	as lhs = (lhs rule)
	as llhs = (length lhs)
	when (and (>= largs llhs)
		  (or (setq $false-rhs (falsep (rhs rule)))
		      (eq largs llhs))
		  (setq res-subst (eq-match lhs term))
		  (if $trace-proof then
		      (push (ruleno rule) $used-rule-nums) else t))
	return (norm-ctx (flat-term (applysubst res-subst (rhs rule))))))

(defun eq-tr (terms)
  ;  Returns term with arguments passed through the eq-find and
  ;  the transitive closure algorithms.
  (let (others eqlist trlist)
     (loop for term in terms do
            (cond ((eq (op-of term) 'eq) (push term eqlist))
                  ((member (op-of term) $translist) 
                   (setq trlist (add-associate-list
					(op-of term) (copylist term) trlist)))
                  (t (push term others))))
     (append (if eqlist (eq-find eqlist)) 
	     (if trlist (tr-find trlist)) others)))

(defun eq-find (eq-pairs)
  ; Control function for the union find algorithm.
  ; Returns terms with appropriate eq's joined.
  (loop with eqlists = nil for xa in eq-pairs 
	do (setq eqlists (eq-add (args-of xa) eqlists))
	finally (return (loop for xa in eqlists collect
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
  (loop for terms in op-trlist nconc
    (progn (setq op (pop terms) 
		 trlists nil)
	(loop for xa in terms do
	     (setq trlists (tr-add (args-of xa) trlists)))
	(loop for tlist in (tr-closure trlists) nconc
	     (tr-term op (car tlist) (cdr tlist))))))

(defun tr-add (args trlists)
  ; Adds a related pair to the strcuture for the transitive closure algorithm.
  (let ((l1 (assoc (car args) trlists)))
    (if l1 then (rplacd l1 (union (cdr l1) (cdr args))) trlists
           else (cons args trlists))))

(defun tr-closure (trlists)
  ;  Does the actual transitive closure algotrithm.
  (let (unmarked adns)
    (loop for current in trlists do
      (setq unmarked (remove current trlists) adns t)
      (loop while adns do
        (setq adns nil
              unmarked (loop for x in unmarked 
                        if (if (member (car x) (cdr current)) 
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
  (cond ((member left tlist)
         (cond ((get oper 'irreflexive) '((false)))
               ((setq tlist (delete left tlist)) 
                (loop for x in tlist collect (make-term oper (list left x))))
               (t '((true)))))
        (t (loop for x in tlist collect (make-term oper (list left x))))))

(defun idem-eq-critical (rule l1 ruleno &aux l2)
   ; Computing critical pairs with EQ predicate.
   (loop while (cdr l1) do
      (setq l2 (pop l1))
      (loop for xa in l1 do
          (add-time $unif_time (setq xa (unifier l2 xa)))
	  (if xa then
	     (setq $ncritpr (add1 $ncritpr)
  	           xa (applysubst xa `(xor (true) ,(lhs rule) ,(rhs rule))))
  	     (if (eq $trace_flag 3) then (trace-crit ruleno xa t))
	     (process-ass-simple (make-flat xa) ruleno)))))
