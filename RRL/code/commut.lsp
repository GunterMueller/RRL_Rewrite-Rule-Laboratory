;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")



#+franz (declare (special $p-commut-rules))

(defun c-permutation (term)
  ; Return the standard form of TERM r.p.t. commutative theory.
  (cond	((variablep term) term)
	((commutativep (op-of term))
	 (make-term (op-of term) 
		    (commu-exchange (mapcar 'c-permutation (args-of term)))))
	(t (make-term (op-of term) 
		      (mapcar 'c-permutation (args-of term))))))

;;; Handle PEUSDO commutativity.

(defun is-p-commut-pair (t1 t2)
  (and (ac-root t1)
       (same-list (all-ops t1) (all-ops t2))
       (null (remove0 (cadr t1) (cddr t1)))
       (null (remove0 (cadr t2) (cddr t2)))
       (is-commut-pair (cadr t1) (cadr t2))))

(defun make-p-commut-rule (eqn &aux (lhs (lhs eqn)) (rhs (rhs eqn)))
  ; A p-commutative rule is of form
  ;       + n(x*y) == + n(y * x)
  ; where + is AC operator, n is a natural number and (x * y)'s are the only 
  ; arguments of + with n identical copies.
  (if* (total-order (first-arg lhs) (first-arg rhs)) 
      (setq lhs rhs rhs (lhs eqn)))
  (setq rhs (make-new-rule lhs rhs nil (eqn-source eqn) nil 100000))
  (push-end rhs $rule-set)
  (if* (> $trace_flag 1) then (terpri)
      (princ "Adding Hyper-commutative rule: ") (write-rule rhs))
  (push (setq rhs (list (ruleno rhs) (op-of lhs)
			 (op-of (first-arg lhs)) (length (args-of lhs))))
	$p-commut-rules)
  (p-commut-reduce-others rhs))

(defun reduce-by-p-commut (char term)
  ;; assuming (eq (cadr char) (op-of term))
  (if* (eq (cadr char) (op-of term)) then
      (sloop with succ with l1 with sort
	with n-op = (caddr char)
	with num = (cadddr char)
	with margs = (mult-form (args-of term))
	for xa in margs
	as sub = (car xa)
	if (and (>= (cdr xa) num)
		(nonvarp sub)
		(eq n-op (op-of sub))
		(not (is-sorted (args-of sub) 'total-order)))
	  do (setq margs (delete0 xa margs 1)
		   sort (sort-op-args sub)
		   l1 (quotient (cdr xa) num))
	     (setq succ (nconc succ (ntimes (setq l1 (times l1 num)) sort)
			       (ntimes (- (cdr xa) l1) sub)))
	finally (return 
		  (if* succ then
		      (query-insert (car char) $used-rule-nums)
		      (setq succ (nconc succ (demult-form margs)))
		      (if* (cdr succ) (make-term (cadr char) succ) (car succ)))))))

(defun reduce-by-p-commut2 (char coef term)
  (let ((n-op (caddr char))
	(num (cadddr char)) sort)
    (if* (and (>= coef num)
	     (nonvarp term)
	     (eq n-op (op-of term))
	     (not (is-sorted (args-of term) 'total-order))) then
	(setq sort (sort-op-args term)
	      char (times num (quotient coef num)))
	(if* (eq char coef) 
	    (ncons (cons sort char))
	    (list (cons term (- coef char)) (cons sort char))))))

(defun sort-op-args (term &aux (op (op-of term)))
  ; Sort the arguments of op in term.
  (make-term op (sort (sloop for arg in (args-of term) 
			    collect (if* (or (variablep arg) (neq op (op-of arg)))
					arg
					(sort-op-args arg)))
		      'total-order)))

(defun is-sorted (list order)
  (sloop with first = (car list)
	for second in (cdr list)
	always (prog1 (or (equal first second)
			  (funcall order first second))
		      (setq first second))))

(defun p-commut-reduce-others (rule &aux l2)
  ; Loop through the current rule set and try to do the following:
  ;   (i) Check if the left-hand-side is reducible by the new rule.
  ;	  If so, first put the rule-number of the deletable rule in the
  ;	  global-variable $DEL-RULES (helps in critical-pair computation).
  ;	  Then cleanup this rule from the organization of rules by
  ;	  outermost operator.  Then delete this rule from the rule set and
  ;	  put the new equation obtained in $EQN-SET.
  ;
  ;  (ii) If the lhs is not reducible by the new rule, try to rewrite the
  ;	  rhs of the old rule.  If possible, update the data-structures
  ;	  containing the rules.
  ;  ; keep the system reduced.
  ;
  (sloop with rnum = (car rule)
	for xa in $rule-set 
	if (and (not (eq rnum (ruleno xa)))
		(neq (car (rule-source xa)) 'def)) do
     (if* (memq rnum $del-rule-nums) 
	 then (return nil)
	 elseif (setq l2 (reduce-by-p-commut rule (lhs xa)))
	 then
	 (if* (> $trace_flag 1) then
	     (terpri) (princ "  Deleting rule:") (write-rule xa))
	 (clean-rule xa) ; removes from op_rules and if ac corr. pairs.
	 (setq l2 (make-eqn l2 (rhs xa) (ctx xa) 
			    (list 'deleted (ruleno xa) rnum)))
	 (process-del-rule l2 xa)
	 elseif (and (> $reduce-system 2)
		     (nonvarp (rhs xa))
		     (setq l2 (reduce-by-p-commut rule (rhs xa))))
	 then
	 (if* (> $trace_flag 1) then
	     (terpri) (princ "  The right hand side is reducible:") 
	     (terpri) (princ "    ") (write-rule xa))
	 (setq l2 (if* (variablep l2) then l2
		      elseif (predicatep (op-of l2))
		      then (norm-rhs l2)
		      else (norm-ctx l2)))
	 (replace xa (change-rhs xa l2)))))

;;;; Handle REAL commutativity.

(defun is-commut-pair (t1 t2)
   (and (nonvarp t1)
	(nonvarp t2)
	(null (cdddr t1))
	(null (cdddr t2))
	(same-op t1 t2) 
        (variablep (first-arg t1))
	(variablep (second-arg t1))
	(eq (first-arg t1) (second-arg t2))
	(eq (first-arg t2) (second-arg t1))))

(defun commune-terms (term)
  ;  Return the equivalent term class of TERM in the commutative theory. 
  (if* (variablep term) then (ncons term) 
      elseif (and (memq (op-of term) '(= eq)) (null (cdddr term)))
      then (sloop for xa in (if* $commutative
			       then (commune-terms2 term) 
			       else (ncons term))
		 append (list xa (list (op-of xa) 
				       (second-arg xa)
				       (first-arg xa))))
      elseif $commutative 
      then (commune-terms2 term) 
      else (ncons term)))

(defun commune-terms2 (term)
  (if* (variablep term) then (ncons term) else
     (let ((op (op-of term)) (args (args-of term)))
	(cond ((null args) (ncons term))
	      ((member op $commutative) 
               (rem-dups
		   (sloop for xa in (commune-terms2 (car args)) nconc
		       (sloop for xb in (commune-terms2 (cadr args)) nconc
			  (list (make-term op (list xa xb))
				(make-term op (list xb xa)))))))
	      (t (rem-dups (sloop for args1 in 
			     (product-lists (mapcar 'commune-terms2 args))
		           collect (make-term op args1))))))))

;;;; functions used to be in pcmisc.l

(defun commue-exchange (args)
   (if* (total-order (first args) (second args)) 
	then (reverse args)
 	else args))

(defun commu-exchange (args)
   (if* (total-order (first args) (second args))
       then args
       else (reverse args)))
