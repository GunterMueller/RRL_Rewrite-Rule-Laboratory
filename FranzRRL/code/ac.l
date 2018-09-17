;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

(defun flatten-rule (rule)
 (change-lhs-rhs rule (flat-term (lhs rule)) (flat-term (rhs rule))))

(defun flatten-eqn (eqn)
  (setq eqn (change-lhs-rhs eqn (flat-term (lhs eqn)) (flat-term (rhs eqn))))
  (if (ctx eqn) (change-ctx eqn (flatten-premises (ctx eqn))) eqn))

(defun flatten-premises (ctx)
  (if (eq (car ctx) '&&) then
      (cons '&& 
	    (loop for pre in (cdr ctx) 
		  collect (make-pre (flat-term (first pre)) 
				    (flat-term (second pre))
				    (cddr pre))))
      else
      (flat-term ctx)))

(defun flat-term-func (term) 
  ; Make sure every term in the system is flattend and brted.
  (if (variablep term) then term else
      (setq term (if $ac then (make-flat term)
		     elseif $commutative then (c-permutation term)
		     else term))
      (if $in-fopc then (brt term) else term)))

(defun make-flat (term)
  (cond
    ((variablep term) term)
    ((null (args-of term)) term)
    (t (compress-flat (op-of term) (mapcar 'make-flat (args-of term))))))

(defun compress-flat (op args)
  (make-term op 
	(if (ac-op-p op) 
	     then (flat-sort-args op args)
	     elseif (commutativep op)
	     then (commu-exchange args)
	     else args)))

(defun flat-sort-args (op args)
    (loop with ans for arg in args do
        (setq ans (if (and (nonvarp arg) (eq op (op-of arg))) 
			then (merge-list (args-of arg) ans 'total-order)
			else (insert-list arg ans 'total-order)))
	finally (return ans)))

(defun is-assoc-under-c (t1 t2)
   ; Return T iff T1 is of form "f(f(x, y), z)" and T2 of form
   ; "f(x, f(y, z))" or vice versa, where "f" is commutative.
   (and	(is-assoc-pair t1 t2)
	(memq (op-of t1) $commutative)))

(defun is-assoc-pair (t1 t2 &aux ops vars)
  (and (nonvarp t1) 
       (eq (get-arity (op-of t1)) 2)
       (eq (length (setq ops (all-ops t1))) 2)
       (eq (car ops) (cadr ops))
       (eq (length (setq vars (var-list t1))) 3)
       (equal ops (all-ops t2))
       (is-subset vars (setq ops (var-list t2)))
       (is-subset ops vars)
       (nequal (first-arg t1) (first-arg t2))
       (nequal (second-arg t1) (second-arg t2))))

(defun make-ass-com-op (op eqn ac-flag &aux ops)
  (start-push-history eqn)
  (terpri)
  (princ (uconcat "'" op "' has the "
		  (if ac-flag then "associative and " else "")
		 "commutative property now: ")) (terpri) 
  (princ "    ") (write-eqn eqn)

  (if (get op 'status) then
     (princ (uconcat "'" op "' has been given the status " 
		(get op 'status) "."))
     (princ " Now, the status is cancelled.") (terpri)
     (remprop op 'status)
     (delete op (ops-equiv-to op)))

  (if ac-flag then (push op $ac) 
		   (setq $commutative (delq op $commutative 1))
	      else (push op $commutative))

  (setq ac-flag (if ac-flag then 'make-flat else 'c-permutation))

  ; >>>>> 1/29/89
  (if $witness-eqn (flatten-witness (eqn-source eqn)))

  ; >>>>> 4/29/89
  (setq $p-commut-rules (loop for rule in $p-commut-rules 
			      if (not (member op rule)) collect rule))

  (if $testset (flatten-testset ac-flag eqn))
      
  (setq ops (flatten-rules op ac-flag (eqn-source eqn)))
  (if (and ops (neq 'make-flat ac-flag)) (wash-def-rules ops)))

(defun flatten-rules (op flatten &optional source &aux def-rule-ops)
  ; Flatten the equations and rules in the current system.
  ; Delete the rules which have "op".
  ; If the ac is the first time introduced, then changeing the
  ; critical pair computing strategies.
  (setq $free-constructors (delq op $free-constructors))
  (if $post-ass-set then (flatten-post-ass flatten))
  (setq def-rule-ops (flatten-rules2 op flatten source))
  (setq $eqn-set (mapcar 'flatten-eqn $eqn-set)
	$post-set (mapcar 'flatten-eqn $post-set))
  ; If this is the first AC operator, then change the strategy of
  ; computing critical pairs.
  (if (and (eq flatten 'make-flat) (null (cdr $ac))) then
      (setq $blocking-on 'y $norm_str 'o)
      (loop for xa in $rule-set do
        (if (not (crit-marked xa))
	    then (loop for xb in $rule-set do (add-pairs xa xb)))))
  def-rule-ops)

(defun flatten-rules2 (op flatten source &aux l2 neweq def-rule-ops)
  ; Auxillary function of "faltten-rules".
  (loop for xa in $rule-set 
	if (memq op (all-ops (lhs xa))) do
	(if (> $trace_flag 1) then (terpri) 
	    (princ (uconcat "  The LHS of Rule contains '" op "', which is "
			    (if (eq flatten 'c-permutation) 
				"commutative now."
			        "AC now."))) 
	    (terpri)
	    (write-rule xa))
	(if (and $induc (eq (car (rule-source xa)) 'def)) 
	    then
	  (if (eq flatten 'c-permutation)
	      (insert1 (op-of (lhs xa)) def-rule-ops))
	  else
	  (clean-rule xa) ; removes from op_list and if ac corr. pairs.
	  (setq l2 (make-eqn (lhs xa) (rhs xa) (ctx xa) 
			     (nconc (list 'deleted (ruleno xa) 'ac-op)
				    (if source
					(if (eq (car source) 'deleted)
					    (list (car source) (cadr source) 
						  (caddr source))
					    (list (car source) 
						  (cadr source)))))))
	  (push l2 neweq)))

  (loop for xa in $rule-set do
	(if (memq op (all-ops (rhs xa))) then
	  (if (> $trace_flag 1) then (terpri) 
	      (princ (uconcat "  The RHS of Rule contains '" op "', which is "
			      (if (eq flatten 'c-permutation)
				  "commutative now."
				"AC now."))) 
	      (terpri)
	      (write-rule xa))
	  (setq l2 (if (predicatep (op-of (rhs xa)))
		       (norm-rhs (funcall flatten (rhs xa)))
		     (norm-ctx (funcall flatten (rhs xa)))))
	  (replace xa (change-rhs xa l2)))
	(if (ctx xa) (replace xa (change-ctx xa (flatten-premises (ctx xa))))))

  (setq $eqn-set (nreconc neweq $eqn-set))
  def-rule-ops)

(defun flatten-post-ass (flatten &aux l2)
   (setq l2 $post-ass-set
	 $post-ass-set nil)
   (loop with xb for xa in l2 do
     (if (not (eq (cddr xa) (setq xb (funcall flatten (cddr xa))))) 
	then (if (eq $trace_flag 3) then
		(princ "Process proposition: ") (write-assertion (cdr xa)))
	     (process-ass-simple xb (cadr xa))
        else (setq $post-ass-set (nconc $post-ass-set (ncons xa))))))

(defun has-acop (t1) (loop for op in (all-ops t1) thereis (ac-op-p op)))

(defun flatten (op args)
  ;  Simplifies ARGS for associativity and commutativity of the operator OP.
  (loop for term in args append
     (cond ((null term) term)
           ((variablep term) (ncons term))
           ((equal op (op-of term)) (flatten op (args-of term)))
           (t (ncons term)))))

(defun elimcom (argsx argsy)
  (loop
    for x in argsx
	if
	(loop
	  for terms on argsy
	  as y = (car terms)
	  if (ac-equal y x)
	  return (prog1 nil (setq argsy (nconc new-argsy (cdr terms))))
	  else collect y into new-argsy
	  finally (return t))
	collect x into new-argsx
	finally(return (list new-argsx argsy))))

(defun multi-com (args)
  (loop for term in args
	if (and (variablep term)
		(loop for l in vars-argsx
		      if (equal (car l) term)
			return (rplacd l (add1 (cdr l)))
		      finally (return nil)))
	  do nil
	else if (and (nonvarp term)
		     (loop for l in non-vars-argsx
			   if (equal (car l) term)
			     return (rplacd l (add1 (cdr l)))
			   finally (return nil)))
	       do nil
	else
	  if (variablep term) collect (cons term 1) into vars-argsx
	else collect (cons term 1) into non-vars-argsx 
	finally (return (cons vars-argsx non-vars-argsx))))

;      (return (let ((l1 (split-alist vars-argsx))
;		    (l2 (split-alist non-vars-argsx)))
;		(list (car l1) (car l2) (nconc (cadr l1) (cadr l2)))))))

(defun ac-member (t1 list)
  (loop for y on list if (ac-equal(car y) t1) return y finally (return nil)))

(defun wash-def-rules (ops)
  ; "ops" are operators of which the definition rules
  ; containing a newly commutative operators. 
  ; If their definition can be simplified, then save their old
  ; definition structure (or cover-set) in $non-comm-cover-sets
  ; and delete them from $cover-sets.
  (loop with del for op in ops do
    (setq del nil)
    (loop with result with rul3
	  for rul1 in (cdr (assoc op $op_rules)) 
	  if (eq (car (rule-source rul1)) 'def) do
      (setq rul3 (flatten-eqn rul1))
      (if (loop for rul2 in result thereis (similar-eqn rul3 rul2))
	  then (clean-rule rul1) (setq del t)
	  else (replace rul1 rul3) (push rul3 result)))
    (if del then
	(setq del (assoc op $cover-sets))
	(push del $non-comm-cover-sets ))))
