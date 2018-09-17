;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")



(setq $cycle-rule nil $symmetry-terms nil)

(defun is-cycle-eqn (eqn &aux vars lhs)
  (and (not (ctx eqn))
       (or (ac-root (setq lhs (lhs eqn))) $polynomial)
       (same-list (all-ops lhs) (all-ops (rhs eqn)))
       (same-list (setq vars (all-vars lhs)) (all-vars (rhs eqn)))
       (not (lrpo lhs (rhs eqn)))
       (not (lrpo (rhs eqn) lhs))))

(defun is-symmetry-eqn (vars lhs rhs &aux rhs1)
  (if* (cddr vars) then nil
      elseif (cdr vars) 
      then
      (setq vars (list (cons (car vars) (cadr vars))
		       (cons (cadr vars) (car vars))))
      (if* (equal lhs (setq rhs1 (flat-term (applysubst vars rhs))))
	  then t
	  elseif (equal rhs rhs1)
	  then (equal lhs (flat-term (applysubst vars lhs))))
      else t))

(defun same-list (l1 l2)
   (sloop for xa in l1 do
     (if* (memq xa l2) then (setq l2 (delete0 xa l2 1)) 
	 else (return nil))
     finally (return (null l2))))

(defun make-cycle-rule (eqn)
  (let ((s1 (size (lhs eqn))) (s2 (size (rhs eqn))) rule)
    (if* (= s1 s2) then
      (if* (ac-root (lhs eqn)) 
	  (if* (> (setq s1 (apply 'max
				 (mapcar 'cdr (mult-form
					       (args-of (lhs eqn))))))
		 (setq s2 (apply 'max 
				 (mapcar 'cdr (mult-form
					       (args-of (rhs eqn)))))))
	      then (setq s1 (lhs eqn) s2 (rhs eqn))
	      elseif (< s1 s2)
	      then (setq s2 (lhs eqn) s1 (rhs eqn))
	      elseif (total-order (lhs eqn) (rhs eqn))
	      then (setq s2 (lhs eqn) s1 (rhs eqn))
	      else (setq s1 (lhs eqn) s2 (rhs eqn)))
 		 ; else
	(if* (total-order (lhs eqn) (rhs eqn))
	    then (setq s2 (lhs eqn) s1 (rhs eqn))
	    else (setq s1 (lhs eqn) s2 (rhs eqn))))
      elseif (> s1 s2)
      then (setq s1 (lhs eqn) s2 (rhs eqn))
      else (setq s2 (lhs eqn) s2 (rhs eqn)))

    (setq rule (make-new-rule s1 s2 nil (eqn-source eqn) nil 100000))
    (push-end rule $rule-set)
    (add-associate-list (op-of (lhs rule)) rule $cycle-op-rules)
    (if* (> $trace_flag 1) then (terpri)
	(princ "Adding cycle rule: ") (write-rule rule))
    (cycle-reduce-others rule)))

(defun cycle-reduce-others (rule &aux l2)
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
  (sloop with rnum = (ruleno rule)
	for xa in $rule-set 
	if (and (not (= rnum (ruleno xa)))
		(neq (car (rule-source xa)) 'def)) do
     (if* $induc (setq $premises-set (ctx xa)))
     (if* (memq rnum $del-rule-nums) 
	 then (return nil)
	 elseif (setq l2 (cycle-rewrite-rule (lhs xa) rule))
	 then
	 (if* (> $trace_flag 1) then
	     (terpri) (princ "  Deleting rule:") (write-rule xa))
	 (clean-rule xa) ; removes from op_rules and if ac corr. pairs.
	 (if* $induc then 
	     (setq l2 (make-eqn (norm-ctx l2) (rhs xa) (ctx xa) 
				(append (list 'deleted (ruleno xa) rnum)
					(rem-dups $used-rule-nums)))
		   $used-rule-nums nil
		   l2 (pre-crit-checkeq l2))
	     else
	     (setq l2 (make-eqn l2 (rhs xa) (ctx xa) 
				(list 'deleted (ruleno xa) rnum))))
	 (process-del-rule l2 xa)
	 elseif (and (> $reduce-system 2)
		     (nonvarp (rhs xa))
		     (same-op (rhs xa) (lhs rule))
		     (setq l2 (cycle-reduce-at-root-1 (rhs xa) rule)))
	 then
	 (if* (> $trace_flag 1) then
	     (terpri) (princ "  The right hand side is reducible:") 
	     (terpri) (princ "    ") (write-rule xa))
	 (setq l2 (if* (variablep l2) then l2
		      elseif (predicatep (op-of l2))
		      then (norm-rhs l2)
		      else (norm-ctx l2)))
	 (replace xa (change-rhs xa l2)))))


(defun cycle-norm-term (term)
  (sloop for t1 = (cycle-reduce-term term $cycle-op-rules)
	if t1 do (setq term t1) 
	else return term))

(defun cycle-reduce-term (term op-rules)
  ; Rewrites TERM once at the first possible leftmost-outermost position.
  (cond ((variablep term) nil)
        ((assoc (op-of term) op-rules)
	 (sloop for rule in (rules-with-op (op-of term) op-rules)
	       if (setq rule (cycle-reduce-at-root-1 term rule))
		 return rule
	       finally (return nil)))
	(t nil))) ; (cycle-out-red term op-rules))))

(defun cycle-out-red (term op-rules &aux subterms)
  (cond 
    ((sloop for xa in (args-of term) for i from 1
	   if (or (variablep xa) (member0 xa subs)) do nil
	   else if (setq xa (cycle-reduce-term xa op-rules))
		  return (rplnthsubt-in-by i term xa)
	   else collect xa into subs
	   finally (progn (setq subterms subs) (return  nil))))
    ((sloop for xa in (args-of term) for i from 1
	   if (not (member0 xa subterms)) do nil
	   else if (setq xa (cycle-out-red xa op-rules))
		  return (rplnthsubt-in-by i term xa)
	   else do (setq subterms (delete0 xa subterms))
	   finally (return nil)))))

(defun cycle-rewrite-at-root (term rules)
  (sloop for rule in rules thereis (cycle-reduce-at-root-1 term rule)))

(defun cycle-rewrite-rule (term rule &aux (lhs (lhs rule)))
  (if* (and (same-op term lhs)
	   (memq (op-of lhs) $ac)
	   (nonvarp (first-arg lhs))
	   (null (remove0 (first-arg lhs) (cddr lhs)))) ; lhs has one distinct arguement.
      (cycle-reduce-at-root-2 term rule)
      (cycle-reduce-at-root-4 term rule)))

(defun cycle-reduce-at-root-1 (term rule &aux (lhs (lhs rule)))
  ; Assuming the lhs of "rule" and "term" have the same root.
  (if* (and (memq (op-of term) $ac)
	   (nonvarp (first-arg lhs))
	   (null (remove0 (first-arg lhs) (cddr lhs)))) ; lhs has one distinct arguement.
      (cycle-reduce-at-root-2 term rule)
      (cycle-reduce-at-root-3 term rule)))

(defun cycle-reduce-at-root-2 (term rule &aux new)
  ; using one of the arguments of lhs of rule to rewrite any arguments of term.
  ; its result can be rewriten by any rules.
  ; Efficient usage of cycle rules.
  (sloop with arg = (first-arg (lhs rule))
	with n = (length (args-of (lhs rule)))
	for xa in (mult-form (args-of term))
	as arg2 = (car xa)
	if (and (>= (cdr xa) n) 
		(nonvarp arg2)
		(same-op arg arg2)
		(setq new (cycle-reduce-at-root-3 
			    arg2
			    (make-rule arg (first-arg (rhs rule)) nil 
				       (ruleno rule) nil nil nil nil))))
	  return (append (remove0 arg2 term n) (ntimes n new))))
;	  return (norm-term-simple 
;		   (flat-term (append (remove0 arg2 term n) (ntimes n new))))))

(defun cycle-reduce-at-root-3 (term rule)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (if* (and $polynomial (memq (op-of term) '(+ *))) then
      (poly-cycle-reduce-at-root-one-rule term rule)
      else
      (setq rule (reduce-at-root-one-rule term rule))
      (if* (total-order rule term) rule)))
;      (if* (total-order (setq rule (norm-term-simple rule)) term) rule)))

(defun cycle-reduce-at-root-4 (term rule &aux new)
  ; returns nil if term cant be rewritten at root else rewritten term.
  (if* (setq new (if* (and $polynomial (memq (op-of term) '(+ *)))
		    (poly-reduce-at-root-one-rule term rule)
		    (reduce-at-root-one-rule term rule)))
      (if* (total-order new term) new)))

;;;; Following functions play the role in deleting AC-unifiers by symmetry relations.

(defun get-symmetry-terms (rule &aux l1)
  (if* (setq l1 (symmetry-vars rule)) (cons l1 (symmetry-terms (lhs rule) l1))))

(defun same-nonvar (t1 t2) (if* (match t1 t2) (match t2 t1)))

(defun symmetry-vars (rule &aux results)
  ; If lhs contains some AC operator, return a list of symmetry variables in lhs.
  (if* (have-common $ac (all-ops (lhs rule))) then
      (sloop with vars = (var-list (lhs rule))
	    with first 
	    while vars do
	(setq first (car vars) vars (cdr vars))
	(sloop for second in vars 
	      if (is-symmetry-rule rule first second) 
		do (add-associate-list first second results)
		   (setq vars (delete0 second vars 1)))
	    finally (return results))))

(defun is-symmetry-rule (rule xa xb)
  ; return t iff h1(rule) = h2(rule) where
  ;     h1(xa) = you and h1(xb) = me
  ;     h2(xa) = me  and h2(xb) = you.
  (let ((h1 (list (cons xa 'you) (cons xb 'me)))
	(h2 (list (cons xb 'you) (cons xa 'me))))
    (and (equal (make-flat (applysubst h1 (rhs rule)))
		(make-flat (applysubst h2 (rhs rule))))
	 (equal (make-flat (applysubst h1 (lhs rule)))
		(make-flat (applysubst h2 (lhs rule)))))))

(defun symmetry-terms (term symvars &aux subst results)
  ; return all equivalent terms under the symmtry variables and are
  ; arguements of the same AC-operator.
  (cond ((variablep term) nil)
	((ac-root term) 
	 (sloop with args = (rem-dups (args-of term))
	       with first 
	       while args do
	   (setq first (car args) args (cdr args))
	   (sloop for second in args 
	      if (and (setq subst (same-nonvar first second))
		      (sloop for pair in subst 
			    as v1 = (car pair)
			    as v2 = (cdr pair)
			    always (or (equal v1 v2)
				       (sloop for vars in symvars
					     always (and (memq v1 vars)
							 (memq v2 vars))))))
		do (add-associate-list first second results)
		   (setq args (delete0 second args 1)))
	    finally (return results)))
	(t (sloop for xa in (args-of term) 
		 append (symmetry-terms xa symvars)))))

(defun cycle-pairs (l1 &aux result previous) 
  ; if l1 = (a b c ... d)
  ; return ((a b) (b c) (c .) ... (d a))
  (setq previous (car l1))
  (sloop for xa in (cdr l1) do
    (push (cons previous xa) result)
    (setq previous xa))
  (push (cons previous (car l1)) result))
