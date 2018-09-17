;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

(declare (special $reduced-premises))

(defun induc-add-rule (rule &aux big pres)
  ; If some variables appear only in the premises, then that rule will be 
  ; useless for reduction, at least by the current implementation.
  ; Two ways to use this kind of rules:
  ;  1) computing critical pairs with them, 
  ;  2) choose a premise as the body and put the body into premises.
  ; "induc-add-rule" is doing those two works.
  ; Conditions to invoke it: $prove-eqn and $induc are both true.
  (if (and (ctx rule)
	   (setq big (more-vars-premise (var-list (lhs rule))
					(reverse (cdr (ctx rule)))))) then
      (push-end rule $del-rules)
      (terpri)
      (princ "In") (write-rule rule)
      (princ "    the premise ") (write-one-pre big nil) 
      (princ " has more variables.") (terpri)

      (setq pres (cons (negate-one-pre (eqn2pre rule))
		       (remove big (cdr (ctx rule)) 1))
	    big (make-one-down-hill big pres (r2e rule) nil))
      (terpri)
      (princ (uconcat "New conjecture is made from Rule [" (ruleno rule) "]:")) (terpri)
      (princ "    ") (write-eqn big)
      (order-one-norm-others big)
      else
      (add-rule-complete rule)))

(defun release-premises (eqn &aux pres (first t) used-rules)
  ; A premise can be released if under its negation, the theorem 
  ; is still valid. 
  ; All build-in premises should be released.
  (loop with pre2 for pre in (setq pres (cdr (ctx eqn)))
	do
    (if (memq 'build (cddr pre))
	then (setq pres (delq pre pres))
	elseif (is-eq-false-pre pre) then
	(setq $used-rule-nums nil
	      $reduced-premises (remove pre pres)
	      $premises-set (cons '&& $reduced-premises)
	      $var-premises nil)
	(setq pre2 (negate-one-pre pre))
	(add-simplify-others pre2)
	(simplify-all-premises)

	(if (or (falsep $premises-set)
		(null (checkeq-normal eqn t))) then
	    (if first then
		(terpri) (princ "In ") 
		(write-eqn (change-ctx eqn (cons '&& pres)))
		(setq first nil))
	    (princ "    the premise ") 
	    (write-one-pre pre nil) 
	    (princ " is released,") (terpri)
	    (setq used-rules (append used-rules $used-rule-nums))
	    (setq pres (delq pre pres)))))
  (if (null first) then 
    (princ "    because the equation is true under its negation.") (terpri)
    (change-source (nconc (eqn-source eqn) (rem-dups used-rules)) eqn)
    )
  (if pres then (setq pres (cons '&& pres)))
  (setq $premises-set nil $var-premises nil)
  (change-ctx eqn pres))

(defun build-premises (eqn)
  ; return the first argument of "cond" as the new premises.
  (or (first-arg-of-if (lhs eqn))
      (first-arg-of-if (rhs eqn))
      (if (ctx eqn) (loop for xa in (cdr (ctx eqn))
			  if (setq xa (first-arg-of-if (car xa)))
			    return xa))))

(defun first-arg-of-if (term)
  (if (variablep term) then nil
      elseif (eq (op-of term) 'cond) then (first-arg term)
      else (loop for xa in (args-of term)
		 if (setq xa (first-arg-of-if xa)) return xa)))

(defun proof-under-new-premises (term oldeqn num step 
				 &aux l2 (eqn oldeqn) (premise (make-pre-ass term nil)))
  (if $try then (terpri) (princ "NEW TERM AS PRE: ") (princ term) (terpri))
  (terpri) (princ "Proving") (write-seq-eqn num eqn)
  (princ "    under the condition ") 
  (write-one-pre premise nil) (terpri)
  (princ "    and its negation.") (terpri)
  (and (setq eqn (subst '(true) term oldeqn))
       (setq l2 (if (ctx eqn) 
		    then (append1 (ctx eqn) premise)
		    else (list '&& premise)))
       (setq l2 (change-ctx eqn l2))
       (one-induction l2 (sub1 step) (append1 num 1) t)
       (setq eqn (subst '(false) term oldeqn))
       (setq l2 (negate-one-pre premise))
       (setq l2 (if (ctx eqn) then (append1 (ctx eqn) l2) else (list '&& l2)))
       (setq l2 (make-eqn (lhs eqn) (rhs eqn) l2 (list 'built 2)))
       (one-induction l2 (sub1 step) (append1 num 2) t)))

(defun check-build-rule (rule &aux subs)
  ; check whether rule is build-in rule.
  ; If it is, put it into $build-rules
  ; 
  ; $build-rules is an assoc list of
  ;        (op (op x1 ..., xn) rule subs-of-rule)
  ;
  (if (and (variablep (rhs rule)) 
	   (null (ctx rule))
	   (not (eq (car (rule-source rule)) 'def))
	   (setq subs (free-subterms (lhs rule)))
	   (loop with root = (position (op-of (lhs rule)) $operlist)
		 for xa in subs 
		 always (>= (position (op-of xa) $operlist) root))) 
      then
      (loop for sub in subs 
	    if (or (not (assoc (op-of sub) $build-rules))
		   (and (ctx (third (assoc (op-of sub) $build-rules)))
			(null (ctx rule))))
	      do (push (list (op-of sub) sub rule subs) $build-rules))))

(defun building (eqn num step &aux rules)
  ; Try to find terms in "eqn" such that these terms can be eliminated
  ; by building a rule into the premises and using abstraction technique.
  ; Return the result of proving these new equations.
  ;(if (eq (car (eqn-source eqn)) 'user) then)
  (loop with n = 0
	for sub in (eliminable-terms eqn) 
	as ruleno-eqns = (eliminate-sub eqn sub)
	if (and ruleno-eqns (not (memq (car ruleno-eqns) rules)))
	  do (inc n)
		 (push (car ruleno-eqns) rules)
		 (if (> $trace_flag 1) then 
		     (trace-building eqn num (car ruleno-eqns) (cdr ruleno-eqns)))
		 (if (prove-all-eqns 
		       (cdr ruleno-eqns) (append1 num n) step) then
;		       (mapcar 'remove-var-pres (cdr ruleno-eqns)) (append1 num n) step) then
		     (terpri)
		     (princ (uconcat "By adding the rule [" (car ruleno-eqns)
				     "] to the premises and the abstraction method,"))
		     (terpri) (princ "   ")
		     (write-seq-eqn (append1 num n) eqn) 
		     (princ "    is proven.") (terpri)
		     (return t))
	    finally (return nil)))

(defun trace-building (eqn num ruleno eqns) 
  (terpri)
  (princ (uconcat "By adding the rule [" ruleno
		  "] to the premises and the abstraction method,"))
  (terpri) (princ "   ")
  (write-seq-eqn num eqn)
  (princ "    is transformed into:") (terpri)
  (loop for xa in eqns for n from 1 do
    (princ "   ") 
    (write-seq-eqn (append1 num n) xa)))

(defun remove-var-pres (eqn &aux pres)
  ; remove the premises from "eqn" such that the lhs of the premise
  ; is a variable.
  (setq $var-premises nil)
  (loop for xa in (setq pres (cdr (ctx eqn)))
	if (variablep (car xa))
	  do (setq pres (remove xa pres)
		   xa (applysubst $var-premises xa)
		   $var-premises (subst (cadr xa) (car xa) $var-premises))
	     (add-premise-end xa)
	finally (return (if $var-premises
			    then (applysubst-eqn 
				   $var-premises 
				   (change-ctx eqn (if pres then (cons '&& pres))))
			    else eqn))))

(defun eliminable-terms (eqn &aux term)
  ; return all eliminable substerms in the premises of "eqn".
  (or (if (ctx eqn) then
	  (loop for pre in (cdr (ctx eqn))
		if (and (truep (cadr pre))
			(eq (op-of (setq pre (car pre))) '=))
		  append (or (is-elim-term (first-arg pre))
			     (is-elim-term (second-arg pre)))))
      (if (and (setq term (one-elim-subterm (lhs eqn)))
	       (progn
		 (terpri) (princ "The term ")
		 (write-term term) (princ " in the equation") (terpri)
		 (princ "    ") (write-eqn eqn)
		 (ok-to-continue "    can be eliminated.  Do you want to do it ? ")))
	  then (ncons term))))
	   
(defun one-elim-subterm (term)
  (if (variablep term) then nil 
      elseif (is-elim-term term) then term
      else (loop for xa in (args-of term) thereis (one-elim-subterm xa))))

(defun is-elim-term (term)
  ; term is eliminable if term = op(x1, x2, ..., xn) where
  ; op is defining function and x1, x2, ..., xn are distinct.
  (if (and (nonvarp term)
	   (assoc (op-of term) $build-rules)
	   (loop for arg in (args-of term) always (variablep arg))
	   (null (non-linear-vars term)))
      then (ncons term)))

(defun free-subterms (term)
  ; return a list of eliminable terms.
  (if (variablep term) then nil
      elseif (and (is-free-term term) (assoc (op-of term) $cover-sets))
      then (ncons term)
      else (mapcan 'free-subterms (args-of term))))

(defun is-free-term (term)
  ; term is eliminable if term = op(x1, x2, ..., xn) where
  ; op is defining function and x1, x2, ..., xn are distinct.
  (and (nonvarp term)
       (loop for arg in (args-of term) always (variablep arg))
       (null (non-linear-vars term))))

(defun eliminate-sub (eqn sub &aux tmp l1 eqns)
  ; Try to replace "sub" in "eqn" by a new variable if there
  ; is rule in $build-rules containing "sub".
  ; Return (ruleno . new-equations).
  ; 
  ; $build-rules is an assoc list of
  ;        (op (op x1 ..., xn) rule subs-of-rule)
  (if (setq tmp (assoc (op-of sub) $build-rules)) then
      (setq l1 (applies (second tmp) sub)
	    tmp (applysubst l1 (cddr tmp))
	    ; rename variables in the rule and the related subterms.
	    l1 (car tmp)
	    l1 (if (is-condi-rule l1)
		   then (or-condi-eqn (var-list (lhs l1)) l1 'build)
		   else (ncons (eqn2pre l1 'build)))
	    eqns (loop for pre in l1
		       collect (make-eqn (lhs eqn) (rhs eqn)
					 (merge-premises (ctx eqn) (list '&& pre))
					 (list 'gene (inc $gene-num))))
	    eqn (car (last eqns))
	    eqns (butlast eqns))
      (inc $gene-num)
      (loop for sub in (cadr tmp) do
	(setq eqn (subst-eqn sub (make-new-variable)
			     eqn (list 'gene $gene-num))))
      (cons (ruleno (car tmp)) (append1 eqns eqn))))
