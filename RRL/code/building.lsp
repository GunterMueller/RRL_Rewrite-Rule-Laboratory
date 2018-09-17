;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

(defun induc-add-rule (rule &optional as-is &aux big pres)
  ; If some variables appear only in the premises, then that rule will be 
  ; useless for reduction, at least by the current implementation.
  ; Two ways to use this kind of rules:
  ;  1. computing critical pairs with them, 
  ;  2. choose a premise as the head and put the body into premises.
  ; "induc-add-rule" is doing those two works.
  ; Conditions to invoke it: $induc is true.
  (if* (is-reduction rule)
      then (add-rule-complete rule)
      elseif (and (not as-is) 
		  (is-condi-dominate-rule rule)
		  (setq big (more-vars-premise (lhs-vars rule)
					       (reverse (cdr (ctx rule))))))
      then
      (push-end rule $del-rules)
      (terpri)
      (princ "In") (write-rule rule)
      (princ "    the premise ") (write-one-pre big nil) 
      (princ " has more variables.") (terpri)

      (setq pres (cons (negate-one-pre (eqn2pre rule))
		       (remove0 big (cdr (ctx rule)) 1))
	    big (make-one-down-hill big pres (r2e rule) nil))
      (terpri)
      (princ (uconcat "New equation is made from Rule [" (ruleno rule) "]:"))
      (terpri)
      (princ "    ") (write-eqn big)
      (order-one-norm-others big)
      elseif (null $induc-eqns) 
      then (if* (is-condi-dominate-rule rule)
		then (add-condi-dominate-rule rule)
		else 
		(push-end rule $rule-set)
		(terpri)
		(princ "Following rule is useless for reduction:") (terpri)
		(write-rule rule)
		)))

(defun add-condi-dominate-rule (rule)
  (push-end rule $rule-set)
  (push-end rule $condi-dominate-rules)
  (terpri)
  (princ "Following rule has extra variables in its condition:")
  (terpri) (princ "    ") (write-rule rule)
  )

(defun order-only ()
  (sloop with res while $eqn-set do 
     (setq res (pop $eqn-set))
     (*catch 'kb-top (if* (is-assertion res)
			then (order-ass (lhs res) (ctx res) (eqn-source res))
			else nil))) ; (order-an-eqn res))))
  (if* $post-set then (setq $eqn-set $post-set $post-set nil)))

(defun order-one-norm-others (eqn)
  (*catch 'kb-top (induc-orient-an-eqn eqn))
  (if* (or $ac $commutative) then
      (setq $eqn-set (mapcar 'flatten-eqn $eqn-set)))
  (sloop while $eqn-set do (*catch 'kb-top (process-equation (pop $eqn-set))))
  (if* $post-set then (setq $eqn-set $post-set $post-set nil))
  )

(defun cover-orient-eqn (eqn &optional good-only)
  (if (ctx eqn) (setq eqn (release-premises eqn)))
  (if (falsep (lhs eqn)) (refuted-result (eqn-source eqn)))
  (if eqn (setq eqn (*catch 'reset 
			    (add-time $ord_time 
				      (orient-rule eqn good-only)))))
  (cond ((memq eqn '(nil *reset* *kb-top*)) nil)
	(eqn (add-time $add_time (add-rule eqn)))))

(defun induc-orient-an-eqn (eqn &optional as-is &aux rule)
  (if (ctx eqn) (setq eqn (release-premises eqn)))
  (if (falsep (lhs eqn)) (refuted-result (eqn-source eqn)))
  (when eqn
	(setq rule (*catch 'reset (add-time $ord_time (orient-rule eqn))))
	(cond ((eq rule '*reset*)
	       (push eqn $eqn-set)
	       (reset))
	      ((memq rule '(nil *kb-top*)) nil)
	      (rule (add-time $add_time (induc-add-rule rule as-is))))))

(defun query-add-eqn (eqn0)
  (princ "Do you want to normalize innermost-firstly the equation ? ") 
  (when (ok-to-continue "Answer please !")
	(setf (lhs eqn0) (norm-but-root (lhs eqn0) (ctx eqn0)))
	(induc-orient-an-eqn eqn0)
	(return-from query-add-eqn nil))
  (princ "Do you want to keep the equation as is ? ") 
  (if (ok-to-continue "Answer please !") (induc-orient-an-eqn eqn0 t))
  )

(defun induc-reduce-other-rules (rule &aux l2)
  (check-build-rule rule)
  (sloop with rnum = (ruleno rule)
	 for xa in (rules-with-op (op-of (lhs rule)) $op_rules) 
	 if (and 
	     (not (eq (car (rule-source xa)) 'def))
	     (not (= rnum (ruleno xa)))
	     (setq $avoid-rules (ncons xa))
	     (setq l2 (reduce-by-one-at-root (lhs xa) rule (ctx xa))))
	 do (induc-reduce-others-aux xa l2 rnum))
  (setq $avoid-rules nil)
  )

(defun induc-reduce-others-aux (xa l2 rnum)
  (if* (> $trace_flag 1) then
    (terpri) (princ "  Deleting rule:") (write-rule xa))
  (clean-rule xa) ; removes from op_rules and if ac corr. pairs.
  (if* (nequal l2 (rhs xa)) then
    (push (make-eqn l2 (rhs xa) (ctx xa) 
		    (append (list 'deleted (ruleno xa) rnum)
			    (rem-dups $used-rule-nums)))
	  $eqn-set))
  (setq $used-rule-nums nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun release-premises (eqn &aux pres (first t) used-rules)
  ; A premise can be released if under its negation, the theorem 
  ; is still valid. 
  ; All build-in premises should be released.
  (sloop with pre2 for pre in (setq pres (cdr (ctx eqn)))
	do
    (if* (memq 'build (cddr pre))
	then (setq pres (delete0 pre pres))
	elseif (eq 'hint (op-of (car pre)))
	then (setq pres (delete0 pre pres))
	elseif (is-eq-false-pre pre) then
	(setq $used-rule-nums nil
	      $reduced-premises (remove0 pre pres)
	      $premises-set (cons '*&* $reduced-premises)
	      $var-premises nil)
	(setq pre2 (negate-one-pre pre))
	(add-simplify-others pre2)
	(simplify-all-premises)

	(if* (or (falsep $premises-set)
		(null (checkeq-normal eqn t))) then
	    (if* first then
		(terpri) (princ "In ") 
		(write-eqn (change-ctx eqn (cons '*&* pres)))
		(setq first nil))
	    (princ "    the premise ") 
	    (write-one-pre pre nil) 
	    (princ " is released,") (terpri)
	    (setq used-rules (append used-rules $used-rule-nums))
	    (setq pres (delete0 pre pres)))))
  (if* (null first) then 
    (princ "    because the equation is true under its negation.") (terpri)
    (change-source (nconc (eqn-source eqn) (rem-dups used-rules)) eqn)
    )
  (if* pres then (setq pres (cons '*&* pres)))
  (setq $premises-set nil $var-premises nil)
  (change-ctx eqn pres))

(defun build-premises-from-cond-term (eqn)
  ; return the first term whose root  is "cond".
  (find-special-term eqn '(cond)))

(defun build-premises-from-bool-term (eqn)
  ; return the first term whose root  is "and" or "or".
  (find-special-term eqn '(and or)))

(defun find-special-term (eqn ops)
  ;; return a subterm of eqn whose root is in ops.
  (or (first-spec-term (lhs eqn) ops)
      (first-spec-term (rhs eqn) ops)
      (if (ctx eqn)
	  (sloop for xa in (cdr (ctx eqn))
		 if (setq xa (first-spec-term (car xa) ops))
		 return xa))))

(defun first-spec-term (term ops)
  ;; Return the leftmost term whose outermost symbol is "cond".
  ;; If no such term, return nil.
  (if* (variablep term) then nil
      elseif (member (op-of term) ops) 
      then (or (first-spec-term (first-arg term) ops) term)
      else (sloop for xa in (args-of term)
		  if (setq xa (first-spec-term xa ops)) return xa)))

(defun have-boolean-constant (eqn)
  ; return the first boolean constant.
  (or (first-boolean-constant (lhs eqn))
      (first-boolean-constant (rhs eqn))
      (if (ctx eqn) (sloop for xa in (cdr (ctx eqn))
			   if (setq xa (first-boolean-constant (car xa)))
			   return xa))
      ))

(defun has-hint-term (ctx)
  (if ctx (sloop for xa in (cdr ctx) 
		 if (and (nonvarp (car xa))
			 (eq (op-of (car xa)) 'hint))
		 return xa)))

(defun first-boolean-constant (term)
  ;; Return the first boolean constant which is not true or false.
  ;; If no such term, return nil.
  (if* (variablep term) then nil
      elseif (null (args-of term))
      then (when (and (predicatep (op-of term)) 
		    (not (truep term))
		    (not (falsep term))
		    (not (member0 term $case-split-terms))
		    )
		 term)
      else (sloop for xa in (args-of term)
		 if (setq xa (first-boolean-constant xa)) return xa)))

#|
;; ---------------------------------------
;; This function is in x_rrl.lsp.
;; ---------------------------------------
(defun proof-under-new-premises (term oldeqn num step 
 				 &aux premise)
  (setq premise (make-pre-ass (first-arg term) nil))
  (if* $try then (terpri) (princ "NEW CONDI TERM: ") (princ term) (terpri))
  (terpri) (princ "Proving") (write-seq-eqn num oldeqn)
  (princ "    under the condition ") 
  (write-one-pre premise nil) (terpri)
  (princ "    and its negation.") (terpri)

  (and (let ((eqn (subst0 (second-arg term) term oldeqn)) l2)
	 (setq eqn (subst0 '(true) (first-arg term) eqn))
	 (setq l2 (if* (ctx eqn)
		      (append1 (ctx eqn) premise) 
		    (list '*&* premise)))
	 (setq l2 (change-ctx eqn l2))
	 (cover-proof-process l2 step (append1 num 1) t))

       (let ((eqn (subst0 (nth 3 term) term oldeqn))
	     (l2 (negate-one-pre premise))
	     )
	 (setq eqn (subst0 '(false) (first-arg term) eqn))
	 (setq l2 (if* (ctx eqn) (append1 (ctx eqn) l2) (list '*&* l2)))
	 (setq l2 (change-ctx eqn l2))
	 (cover-proof-process l2 step (append1 num 2) t))
       ))
|#

(defun check-build-rule (rule &aux subs)
  ; check whether rule is build-in rule.
  ; If it is, put it into $build-rules
  ; 
  ; $build-rules is an assoc list of
  ;        (op (op x1 ..., xn) rule subs-of-rule)
  ;
  (if* (and (variablep (rhs rule)) 
	   (null (ctx rule))
	   (not (eq (car (rule-source rule)) 'def))
	   (setq subs (free-subterms (lhs rule)))
	   (cdr subs) ;; more than one sub! HZ: 8/5/91.
	   (sloop with root = (op-position (op-of (lhs rule)) $operlist)
		 for xa in subs 
		 always (>= (op-position (op-of xa) $operlist) root))) 
      then
      (sloop for sub in subs 
	    if (or (not (assoc (op-of sub) $build-rules))
		   (and (ctx (third (assoc (op-of sub) $build-rules)))
			(null (ctx rule))))
	      do (push (list (op-of sub) sub rule subs) $build-rules)))
  )

(defun building (eqn num step &aux rules)
  ; Try to find terms in "eqn" such that these terms can be eliminated
  ; by building a rule into the premises and using abstraction technique.
  ; Return the result of proving these new equations.
  ;(if* (eq (car (eqn-source eqn)) 'user) then)
  (sloop with n = 0
	for sub in (eliminable-terms eqn 
				     (and (null num) (null $first-induc-op)))
	as ruleno-eqns = (eliminate-sub eqn sub)
	if (and ruleno-eqns (not (memq (car ruleno-eqns) rules)))
	  do 
	  (inc n)
	  (push (car ruleno-eqns) rules)
	  (if* (> $trace_flag 1) then 
	       (trace-building eqn num (car ruleno-eqns) (cdr ruleno-eqns)))
	  (if* (prove-all-eqns (cdr ruleno-eqns) (append1 num n) step) then
	       (when (> $trace_flag 1) 
		     (terpri)
		     (princ (uconcat "By adding the rule [" (car ruleno-eqns)
				     "] to the premises and the abstraction method,"))
		     (terpri) (princ "   ")
		     (write-seq-eqn (append1 num n) eqn) 
		     (princ "    is proven.") (terpri))
	       (return t))
	    finally (return nil)))

(defun trace-building (eqn num ruleno eqns) 
  (terpri)
  (princ (uconcat "By adding the rule [" ruleno
		  "] to the premises and the abstraction method,"))
  (terpri) (princ "   ")
  (write-seq-eqn num eqn)
  (princ "    is transformed into:") (terpri)
  (sloop for xa in eqns for n from 1 do
    (princ "   ") 
    (write-seq-eqn (append1 num n) xa)))

(defun remove-var-pres (eqn &aux pres)
  ; remove the premises from "eqn" such that the lhs of the premise
  ; is a variable.
  (setq $var-premises nil)
  (sloop for xa in (setq pres (cdr (ctx eqn)))
	if (variablep (car xa))
	  do (setq pres (remove0 xa pres)
		   xa (applysubst $var-premises xa)
		   $var-premises (subst0 (cadr xa) (car xa) $var-premises))
	     (add-premise-end xa)
	finally (return (if* $var-premises
			    then (applysubst-eqn 
				   $var-premises 
				   (change-ctx eqn (if* pres then (cons '*&* pres))))
			    else eqn))))

(defun eliminable-terms (eqn ask &aux term)
  ; return all eliminable substerms in the premises of "eqn".
  (or (if* (ctx eqn) then
	  (sloop for pre in (cdr (ctx eqn))
		if (truep (cadr pre))
		append (sloop for arg in (args-of (car pre))
			     if (nonvarp arg)
			     nconc (is-elim-term arg))))
      (if* (and (setq term (one-elim-subterm (lhs eqn)))
	       ask
	       (progn
		 (terpri) (princ "The term ")
		 (write-term term) (princ " in the equation") (terpri)
		 (princ "    ") (write-eqn eqn)
		 (princ "    can be eliminated.  Do you want to do it ? ")
		 (ok-to-continue "(y/n)")))
	  then (ncons term))))
	   
(defun one-elim-subterm (term)
  (if* (variablep term) then nil 
      elseif (is-elim-term term) then term
      else (sloop for xa in (args-of term) thereis (one-elim-subterm xa))))

(defun is-elim-term (term)
  ; term is eliminable if term = op(x1, x2, ..., xn) where
  ; op is defining function and x1, x2, ..., xn are distinct.
  (if* (and (nonvarp term)
	   (assoc (op-of term) $build-rules)
	   (or (and (eq (op-of term) 'rem) 
		    (variablep (first-arg term)))
	       (sloop for arg in (args-of term) always (variablep arg))
	       )
	   (null (non-linear-vars term)))
      then (ncons term)))

(defun free-subterms (term)
  ; return a list of eliminable terms.
  (if* (variablep term) then nil
      elseif (and (is-free-term term) (assoc (op-of term) $cover-sets))
      then (ncons term)
      else (mapcan 'free-subterms (args-of term))))

(defun is-free-term (term)
  ; term is eliminable if term = op(x1, x2, ..., xn) where
  ; op is defining function and x1, x2, ..., xn are distinct.
  (and (nonvarp term)
       (sloop for arg in (args-of term) always (variablep arg))
       (null (non-linear-vars term))))

(defun eliminate-sub (eqn sub &aux tmp l1 eqns)
  ; Try to replace "sub" in "eqn" by a new variable if there
  ; is rule in $build-rules containing "sub".
  ; Return (ruleno . new-equations).
  ; 
  ; $build-rules is an assoc list of
  ;        (op (op x1 ..., xn) rule subs-of-rule)
  (if* (setq tmp (assoc (op-of sub) $build-rules)) then
      (setq l1 (applies (second tmp) sub)
	    tmp (applysubst l1 (cddr tmp))
	    ; rename variables in the rule and the related subterms.
	    l1 (car tmp)
	    ;; l1 contains the rule.
	    l1 (if* (is-condi-rule l1)
		   then (or-condi-eqn (var-list (lhs l1)) l1 'build)
		   else (ncons (eqn2pre l1 'build)))
	    eqns (sloop for pre in l1
		       collect (make-eqn (lhs eqn) (rhs eqn)
					 (merge-premises (ctx eqn) (list '*&* pre))
					 (list 'gene (inc $gene-num))))
	    eqn (car (last eqns))
	    eqns (butlast eqns))
      (inc $gene-num)
      (sloop for sub in (cadr tmp) do
	(setq eqn (subst-eqn sub (make-new-variable)
			     eqn (list 'gene $gene-num))))
      (cons (ruleno (car tmp)) (append1 eqns eqn))))
