;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

(in-package "USER")

#|
;; in xrrl.lsp
(defun cover-induc-prove (eqn)
  (get-cover-sets)
  (init-cover-prove)
  (if* (*catch 'prove 
	(progn
	  (if* (cover-proof-process eqn $step-deep)
	      then (succ-end-induc) 
	      else
	      (terpri)
	      (sloop while (and $first-induc-op
			       (ok-to-continue 
				(uconcat "Do you want to try more inductions on other terms ?")))
		    do
		(setq $failed-eqns nil
		      $induc-eqns nil)
		(when (cover-proof-process eqn $step-deep)
		      (succ-end-induc)
		      (return-from cover-induc-prove nil))
		)
	      (fail-end-induc $failed-eqns))
	  nil))
      then (fail-end-induc $failed-eqns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; in xprover.lsp
(defun cover-proof-process (eqn step &optional num norm &aux l2)
  ; Return t iff "eqn" is a theorem.
  (if* (= $trace_flag 3) then 
      (terpri) (princ (uconcat "Down " (- $step-deep step) ": ")) (terpri)
      (princ "Proving") (write-seq-eqn num eqn))

  (if* (and norm (null (setq eqn (reduction-proof eqn num)))) 
      then t ; eqn is normalized to nil.
      elseif (or (variablep (lhs eqn)) (falsep (lhs eqn)))
      then (if* (> $trace_flag 1) then 
	       (terpri) (princ "Fail on") (write-seq-eqn num eqn))
           nil
      elseif (and-lhs-true-rhs eqn)
      then (prove-split-and t eqn step num)
      elseif (and (nonvarp (rhs eqn)) (eq (op-of (rhs eqn)) 'and))
      then (prove-split-and nil eqn step num)
      elseif (is-previous-induc-eqn eqn (reverse $induc-eqns) num) then t
      elseif (is-failed-induc-eqn eqn $failed-eqns num) then nil
      elseif (and num 
		  (setq l2 (ctx eqn))
		  (setq l2 (remove-irrelevant2 eqn (ctx eqn)))
		  (eq (car l2) 'fail))                        
      then (terpri) (princ "The induction hypotheses are not applicable in: ")
           (terpri) (princ "   ") (write-seq-eqn num eqn)
	   (setq eqn (cdr l2))
	   (if* ; (setq l2 (build-premises-from-cond-term eqn))
	       ; then (proof-under-new-premises l2 eqn num step)
	       ; elseif 
	       (induc-subsumed-by eqn $induc-eqns) 
	       then (if* (> $trace_flag 1) then 
			(terpri) 
			(princ (uconcat "This equation is subsumed by a previous conjecture,"
					" so we consider it as a failure."))
			(terpri))
     	            (push eqn $failed-eqns)
	            (abstract-proof eqn num step)
	       elseif (< step 1) 
	       then (if* (> $trace_flag 1) then 
			(terpri) 
			(princ (uconcat "Last proof failed in "
					$step-deep " steps."))
			(terpri))
	            nil
	       else (cover-proof-process2 eqn num (- step 2)))
      else
      (if* l2 then (setq eqn l2))
      (cover-proof-process2 eqn num step)))

;;---------------------------------------------
;; This function is in x_rrl.lsp.
;;---------------------------------------------
(defmacro continue-proof ()
  `(let ()
    (push eqn $induc-eqns)
    (if* (sloop for n from 1 for e1 in (cdr l2) 
	      always (prove-all-eqns 
		       (form-subgoals-from-patterns e1 (car l2) eqn (append1 num n))
		       (append1 num n) (sub1 step)))
	then
	(if* (> $trace_flag 1) then (trace-succ-prove eqn num))
	(push eqn $succ-eqns)
	(when (and num (null $x_indhyps))
	      (push eqn $eqn-set)
	      (order-eqns))
	(pop $induc-eqns)
	else
	(pop $induc-eqns)
	(push eqn $failed-eqns)
	nil)))
 
;;---------------------------------------------
;; This function is in x_rrl.lsp.
;;---------------------------------------------
(defun cover-proof-process2 (eqn num step &aux l2)
  (if* (setq l2 (build-premises-from-cond-term eqn))
      then (proof-under-new-premises l2 eqn num step)
      elseif (building eqn num (sub1 step))
      then t
      elseif (abstract-proof eqn num (sub1 step))
      then t
      elseif (> (length (ctx eqn)) 9) 
      then (if* (> $trace_flag 1) then 
	       (terpri) (princ "We won't prove it by induction because of its big size:")
	       (terpri) (princ "   ") (write-seq-eqn num eqn))
           (push eqn $failed-eqns) nil
      elseif (< step 1) then
            (if* (> $trace_flag 1) then
		(terpri) (princ (uconcat "Proof failed at Step " $step-deep ":"))
		(terpri) (princ "   ") (write-seq-eqn num eqn))
	    (push eqn $failed-eqns)
	    nil
      elseif (setq l2 (cover-induc-on eqn num)) 
      then (continue-proof)
      elseif (and (null num)
		  (setq l2 (structure-induc-on eqn num)))
      then (continue-proof)
      elseif (and (null num)
		  (setq l2 (have-boolean-constant eqn)))
      then (proof-under-new-premises l2 eqn num step)
      else 
      (if* (> $trace_flag 1) then 
	  (terpri) (princ "No induction schemes are possible for:")
	  (terpri) (princ "   ") (write-seq-eqn num eqn))
      (push eqn $failed-eqns) nil))
|#

(defun prove-split-bool (flag eqn step num &aux eqns)
  ; the eqn has the form of (and p1 p2 ... pn) == true if C.
  ; it is equivalent to prove p1 == true if C, p2 == true if C, ....
  (setq eqns (case flag
		   (lhs-and (split-lhs-and eqn))
		   (rhs-and (split-rhs-and eqn))
		   (lhs-or (split-lhs-or eqn))
		   (rhs-or (split-rhs-or eqn))
		   (t (break "Wrong flag"))))

  (terpri) (princ "Split") (write-seq-eqn num eqn)
  (princ " into:") 
  (sloop for e in eqns for n from 1 do 
    (write-seq-eqn (append1 num n) e) 
    (princ "      "))
  (sloop for e in eqns for n from 1 
	always (cover-proof-process e step (append1 num n) t)))

(defun split-lhs-and (eqn)
  ; "eqn" has form of t1 and t2 and t3 and ...and tn == true if ctx
  ; return a list of equations as
  ;       t1 == true if ctx
  ;       t2 == true if ctx 
  ;       ... ...
  ;       tn == true if ctx 
  (sloop for arg in (args-of (lhs eqn)) 
	 collect (make-eqn arg (rhs eqn) (ctx eqn) (eqn-source eqn))))

(defun split-lhs-or (eqn &aux res)
  ; "eqn" has form of t1 or t2 or t3 or ... or tn == true if ctx
  ; return a list of equations as
  ;       t1 == true if ctx and not t2 and .., and not tn,
  (setq res (sloop for arg in (cdr (args-of (lhs eqn))) 
		   collect (make-better-pre arg nil nil)))
  (list (make-eqn (first-arg (lhs eqn)) (rhs eqn)
		  (if (ctx eqn) 
		      (append (ctx eqn) res)
		    (cons '*&* res))
		  (eqn-source eqn))))

(defun split-rhs-and (eqn &aux first newrhs)
  ; "eqn" has form of lhs == t1 and t2 and t3 if ctx
  ; return two new equations as
  ;       lhs == false if not(t1) and ctx
  ;       lhs == t2 and t3 if t1 and ctx.
  (setq first (first-arg (rhs eqn))
	newrhs (if* (= (length (rhs eqn)) 3) 
		   then (second-arg (rhs eqn))
		   else (remove0 first (rhs eqn) 1)))
  (list (make-eqn (lhs eqn) $false-term 
		  (if* (ctx eqn) 
		      then (append1 (ctx eqn) (make-pre-ass (ba-simp-not first) nil))
		      else (list '*&* (make-pre-ass (ba-simp-not first) nil)))
		  (eqn-source eqn))
	(make-eqn (lhs eqn) newrhs 
		  (if* (ctx eqn) 
		      then (append1 (ctx eqn) (make-pre-ass first nil))
		      else (list '*&* (make-pre-ass first nil)))
		  (eqn-source eqn))))

(defun split-rhs-or (eqn &aux first newrhs)
  ; "eqn" has form of lhs == t1 or t2 or t3 if ctx
  ; Return two new equations as
  ;       lhs == true if t1 and ctx
  ;       lhs == t2 and t3 if not t1 and ctx.
  (setq first (first-arg (rhs eqn))
	newrhs (if (= (length (rhs eqn)) 3) 
		   (second-arg (rhs eqn))
		 (remove0 first (rhs eqn) 1)))
  (list (make-eqn (lhs eqn) $true-term
		  (if (ctx eqn) 
		      (append1 (ctx eqn) (make-pre-ass first nil))
		    (list '*&* (make-pre-ass first nil)))
		  (eqn-source eqn))
	(make-eqn (lhs eqn) newrhs 
		  (if (ctx eqn) 
		      (append1 (ctx eqn) (make-pre-ass (ba-simp-not first) nil))
		    (list '*&* (make-pre-ass (ba-simp-not first) nil)))
		  (eqn-source eqn))))

(defun prove-all-eqns (eqns num step)
  ; Apply proof procedure on eqns, return t if success, nil otherwise.
  (if* (cdr eqns) then
      (sloop for n from 1 for xa in eqns
	    always (cover-proof-process xa step (append1 num n) t))
      else
      (cover-proof-process (car eqns) step num t)))

(defun norm-prove-all-eqns (eqns num)
  ; Apply proof procedure on eqns, return t if success, nil otherwise.
  (if* (cdr eqns) then
      (sloop for n from 1 for xa in eqns
	    always (null (reduction-proof xa (append1 num n))))
      else
      (null (reduction-proof (car eqns) num))))

#|
;; in xrrl.lsp
(defun form-subgoals-from-patterns (conj vars eqn num &aux pres neweqn)
  ; Substitute "vars" of "eqn" by the terms in "conj" to make conjectures,
  ; i.e, a list of equations.
  (setq pres (car conj)
	neweqn (eqn-instance vars (cadr conj) eqn))
  (if* (ctx eqn) then 
      (setq pres (merge-premises pres (ctx neweqn)))
      (if* (cddr conj) then
	  (split-premises neweqn pres vars (cddr conj) eqn num)
	  else
	  (ncons (change-ctx neweqn pres)))
      elseif (cddr conj) then
      (setq pres (merge-premises pres (form-premises-from-conj (cddr conj) vars eqn)))
      (ncons (change-ctx neweqn pres))
      else
      (ncons (change-ctx neweqn pres))))
|#

(defun form-premises-from-conj (conjs vars eqn)
  ; eqn is unconditional and conjs are the induction hypotheses. 
  ; vars are to be substituted in eqn.
  (cons '*&* (sloop for conj in conjs 
		  collect (eqn2pre (eqn-instance vars conj eqn)))))

#|
;;; This function is in x_rrl.lsp.
;;; 
(defun split-premises (new pres vars tuples eqn num &aux junk)
  ; tuples are induction hypotheses.
  ; eqn is conditional.
  ; Return a list of eqnations.
  (setq pres (cdr pres)
	junk (or-condi-eqn vars eqn)
	junk (sloop for tup in tuples 
		   collect (premises-instances vars tup junk))
        junk (product-lists junk)
	junk (sloop for xa in junk collect (cons '*&* (append xa pres)))
	junk (rem-dups junk)
	junk (sloop for xa in junk collect (change-ctx new xa)))

  (if* (and (cdr junk) (> $trace_flag 1)) then 
      (terpri)
      (princ "Conjecture") (write-seq-num num) 
      (princ "is split into:") (terpri)
      (sloop for xa in junk for n from 1 do
	(write-seq-eqn (append1 num n) xa)))
  junk)
|#

(defun premises-instances (vars tuple pres &aux sigma)
  (setq sigma (sloop for va in vars for term in tuple collect (cons va term)))
  (sloop for pre in pres collect (premise-instance sigma pre)))

(defun premise-instance (sigma pre &aux lhs rhs)
  ; apply sigma on pre. If necessary, flatten the result.
  (setq lhs (applysubst sigma (car pre))
	rhs (applysubst sigma (cadr pre)))

  (if (and (variablep (car pre)) (not (variablep lhs)))
      (setq lhs (list '= lhs rhs)
	    rhs nil))

  (if (or $ac $commutative) 
      (setq lhs (make-flat lhs)
	    rhs (make-flat rhs)))

  (make-pre lhs rhs (cddr pre)))

(defun eqn-instance (vars tuple eqn &aux sigma)
  (setq sigma (sloop for va in vars for term in tuple collect (cons va term)))
  (applysubst-eqn sigma eqn))

(defun trace-hypothese (l1 l2 step)
  (terpri) (princ (uconcat "[" (+ 1 $step-deep (minus step))
			   "] Induction hypotheses are: ")) (terpri)
  (mapcar 'write-eqn l1) (terpri)
  (princ "Subgoals are: ") (terpri)
  (mapcar 'write-eqn l2))

#|
;; this function is in xrrl.lsp
(defun reduction-proof (eqn num &aux new)
  ; return nil iff eqn is proved by reduction or by adding new premises.
  (setq $used-rule-nums nil)
  (if* (null (cdr (setq new (normal-prove eqn)))) then
      (if* (> $trace_flag 1) then
	  (terpri) 
	  (if* $used-rule-nums then
	      (princ (uconcat "By the rule" (if* (cdr $used-rule-nums) then "s" else "")))
	      (sloop for xa in (rem-dups (reverse $used-rule-nums))
		    do (princ (uconcat " [" xa "],")))
	      else
	      (princ "By reformulation,"))
	  (if* new then (princ " and switching the head and the premises,"))
	  (terpri)
	  (princ "   ") (write-seq-eqn num eqn)
	  (princ "    is reduced to true.") (terpri))
      nil
      else new))
|#

(defun normal-prove (eqn)
  ; return nil iff eqn is proved by reduction.
  (if* (and (setq eqn (cover-normalize  eqn)) (car eqn)) then
      (if* (or (variablep (lhs eqn)) 
	      (and (eq (op-of (lhs eqn)) 'and) (not (truep (rhs eqn))))
	      (and (not (is-oneway eqn)) (lrpo (rhs eqn) (lhs eqn))))
	  then (exchange-lr eqn) 
	  else eqn)
      elseif eqn then (ncons nil)))

(defun applysubst-eqn (sigma eqn)
  (let ((lhs (applysubst sigma (lhs eqn)))
	(rhs (applysubst sigma (rhs eqn)))
	(ctx (applysubst sigma (ctx eqn))))
    (setq eqn (make-eqn lhs rhs ctx (eqn-source eqn)))
    (if* (or $ac $commutative) then (flatten-eqn eqn) else eqn)))

(defun applysubst-pre (sigma pre)
  (cons (flat-term (applysubst sigma (car pre)))
	(cons (flat-term (applysubst sigma (cadr pre)))
	      (cddr pre))))

(defun greater-arity (op1 op2) (> (get-arity op1) (get-arity op2)))

(defun change-vars (tree vars)
  (let ((subst (sloop for var in (intersection (var-list (lhs tree)) vars)
		     collect (cons var (make-new-variable)))))
    (applysubst subst tree)))

(defun trace-succ-prove (eqn num)
  (terpri) (princ "All subgoals of") (write-seq-num num)
  (princ "are proven, hence") (terpri) (princ "   ")
  (write-seq-eqn num eqn) (princ "    is an inductive theorem.") (terpri))

(defun is-failed-induc-eqn (eqn eqns num &aux yes sigma) 
  (sloop for xa in eqns do
    (if* (setq sigma (similar-eqn xa eqn)) then
	(if* (ctx eqn) then 
	    (if* (ctx xa) then 
		(setq $premises-set (ctx xa)
		      yes (premises-are-true (applysubst sigma (ctx eqn)))
		      $premises-set nil))
	    else (setq yes t))
	(if* yes then (return yes))))
  (if* yes then
      (terpri) (princ "Subgoal")
      (write-seq-eqn num eqn)
      (princ "    is one of previous failed subgoals.") (terpri)
      t))

(defun is-previous-induc-eqn (eqn vars-eqns num) 
  ; return t iff one of "eqns" can reduce "eqn" to t.
  (if (ctx eqn) (setq $premises-set (ctx eqn) $var-premises nil))
  (sloop for va-eqn in vars-eqns
	 for xa = (cdr va-eqn) 
	 if (hypo-subsume-eqn eqn (caar va-eqn) (cdar va-eqn) xa)
	 do
	 (terpri)
	 (princ "Subgoal")
	 (write-seq-eqn num eqn)
	 (princ "    is subsumed by its ancestor:")
	 (terpri)
	 (princ "    ") (write-eqn xa)
	 (princ "    so it is true by induciton hypothesis.") 
	 (terpri) 

	 (setq $premises-set nil)
	 (return t)
	 finally (return (setq $premises-set nil))))

(defun hypo-subsume-eqn (eqn as-rule vars hypo &aux sigma)
  ;; return t iff eqn is an instance of hypo and every variable in vars
  ;; is instantiated by a variable.
  (and (setq sigma (applies (lhs hypo) (lhs eqn)))
       (sloop for var in vars always (variablep (applysubst sigma var)))
       (if as-rule
	   (equal (reduce-by-one-rule (lhs eqn) hypo) (rhs eqn))
	 (and (setq sigma (applies (rhs hypo) (rhs eqn) nil sigma))
	      (or (null (ctx hypo))
		  (and (setq sigma (match-premises (cdr (ctx hypo)) 
						   (cdr (ctx eqn))))
		       (sloop for var in vars 
			      always (variablep (applysubst sigma var))
			      )))))))

(defun similar-eqn (e1 e2)
  ;; "e1" and "e2" are the same after renmaing the variables.
  (similar-term (list 'xxx (lhs e1) (rhs e1)) (list 'xxx (lhs e2) (rhs e2))))

(defun similar-term (t1 t2)
  ; return t iff "t1" and "t2" are the same after renmaing the variables.
  (and (applies t1 t2) (applies t2 t1)))

(defun write-seq-eqn (num eqn) (write-seq-num num) (write-f-eqn eqn))

(defun write-seq-num (nums)
  (if* nums then
      (princ (uconcat " [#" (car nums)))
      (sloop for xa in (cdr nums) do (princ ".") (princ xa))
      (princ "] ")
      else
      (princ " [main] ")))

(defun mark (x &optional string)
  (terpri) (princ x) (if* string then (princ " <== ") 
  (princ string)) (terpri))

(defun see (lis) (sloop for xa in lis do (terpri) (princ xa)))

(defun induc-subsumed-by (eqn eqns)
  (sloop with lhs = (lhs eqn)
	for xa in eqns 
	if (is-sub-nonvar-term (lhs (cdr xa)) lhs)
	return (cdr xa)))

;;; >>>>> Added 11/7/90. >>>>>>>>

(defun and-lhs-true-rhs (eqn) 
  ;; Return t iff the lhs of eqn is "and-term" and rhs of eqn
  ;; is "true".
  (if* (and (eq (op-of (lhs eqn)) 'and) (truep (rhs eqn)))
      t
    (if* (ctx eqn)
	(sloop for pre in (cdr (ctx eqn))
	      for lhs = (car pre)
	      for rhs = (cadr pre)
	      if (and (nonvarp lhs)
		      (eq (op-of lhs) 'and) 
		      (falsep rhs))
	      do
	      (setq rhs (negate-one-pre (eqn2pre eqn)))
	      (setf (lhs eqn) lhs)
	      (setf (rhs eqn) $true-term)
	      (setf (car pre) (car rhs))
	      (setf (cadr pre) (cadr rhs))
	      (return t))
      )))

