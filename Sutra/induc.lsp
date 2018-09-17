;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "RRL")

#+franz (declare (special $failed-eqns $induc-eqns $gene $try 
		  $build-premises $first-induc-op))
(setq $step-deep 5)
(setq $gene t)
(setq $try t)

(defun cover-induc-prove (eqn)
  (get-cover-sets)
  (setq $failed-eqns nil
	$succ-eqns nil
	$induc-eqns nil
	$first-induc-op nil)
  (if (*catch 'prove 
	(progn
	  (if (one-induction eqn $step-deep)
	      then (succ-end-induc) 
	      else
	      (terpri)
	      (if (and $first-induc-op
		       (ok-to-continue 
			 (uconcat "Do you want more inductions on operators other than '"
				  $first-induc-op "' ?")))  
		  then
		  (setq $failed-eqns nil
			$induc-eqns nil)
		  (if (one-induction eqn $step-deep)
		      (succ-end-induc) 
		      (fail-end-induc $failed-eqns))
		  else
		  (fail-end-induc $failed-eqns)))
	  nil))
      then (fail-end-induc)))

(defun one-induction (eqn step &optional num norm &aux l2)
  ; Return t iff "eqn" is a theorem.
  (if (= $trace_flag 3) then 
      (terpri) (princ (uconcat "Down " (- $step-deep step) ": ")) (terpri)
      (princ "Proving") (write-seq-eqn num eqn))

  (if (and norm (null (setq eqn (reduction-proof eqn num)))) 
      then t ; eqn is normalized to nil.
      elseif (or (variablep (lhs eqn)) (falsep (lhs eqn)))
      then (if (> $trace_flag 1) then 
	       (terpri) (princ "Fail on") (write-seq-eqn num eqn))
           nil
      elseif (and (eq (op-of (lhs eqn)) 'and) (truep (rhs eqn))) 
      then (prove-split-and t eqn step num)
      elseif (and (nonvarp (rhs eqn)) (eq (op-of (rhs eqn)) 'and))
      then (prove-split-and nil eqn step num)
      elseif (is-previous-induc-eqn eqn $induc-eqns num) then t
      elseif (is-failed-induc-eqn eqn $failed-eqns num) then nil
      elseif (and num 
		  (setq l2 (ctx eqn))
		  (setq l2 (remove-irrelevant2 eqn (ctx eqn)))
		  (eq (car l2) 'fail))                        
      then (terpri) (princ "The induction hypotheses are not applicable in: ")
           (terpri) (princ "   ") (write-seq-eqn num eqn)
	   (setq eqn (cdr l2))
	   (if (setq l2 (build-premises eqn))
	       then (proof-under-new-premises l2 eqn num step)
	       elseif (subsumed-by eqn $induc-eqns) 
	       then (if (> $trace_flag 1) then 
			(terpri) 
			(princ (uconcat "This equation is subsumed by a previous conjecture,"
					" so we consider it as a failure."))
			(terpri))
     	            (push eqn $failed-eqns)
	            (abstract-proof eqn num step)
	       elseif (< step 1) 
	       then (if (> $trace_flag 1) then 
			(terpri) 
			(princ (uconcat "Last proof failed in "
					$step-deep " steps."))
			(terpri))
	            nil
	       else (induction-on eqn num (- step 2)))
      else
      (if l2 then (setq eqn l2))
      ;(if (subsumed-by eqn $induc-eqns) then (setq step (sub1 step)))
      (induction-on eqn num step)))

(defmacro continue-proof ()
  `(let ()
    (push eqn $induc-eqns)
    (if (loop for n from 1 for e1 in (cdr l2) 
	      always (prove-all-eqns 
		       (form-eqns-from-conj e1 (car l2) eqn (append1 num n))
		       (append1 num n) (sub1 step)))
	then
	(if (> $trace_flag 1) then (trace-succ-prove eqn num))
	(push eqn $succ-eqns)
	(if num then 
	    (push eqn $eqn-set)
	    (order-eqns))
	(pop $induc-eqns)
	else
	(pop $induc-eqns)
	(push eqn $failed-eqns)
	nil)))
 
(defun induction-on (eqn num step &aux l2)
  (if (setq l2 (build-premises eqn))
      then (proof-under-new-premises l2 eqn num step)
      elseif (building eqn num (sub1 step))
      then t
      elseif (abstract-proof eqn num (sub1 step))
      then t
      elseif (> (length (ctx eqn)) 9) 
      then (if (> $trace_flag 1) then 
	       (terpri) (princ "We won't prove it by induction because of its big size:")
	       (terpri) (princ "   ") (write-seq-eqn num eqn))
           (push eqn $failed-eqns) nil
      elseif (< step 1) then
            (if (> $trace_flag 1) then
		(terpri) (princ (uconcat "Proof failed in steps " $step-deep ":"))
		(terpri) (princ "   ") (write-seq-eqn num eqn))
	    (push eqn $failed-eqns)
	    nil
      elseif (setq l2 (make-conjectures eqn num)) 
      then (continue-proof)
      elseif (and (null num)
		  (setq l2 (str-make-conjectures eqn num)))
      then (continue-proof)
      else 
      (if (> $trace_flag 1) then 
	  (terpri) (princ "No induction scheme are possible for:")
	  (terpri) (princ "   ") (write-seq-eqn num eqn))
      (push eqn $failed-eqns) nil))

(defun prove-split-and (lhs eqn step num &aux eqns)
  ; the eqn has the form of (and p1 p2 ... pn) == true.
  ; it is equivalent to prove p1 == true, p2 == true, ....
  (setq eqns (if lhs then (split-lhs-and eqn) else (split-rhs-and eqn)))
  (terpri) (princ "Split") (write-seq-eqn num eqn)
  (princ " into:") 
  (loop for e in eqns for n from 1 do 
    (write-seq-eqn (append1 num n) e) 
    (princ "      "))
  (loop for e in eqns for n from 1 
	always (one-induction e step (append1 num n) t)))

(defun split-lhs-and (eqn)
  ; "eqn" has form of t1 and t2 and t3 and ...and tn == rhs if ctx
  ; return a list of equations as
  ;       t1 == rhs if ctx
  ;       t2 == rhs if ctx and t1
  ;       ... ...
  ;       tn == rhs if ctx and t1 and ... and tn-1
  (loop with ctx = (ctx eqn)
	for arg in (args-of (lhs eqn)) 
	collect (prog1 (make-eqn arg '(true) ctx (eqn-source eqn))
		       (setq ctx (append1 ctx (make-pre-ass arg nil))))))

(defun split-rhs-and (eqn &aux first newrhs)
  ; "eqn" has form of lhs == t1 and t2 and t3 if ctx
  ; return two new equations as
  ;       lhs == false if not(t1) and ctx
  ;       lhs == t2 and t3 if t1 and ctx.
  (setq first (first-arg (rhs eqn))
	newrhs (if (= (length (rhs eqn)) 3) 
		   then (second-arg (rhs eqn))
		   else (remove first (rhs eqn) 1)))
  (list (make-eqn (lhs eqn) '(false) 
		  (if (ctx eqn) 
		      then (append1 (ctx eqn) (make-pre-ass (negate-predicate first) nil))
		      else (list '&& (make-pre-ass (negate-predicate first) nil)))
		  (eqn-source eqn))
	(make-eqn (lhs eqn) newrhs 
		  (if (ctx eqn) 
		      then (append1 (ctx eqn) (make-pre-ass first nil))
		      else (list '&& (make-pre-ass first nil)))
		  (eqn-source eqn))))

(defun prove-all-eqns (eqns num step)
  ; Apply proof procedure on eqns, return t if success, nil otherwise.
  (if (cdr eqns) then
      (loop for n from 1 for xa in eqns
	    always (one-induction xa step (append1 num n) t))
      else
      (one-induction (car eqns) step num t)))

(defun norm-prove-all-eqns (eqns num)
  ; Apply proof procedure on eqns, return t if success, nil otherwise.
  (if (cdr eqns) then
      (loop for n from 1 for xa in eqns
	    always (null (reduction-proof xa (append1 num n))))
      else
      (null (reduction-proof (car eqns) num))))

(defun form-eqns-from-conj (conj vars eqn num &aux pres neweqn)
  ; Substitute "vars" of "eqn" by the terms in "conj" to make conjectures,
  ; i.e, a list of equations.
  (setq pres (car conj)
	neweqn (eqn-instance vars (cadr conj) eqn))
  (if (ctx eqn) then 
      (setq pres (merge-premises pres (ctx neweqn)))
      (if (cddr conj) then
	  (split-premises neweqn pres vars (cddr conj) eqn num)
	  else
	  (ncons (change-ctx neweqn pres)))
      elseif (cddr conj) then
      (setq pres (merge-premises pres (form-premises-from-conj (cddr conj) vars eqn)))
      (ncons (change-ctx neweqn pres))
      else
      (ncons (change-ctx neweqn pres))))

(defun form-premises-from-conj (conjs vars eqn)
  ; eqn is unconditional and conjs are the induction hypotheses. 
  ; vars are to be substituted in eqn.
  (cons '&& (loop for conj in conjs 
		  collect (eqn2pre (eqn-instance vars conj eqn)))))

(defun split-premises (new pres vars tuples eqn num &aux junk)
  ; tuples are induction hypotheses.
  ; eqn is conditional.
  ; Return a list of eqnations.
  (setq junk (or-condi-eqn vars eqn)
	junk (loop for tup in tuples 
		   collect (premises-instances vars tup junk))
        junk (product-lists junk)
	junk (loop for xa in junk collect (append pres xa))
	junk (rem-dups junk)
	junk (loop for xa in junk collect (change-ctx new xa)))

  (if (and (cdr junk) (> $trace_flag 1)) then 
      (terpri)
      (princ "Conjecture") (write-seq-num num) 
      (princ "is split into:") (terpri)
      (loop for xa in junk for n from 1 do
	(write-seq-eqn (append1 num n) xa)))
  junk)

(defun premises-instances (vars tuple pres &aux sigma)
  (setq sigma (loop for va in vars for term in tuple collect (cons va term)))
  (loop for pre in pres collect (premise-instance sigma pre)))

(defun premise-instance (sigma pre)
  ; apply sigma on pre. If necessary, flatten the result.
  (setq pre (applysubst sigma pre))
  (if (or $ac $commutative) then 
      (make-pre (make-flat (car pre)) (make-flat (cadr pre)) (cddr pre))
      else pre))

(defun eqn-instance (vars tuple eqn &aux sigma)
  (setq sigma (loop for va in vars for term in tuple collect (cons va term)))
  (applysubst-eqn sigma eqn))

(defun trace-hypothese (l1 l2 step)
  (terpri) (princ (uconcat "[" (+ 1 $step-deep (minus step))
			   "] Induction hypotheses are: ")) (terpri)
  (mapcar 'write-eqn l1) (terpri)
  (princ "Subgoals are: ") (terpri)
  (mapcar 'write-eqn l2))

;(defun reduction-proof (eqn num &optional premises &aux new)
(defun reduction-proof (eqn num &aux new)
  ; return nil iff eqn is proved by reduction or by adding new premises.
  (setq $used-rule-nums nil)
  (if (null (cdr (setq new (normal-prove eqn)))) then
      (if (> $trace_flag 1) then
	  (terpri) 
	  (if $used-rule-nums then
	      (princ (uconcat "By the rule" (if (cdr $used-rule-nums) then "s" else "")))
	      (loop for xa in (rem-dups (reverse $used-rule-nums))
		    do (princ (uconcat " [" xa "],")))
	      else
	      (princ "By reformulation,"))
	  (if new then (princ " and switching the body and the premises,"))
	  (terpri)
	  (princ "   ") (write-seq-eqn num eqn)
	  (princ "    is reduced to true.") (terpri))
      nil
;      elseif premises then 
;      (if (proof-under-new-premises premises new num) then nil else new)
      else new))

(defun normal-prove (eqn)
  ; return nil iff eqn is proved by reduction.
  (if (and (setq eqn (induc-checkeq eqn)) (car eqn)) then
      (if (or (variablep (lhs eqn)) 
	      (and (eq (op-of (lhs eqn)) 'and) (not (truep (rhs eqn))))
	      (and (not (is-oneway eqn)) (lrpo (rhs eqn) (lhs eqn))))
	  then (exchange-lr eqn) 
	  else eqn)
      elseif eqn then (ncons nil)))

(defun norm-order-only ()
  (if (or $ac $commutative) then
      (setq $eqn-set (mapcar 'flatten-eqn $eqn-set)))
  (loop while $eqn-set do (*catch 'kb-top (process-equation (pop $eqn-set))))
  (if $post-set then (setq $eqn-set $post-set $post-set nil)))

(defun order-only ()
  (loop with res while $eqn-set do 
     (setq res (pop $eqn-set))
     (*catch 'kb-top (if (is-assertion res)
			then (order-ass (lhs res) (ctx res) (eqn-source res))
			else nil))) ; (order-an-eqn res))))
  (if $post-set then (setq $eqn-set $post-set $post-set nil)))

(defun order-one-norm-others (eqn)
  (*catch 'kb-top (orient-an-eqn eqn))
  (norm-order-only))

(defun applysubst-eqn (sigma eqn)
  (let ((lhs (applysubst sigma (lhs eqn)))
	(rhs (applysubst sigma (rhs eqn)))
	(ctx (applysubst sigma (ctx eqn))))
    (setq eqn (make-eqn lhs rhs ctx (eqn-source eqn)))
    (if (or $ac $commutative) then (flatten-eqn eqn) else eqn)))

(defun applysubst-pre (sigma pre)
  (cons (flat-term (applysubst sigma (car pre)))
	(cons (flat-term (applysubst sigma (cadr pre)))
	      (cddr pre))))

(defun greater-arity (op1 op2) (> (get-arity op1) (get-arity op2)))

(defun change-vars (tree vars)
  (let ((subst (loop for var in (intersection (var-list (lhs tree)) vars)
		     collect (cons var (make-new-variable)))))
    (sublis subst tree)))

(defun trace-succ-prove (eqn num)
  (terpri) (princ "All subgoals of") (write-seq-num num)
  (princ "are proven, hence") (terpri) (princ "   ")
  (write-seq-eqn num eqn) (princ "    is an inductive theorem.") (terpri))

(defun is-failed-induc-eqn (eqn eqns num &aux yes sigma) 
  (loop for xa in eqns do
    (if (setq sigma (similar-eqn xa eqn)) then
	(if (ctx eqn) then 
	    (if (ctx xa) then 
		(setq $premises-set (ctx xa)
		      yes (premises-are-true (applysubst sigma (ctx eqn)))
		      $premises-set nil))
	    else (setq yes t))
	(if yes then (return yes))))
  (if yes then
      (terpri) (princ "Conjecture")
      (write-seq-eqn num eqn)
      (princ "    is one of previous failed conjectures.") (terpri)
      t))

(defun is-previous-induc-eqn (eqn eqns num) 
  ; return t iff one of "eqns" can reduce "eqn" to t.
  (if (ctx eqn) then (setq $premises-set (ctx eqn) $var-premises nil))
  (loop for xa in eqns
	if (and (similar-eqn eqn xa)
		(equal (reduce-by-one-rule (lhs eqn) xa) (rhs eqn)))
	  do
	    (terpri)
	    (princ "Conjecture")
	    (write-seq-eqn num eqn)
	    (princ "    is one of previous induction conjectures.")
	    (terpri)
	    (setq $premises-set nil)
	    (setq $var-premises nil)
	    (return t)
	    finally (return (setq $premises-set nil $var-premises nil))))

(defun similar-eqn (e1 e2)
  ; return t iff "e1" and "e2" are the same after renmaing the variables.
  (similar-term (list 'xxx (lhs e1) (rhs e1)) (list 'xxx (lhs e2) (rhs e2))))

(defun similar-term (t1 t2)
  ; return t iff "t1" and "t2" are the same after renmaing the variables.
  (and (applies t1 t2) (applies t2 t1)))

(defun write-seq-eqn (num eqn) (write-seq-num num) (write-f-eqn eqn))

(defun write-seq-num (nums)
  (if nums then
      (princ (uconcat " [" (car nums)))
      (loop for xa in (cdr nums) do (princ (uconcat "." xa)))
      (princ "] ")
      else
      (princ " [main] ")))

(defun mark (x &optional string)
  (terpri) (princ x) (if string then (princ " <== ") 
  (princ string)) (terpri))

(defun see (lis) (loop for xa in lis do (terpri) (princ xa)))

(defun subsumed-by (eqn eqns)
  (loop with lhs = (lhs eqn)
	for e in eqns thereis (is-sub-nonvar-term (lhs e) lhs)))


