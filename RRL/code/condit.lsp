;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

(in-package "USER")

(setq $condi-dominate 2)

; The premise set of an equation or a rule is organized as
; a ground rewriting system. 
; The mark of a premise set is "*&*".
; Each premise is in form of
;          (lhs rhs property-list)
; lhs is a predicate term. Sometimes lhs is rooted by "and" and sometimes
; is rooted by "=", in this case, two function terms are arguments of "=".
; rhs is either nil, means true or a predicate term.
; We have the following macros for premises.
;    make-pre: make a new premise from a pair of terms.
;    is-premise-set: return t if (eq (car (ctx eqn)) '*&*).
;    get-premises: return a list of premises without the mark.
;    get-pre-lhs: return the left-hand side when a premise is viewed as a rule.
;    get-pre-rhs: return the right-hand side when a premise is viewed as a rule.

(defun cover-normal-proof (eqn0 &aux (eqn (flatten-eqn eqn0)))
  (setq eqn (cover-normalize eqn t))
  (print-normalized-eqn eqn0 eqn)
  (setq $premises-set nil)
  (if* (and eqn (car eqn))
       then (setq $induc eqn)
       else (query-add-eqn eqn0) nil)
  )

(defun print-normalized-eqn (eqn0 eqn &optional num)
  ;;  eqn is the normalized eqn0.
  (setq $used-rule-nums (rem-dups $used-rule-nums))
  ;(setq $used-rule-nums (rem-dups (append (cddr (eqn-source eqn)) $used-rule-nums)))
  (when (and (> $trace_flag 1) (or $used-rule-nums (null eqn) (null (car eqn))))
	(terpri)
	(cond ((cdr $used-rule-nums) (princ "By rules "))
	      ($used-rule-nums (princ "By rule "))
	      ((not (and eqn (car eqn))) (princ "By reformulation, ")))
	(dolist (num (reverse $used-rule-nums)) (princ "[") (princ num) (princ "], "))
	(if (and eqn (null (car eqn)))
	    (princ "and by switching the head and the premises, "))
	(terpri) 
	(princ "    ")
	(write-seq-eqn num eqn0)
	(princ "     is reduced to")
	(if (null (cdr (ctx eqn))) (setq eqn (change-ctx eqn nil)))
	(if* (car eqn) 
	     then (terpri) (princ "    ") (write-seq-eqn num eqn) 
	     else (princ " true.") (terpri))
	)
  )

(defun cover-norm-order (eqn &aux eqn1)       
  ;; normalize eqn and order it into a rule.
  (setq eqn1 (add-time $norm_time (cover-normalize eqn)))
  (cond ((null eqn1) nil)
	((null (car eqn1)) nil)
	((and-lhs-true-rhs eqn1)
	 (sloop for new in (split-lhs-and eqn1) 
		do (orient-an-eqn new $induc-eqns)))
	(t (cover-orient-eqn eqn1 $induc-eqns))))

(defun cover-normalize (eqn &optional at-top)
  ;; the main normalization procedure in cover-set induction.
  (setq $deep-condi $over-rewrite)
  (if* (equal (lhs eqn) (rhs eqn)) 
      then nil
      elseif (ctx eqn) then
      (setq $used-rule-nums nil)
      (cover-condi-norm eqn)
      else
      (cover-uncondi-norm eqn at-top)
      ))

(defun cover-uncondi-norm (eqn at-top &aux res)
  ;; normalize an unconditional equation.
  (setq $premises-set nil
	$var-premises nil
	eqn (cover-norm-uncondi-eqn eqn))
  (when eqn 
	(if* (setq res (consistent-pair (lhs eqn) (rhs eqn) (ctx eqn))) then
	     (justify-eqn eqn res)
	     elseif at-top then eqn
	     else (make-eqn $false-term $true-term nil (eqn-source eqn)))
	))

(defun cover-norm-uncondi-eqn (eqn &optional consistent &aux lhs rhs)
  ; Returns NIL if after normalizing both sides of EQN they are equal; 
  ; otherwise, returns a new equation of the normalized form of both sides.

  ; Avoiding rules bite one's own tails.
  (setq $avoid-rules nil)

  (if* (not (equal (lhs eqn) (rhs eqn))) then
      (setq $used-rule-nums nil
	    lhs (cover-norm-term (lhs eqn))
	    rhs (cover-norm-term (rhs eqn)))
      (when (and (nonvarp rhs) (nonvarp lhs)) 

;	    (arrange-eq-args lhs rhs)

	    (if* (and (truep rhs) (eq (op-of lhs) '=)
		      (is-subset (all-vars (second-arg lhs))
				 (all-vars (first-arg lhs))))
		 then (setq rhs (second-arg lhs)
			    lhs (first-arg lhs))
		 elseif (and (eq (op-of lhs) 'not))
		 then (setq lhs (first-arg lhs)
			    rhs (ba-simp-not rhs))))
		     
      (if* (equal-term lhs rhs) 
	   then nil
	   else
	   (setq eqn (make-eqn lhs rhs (ctx eqn) (eqn-source eqn)))
	   (if (not consistent) 
	       (last-consistency-check eqn)
	     eqn))))

(defun cover-norm-term (term &aux new) 
  (if* (or (variablep term) (truep term) (falsep term))
       then term 
       else
       (if $var-premises (setq term (subst-var-premises term)))

       (setq $false-rhs nil
	     new (if (predicatep (op-of term)) 
		     (norm-bool-innermost term)
		   (norm-term term)))

       (when (and $condi-dominate-rules (eq $condi-dominate 2))
	     ;(if $try (print-current-premises))
	     (setq new (or (reduce-at-root-by-extra-prevars-rules new) new)))

       (if* (equal new term) 
	    then term
	    elseif (equal (setq term (flat-term new)) new) 
	    then new
	    else (cover-norm-term term))))

(defun norm-but-root (term new)
  (setq	$premises-set new
	new (sloop for arg in (args-of term) collect (cover-norm-term arg))
	new (make-term (op-of term) new)
	$premises-set nil
	term (cover-norm-term new)
	))

#|
(defun post-checkeq (eqn pres-set &aux res)
  ; check whether eqn is consistent, return a new equation if not.
  ; Otherwise, move a premise from pres to make a new head.
  (if* (setq res (consistent-pair (lhs eqn) (rhs eqn) (ctx eqn)))
      then (change-ctx (justify-eqn eqn res) (remove-relevant eqn pres-set))
      else (down-hill-one (cdr pres-set) (change-ctx eqn pres-set))))
|#

(defun pre-crit-checkeq (pair)
  ; If a new critical pair has inconsistant head, then move one premise down.
  (if* (equal (first pair) (second pair)) then nil
      elseif (consistent-pair (lhs pair) (rhs pair) (ctx pair))
      then pair
      else (down-hill-one (cdr (ctx pair)) pair nil)))

(defun cover-condi-norm (eqn &aux head)
  ; Return 
  ;   1. nil if equation is reduced to identity or one premise is reduced 
  ;      to false.
  ;   2. an reduced equation
  ;   3. a "nil" cons to a reduced equation if one of premieses can be reduced
  ; to false if the head is used as premise.
  (if* (is-premise-set (ctx eqn))
      then (setq $premises-set (ctx eqn) $var-premises nil)
      else (setq $premises-set (ncons '|*&*|) $var-premises nil)
           (pre-process-premises (ctx eqn)))

  (setf (cdr $premises-set) (sort (cdr $premises-set) 'smaller-pre-car))

  ; Using the head to simplify the equation.
  (when (setq head (negate-one-pre (eqn2pre eqn 'head))) 
	(if* (falsep head)
	     then (return-from cover-condi-norm
			       (check-head-role eqn (cdr $premises-set)))
	     elseif (eq (car head) '*&*)
	     then (mapcar #'add-premise-end (cdr head))
	     else (add-premise-end head)))

  (if $try (print-current-premises))

  (setq $reduced-premises nil)
  (simplify-all-premises)

  (if (falsep $premises-set)
      (return-from cover-condi-norm
		   (check-head-role eqn (cdr $premises-set))))

  (when (and (eq $condi-dominate 1)
	     (eq (car $premises-set) '*&*))
	;; Build more premises from $condi-dominate-rules.
	(sloop for rule in $condi-dominate-rules do
	      (add-extra-premise rule))
	(simplify-all-premises))

  (if (falsep $premises-set)
      (return-from cover-condi-norm
		   (check-head-role eqn (cdr $premises-set))))

  (when (eq (car $premises-set) '*&*) 
	(reduce-reverse-premises $premises-set nil))

  (if $try (print-current-premises))
      
  (if* (falsep $premises-set) 
      then (if (eq $induc 'c)
		(setq $premises-set nil $var-premises nil)
	     (check-head-role eqn (cdr $premises-set)))
      else
      (if (eq $induc 'c) 
	  (if (no-subsumption (cdr $premises-set))
	      (build-equation-from-prems (cdr $premises-set) eqn))
	(restore-equation eqn))))

(defun smaller-pre-car (pre1 pre2)
  (< (size (car pre1)) (size (car pre2))))

(defun add-extra-premise (rule &aux sigma)
  ;; rule is a condi-dominate-rule.
  ;; find a subsitution sigma such that sigma(ctx(rule))
  ;; is a subset of $premises-set.
  ;; If found, add sigma(lhs = rhs) at the end of $premises-set.
  (when (and (<= (length (cdr (ctx rule))) (length (cdr $premises-set)))
	     (setq sigma (subsumed-premises (cdr (ctx rule)) 
					    (cdr $premises-set) nil nil)))
	(push (ruleno rule) $used-rule-nums)
	(simplify-one-pre (list (applysubst sigma (lhs rule))
				(if* (not (truep (rhs rule)))
				    (applysubst sigma (rhs rule)))
				'build))
	))

(defun subsumed-premises (pres1 pres21 pres22 sigma 
				&aux newsigma (pre1 (car pres1)) (pre2 (car pres21)))
  (cond ((null pres1) sigma)
	((null pres21) nil)
	((and (setq newsigma (match (second pre1) (second pre2) sigma))
	      (setq newsigma (match (first pre1) (first pre2) newsigma))
	      (setq newsigma (subsumed-premises (cdr pres1) 
						(append pres22 (cdr pres21))
						nil
						newsigma)))
	 newsigma)
	(t (subsumed-premises pres1 
			      (cdr pres21) 
			      (cons (car pres21) pres22)
			      sigma))))

; >>>>>>> 1/9/89
(defun no-subsumption (premises)
  ; return t iff no rule in $invalid-rules can subsume premises.
  (not (sloop for rule in $invalid-rules 
	     thereis (rule-subsumed-premises rule premises))))

(defun rule-subsumed-premises (rule premises)
  ; return t iff rule subsumes premises.
  (sloop with sigma
	with head = (negate-one-pre (eqn2pre rule))
	for pre in premises 
	if (and (setq sigma (match-premise head pre))
		(match-premises (cdr (ctx rule)) 
				(remove0 pre premises 1)
				sigma))
	return t
	finally (return nil)))

(defun simplify-all-premises ()
  ; simplify each premise in $premises-set in turn,
  ; using the rules and all premises except itself.
  (sloop with pre with flag = t while flag do 
     (setq flag nil)
     (if* (setq pre (pick-out-premise (cdr $premises-set))) then
	 (setq $premises-set (remove0 pre $premises-set))
	 (simplify-one-pre pre)
	 (if* (falsep $premises-set) then
	     (setq $falsed-pre pre
		   flag nil)
	     (return nil))
	 (setq flag t))))

(defun pick-out-premise (pres)
  (sloop with first for pre in pres 
	if (not (member0 pre $reduced-premises))
	  do (if* (variablep (car pre)) 
		 then (return pre)
                 elseif (truep (car pre))
		 then (return pre)
                 elseif (falsep (car pre))
		 then (return pre)
                 elseif (eq 'cond (op-of (car pre)))
		 then (return pre)
		 elseif (null first)
		 then (setq first pre))
	     finally (return first)))

(defun less-size-car (pre1 pre2) (< (size (car pre1)) (size (car pre2))))

(defun check-head-role (eqn pres &aux head used-rules)
  ; At this point, the premises are equal to false.
  (setq head (sloop for pre in pres if (memq 'head (cddr pre)) return pre))
  (if* (or (assoc 'head-role $var-premises) (and head (is-used-pre head))) then
     ; head is used to simplify others.
     (setq $premises-set (cons '*&* (delete0 head pres))
	   $var-premises nil
	   $reduced-premises (delete0 head pres)
	   used-rules $used-rule-nums)
     (simplify-one-pre $falsed-pre)
     (simplify-all-premises)
     (setq eqn (checkeq-normal eqn)
	   $used-rule-nums used-rules)
     (if* eqn then
	 (setq eqn (change-ctx eqn (remove-irrelevant $premises-set)))
	 (if (consistent-pair (lhs eqn) (rhs eqn) t) (cons nil eqn)))))

(defun build-equation-from-prems (pres eqn)
  ; Pick out the maximal literal from the premises "pres" as the head 
  ; to make an equation.
  ; If that one is not old head, then an addtional rewrite is needed.
  ; Delete that head from $premises-set.
  (setq pres (sloop for xa in pres if (nonvarp (car xa)) collect xa))
  (if* (not (eq (car (eqn-source eqn)) 'user)) 
      (setq pres (remove-irrelevant4 pres)))
  (if* (null pres) then 
      (prog1 
	(make-eqn $false-term nil nil 
		  (append (eqn-source eqn) (rem-dups $used-rule-nums)))
	(setq $used-rule-nums nil))
      elseif (falsep pres) then nil
      else (build-eqn-from-pres pres eqn)))
      
(defun build-eqn-from-pres (pres eqn &aux head)
  ; >>>>>>> 1/14/89
  (if* (cdr pres) then
      (setq head (sloop for pre in pres if (memq 'head pre) return pre))
      (if* (and head (eq (car (eqn-source eqn)) 'user)) then
	  (make-one-build head (delete0 head pres 1) eqn head)
	  else
	  (sloop with big = head
		with big-info = (big-pre-info head)
		with new-info 
		for xa in pres 
		if (and (nequal xa head)
			(lrpo-premises 
			 (setq new-info (big-pre-info xa)) big-info))
		do (setq big xa 
			 big-info new-info)
		finally (return (make-one-build 
				 big (delete0 big pres 1) eqn head))))
      else
      (make-one-down-hill (car pres) nil eqn nil)))

(defun print-current-premises ()
  (terpri) (princ "PREMISES: ") (princ $premises-set) (terpri)
  (princ "VAR PREMISES: ") (princ $var-premises) (terpri))

(defun make-one-build (big pres eqn head)
  (if* (or (null head) (equal big head))
      then (make-one-down-hill big pres eqn nil)
      else
      (delete0 big $premises-set 1)
      (if* (not (reducible (first big)))
	  then (delete0 'head head) (make-one-down-hill big pres eqn nil) 
	  else
	  (process-pre-ass (eqn2assertion big) (cddr big))
	  (simplify-all-premises)
          (if $try (print-current-premises))
	  (if* (falsep $premises-set) 
	      (build-equation-from-prems (cdr $premises-set) eqn)))))

(defun restore-equation (eqn &aux head)
  ; Pick out the head from the premises "pres" to make an equation.
  ; Delete that head from $premises-set.
  (setq head (sloop for pre in (cdr $premises-set) 
		   if (memq 'head (cddr pre)) return pre))
  (if* (and head (nonvarp (car head))) then

      (if (and $try (is-used-pre head)) (mark head "Used BODY !!!"))

      (delete0 head $premises-set)
      (if (and (falsep (cadr head)) (eq (op-of (car head)) '=))
	  (setq head (make-eqn (first-arg (car head))
			       (second-arg (car head))
			       nil
			       (eqn-source eqn)))
	(setq head (make-eqn (car head)
			     (ba-simp-not (cadr head))
			     nil
			     (eqn-source eqn))))

      (if (and (eq 'def (car (eqn-source eqn)))
	       (match (lhs eqn) (rhs head))
	       (not (match (lhs eqn) (lhs head))))
	  (setq head (change-lhs-rhs head (rhs head) (lhs head))))
      (change-ctx head
		  (remove-irrelevant $premises-set))
      else 
      (down-hill-one (cdr $premises-set)
		     (change-ctx eqn $premises-set) head)))

(defun eqn2pre (eqn &optional info)
  ; transform unconditional "eqn" into pre with the mark "hypo" added 
  ; if info is nil.
  (if (null info) (setq info 'hypo))
  (if* (variablep (lhs eqn))
       then (make-pre (lhs eqn) (rhs eqn) (ncons info))
       elseif (predicatep (op-of (lhs eqn)))
       then (if* (pseudo-term-ordering (rhs eqn) (lhs eqn))
		 then (make-pre (lhs eqn) 
				(if (not (truep (rhs eqn))) (rhs eqn))
				(ncons info))
		 else (make-pre (rhs eqn) 
				(if (not (truep (lhs eqn))) (lhs eqn))
				(ncons info)))
       else (make-pre (list '= (lhs eqn) (rhs eqn)) nil (ncons info))))

(defun justify-eqn (eqn res)
  ; this function always returns an equation. 
  ; "res" is the result returned by "consistent-pair". If "res" contained
  ; a changed equation, then return that equation. Otherwise, return the old one.
  (if* (and (neq res t) (neq (car res) 'and)) 
      then (make-eqn (first res) (second res) nil (eqn-source eqn))
      else eqn))

(defun head-less-pre (eqn pres)
  ; return t iff one of premises in pres is "big" than the lhs of eqn.
  (or (and (nonvarp (rhs eqn)) (falsep (rhs eqn)))
      (and (sloop with maxop-posi = (high-op-posi (op-list (lhs eqn)))
		 for pre in pres
		 thereis (>= (high-op-posi (pre-ops pre)) maxop-posi))
	   (sloop with lhsvars = (var-list (lhs eqn))
		 for pre in pres 
		 thereis (is-subset lhsvars (pre-vars pre))))))

(defun head-less-than-pres (eqn &aux new)
  ; if one of premises is bigger than the head of equation, then switch
  ; the head and that premise.
  (if* (and (ctx eqn) (setq new (pre-bigger-than-eqn (cdr (ctx eqn)) eqn))) then
      (setq new (make-one-down-hill 
		  new
		  (cons (negate-one-pre eqn) (remove0 new (cdr (ctx eqn))))
		  eqn nil))
      (if* (> $trace_flag 1) then
	  (terpri) (princ "Equation ") (write-f-eqn eqn)
	  (princ "    is transformed into") (terpri)
	  (princ "    ") (write-f-eqn new))
      new))
		
(defun pre-bigger-than-eqn (pres eqn)
  ; return the premise in "pres" which is bigger then the lhs of "eqn".
  (sloop with info = (big-pre-info eqn)
	for pre in pres
	if (lrpo-premises (big-pre-info pre) info)
	return pre
	finally (return nil)))

(defun big-pre-info (pre)
  ; >>>>>> 1/14/89
  ; return the info used to comparae two premises.
  (caseq $ordering
	 (s (list (pre-vars pre) 
		  (car pre) 
		  (+ (size (car pre)) (size (cadr pre)))))
	 (d (list (pre-vars pre)
		  (car pre)
		  (+ (depth (car pre)) (depth (cadr pre)))))
	 (t (cons (pre-vars pre) pre))))

(defun lrpo-premises (pre1 pre2 &aux vars1 vars2)
  ; Return t iff pre1 is "bigger" than pre2.
  (setq vars1 (pop pre1) vars2 (pop pre2))
  (if* (and (is-subset vars2 vars1)
	   (lrpo (car pre1) (car pre2))) then t
      elseif (and (is-subset vars1 vars2)
		  (lrpo (car pre2) (car pre1))) then nil
      elseif (memq $ordering '(s d))
      then
      (if* (> (cadr pre1) (cadr pre2))
	  then t
	  elseif (> (cadr pre2) (cadr pre1))
	  then nil
	  elseif (not (same-op (car pre1) (car pre2)))
	  then (operator-ordering (op-of (car pre1)) (op-of (car pre2)))
	  elseif (is-subset vars1 vars2)
	  then nil
	  else (is-subset vars2 vars1))
      elseif (is-subset vars1 vars2)
      then nil
      else (is-subset vars2 vars1)))

(defun ops-in-pres-of-rules (rules)
  ; return the operators which appear in the premises of rules.
  (sloop for rule in rules
	if (ctx rule) nconc (get-pres-ops (cdr (ctx rule)))))

(defun or-condi-eqn (vars eqn &optional info)
  ; eqn is in form of lhs = rhs if (*&* P1 P2 ..., Pn)
  ; return ((not P1) (not P2) ... (not Pn) (= lhs rhs))
  (append1 
    (sloop for pre in (negate-premises vars (ctx eqn) info)
	      collect pre)
;    (if* (variablep (car pre)) 
;	then `((= ,(car pre) ,(cadr pre)) nil . ,(cddr pre))
;	else pre)
    (eqn2pre eqn info)))

(defun down-hill-one (pres eqn &optional print)
  ; one of premises in "pres" is bigger than the head of "eqn".
  ; return a new equation with the negation of the bigger premise 
  ; as the head and the head of "eqn" as a new premise.
  (if* (not (eq $induc 'c)) then
      (setq pres (sloop for pre in pres 
		       if (and (nonvarp (car pre)) 
			       (not (and (is-used-pre pre) (is-hypo-pre pre))))
			 collect pre)))
  (if* (null pres) then 
      (if* (eq $induc 'c)
	  (inconsistent-eqn eqn)
	(make-eqn $false-term nil nil (eqn-source eqn)))
      else
      (sloop with big = (car pres)
	    with info = (big-pre-info big)
	    for xa in (cdr pres) 
	    as xainfo = (big-pre-info xa) 
	    if (lrpo-premises xainfo info)
	      do (setq big xa info xainfo)
	    finally (return (make-one-down-hill 
			     big (remove0 big pres 1) eqn print)))))

(defun make-one-down-hill (pre pres eqn print)
  ; Put the negation of the maximal premise
  ; as the new head, if there are some premises. Otherwise an inconsistency
  ; has been found.
  (let ((new (negate-one-pre pre)) lhs rhs)
    (setq lhs (get-pre-lhs new) 
	  rhs (get-pre-rhs new)
	  new (if* pres then (make-term '*&* pres))
	  pre (make-eqn lhs rhs new
			(append (eqn-source eqn) 
				(rem-dups $used-rule-nums)))
	  $used-rule-nums nil)
    (if* (consistent-pair (car pre) (cadr pre) pres) then
	(if* (or (> $trace_flag 2) (and print (= $trace_flag 2))) then
	    (terpri)
	    (princ "The head of the equation is inconsistent or smaller:") 
	    (terpri) (princ "    ") (write-eqn eqn)
	    (princ "  New equation is made:   ") (terpri)
	    (princ "    ") (write-eqn pre))
	pre
	elseif new then
	(down-hill-one (cdr new) eqn print)
	elseif (eq $induc 'c)
	then (inconsistent-eqn pre)
        else (make-eqn $false-term $true-term nil (eqn-source eqn)))))

;;; Functions to release some premises

;(defun remove-rerelevant (eqn pres &aux vars) 
;  ; remove those premises that the lhs is a variable or that have no relation
;  ; with other premises. -------- It turns out that some useful premises
;  ; are dropped by this function.
;  (setq pres (sloop for pre in (cdr pres) if (nonvarp (car pre)) collect pre)
;	vars (sloop for pre in pres collect (pre-vars pre))
;	pres (sloop with vars1 = (related-vars
;				  vars
;				  (var-list (list 'aaa (lhs eqn) (rhs eqn))))
;		   for var in vars
;		   for pre in pres 
;		   if (and var (have-common var vars1))
;		     collect pre))
;  (if* pres then (cons '*&* pres)))

(defun remove-irrelevant (pres) 
  (if* pres (setf (car pres) '*&*))
  pres
  )

(defun remove-irrelevant2 (eqn pres &aux newpres drops hypo)
  (sloop for pre in (cdr pres) do
	 (cond ((is-hypo-pre pre) 
		(if (is-used-pre pre) (push pre drops) (push pre hypo)))
	       ((and $drop-pres
		     (is-used-pre pre)
		     (truep (cadr pre)) 
		     (eq (caar pre) '=))
		(push pre drops))
	       (t (push pre newpres))))
  (setq newpres (nreverse newpres))

  (if hypo (setq hypo (handle-commu-hypo hypo eqn)))
  (if* (eq 'fail (car hypo)) then 
      (sloop for hyp in (cdr hypo) do (push (delete 'hypo hyp) newpres))
      (setq eqn (change-ctx eqn (cons '*&* newpres)))
      (trace-dropped-premises eqn drops)
      (cons 'fail eqn)
      else
      (if newpres (setq newpres (cons '*&* newpres)))
      (setq eqn (if hypo (change-ctx hypo newpres) (change-ctx eqn newpres)))
      (trace-dropped-premises eqn drops)
      eqn
      ))

(defun trace-dropped-premises (eqn drops)
  (when (and (> $trace_flag 1) (or $var-premises drops))
	(terpri) (princ "The following premises are dropped from:") (terpri)
	(princ "   ") (write-eqn eqn)
	(sloop for pre in drops do 
	       (princ "    the premise: ")
	       (write-one-pre pre nil) (terpri))
	(sloop for pre in $var-premises do 
	       (princ "    the premise: ")
	       (write-one-pre (make-pre (car pre) (cdr pre) nil) nil) 
	       (terpri))
	))

(defun handle-commu-hypo (hypo eqn &aux lhs rhs) 
  ; If a hypothesis has not been applied, try to use its reverse to apply
  ; on the head of the equation if the equation under proving is 
  ; a commutative relation. 
  ; If a hypothesis has been applied in any way, then throw that premise.
  ; Otherwise give a message to the user.
  (setq lhs (lhs eqn) rhs (rhs eqn))
  (sloop with result with lhs2 with rhs2 
	for pre in hypo 
	as prelhs = (get-pre-lhs pre)
	as prerhs = (get-pre-rhs pre) do
    (if* (is-commut-pair prelhs prerhs) then
	(setq lhs2 (subst0 prelhs prerhs lhs)
	      rhs2 (subst0 prelhs prerhs rhs))
	(if* (not (and (equal lhs lhs2) (equal rhs rhs2)))
	    then (setq lhs lhs2 
		       rhs rhs2 
		       result t)))
    finally (return (if* result 
			then (make-eqn lhs rhs nil (eqn-source eqn))
			else (cons 'fail hypo)))))

(defun remove-irrelevant3 (eqn &aux ops pres) 
  (if* (null (ctx eqn)) then eqn else
      (setq ops (op-list (lhs eqn))
	    ops (append ops (sloop for op in ops
				  nconc (ops-in-pres-of-rules 
					 (cdr (assoc op $op_rules)))))
	    pres (sloop for pre in (cdr pres) 
		       if (have-common (op-list (first pre)) ops)
			 collect pre))
      (if* pres then (setq pres (cons '*&* pres)))
      (change-ctx eqn pres)))

(defun remove-irrelevant4 (pres &aux newpres vars vars1 rule) 
  ; If a variable does not appear in the head of the equation and
  ; appears only in one premise, then delete that premise.
  (setq vars (sloop for pre in pres collect (pre-vars pre))
	vars1 (related-vars2 vars))
  (sloop for pre in pres
	for var in vars 
	if (or (is-subset var vars1)
	       (null (setq rule (good-unit-clause pre))))
	do (push pre newpres)
	else do (trace-remove-irrelevant4 var pre rule))
  newpres)

(defun good-unit-clause (pre)
  ; return a unconditional rule such that pre and the rule have the same
  ; right side and their left sides are unifiable.
 (sloop for rule in (rules-with-op (op-of (get-pre-lhs pre)) $op_rules)
       if (and (null (ctx rule))
	       (equal (rhs rule) (get-pre-rhs pre))
	       (unify (get-pre-lhs pre) (lhs rule)))
       return rule
       finally (return nil)))

(defun trace-remove-irrelevant4 (var pre rule)
  (if* (> $trace_flag 1) then
      (setq l__2 nil l__3 nil l__ctr 0)
      (terpri) (princ "Assuming  (Exist ") 
      (princ (car var)) 
      (sloop for xa in (cdr var) 
	    do (princ ", ") (write-variable xa nil))
      (princ " ") (write-one-pre pre) (princ ")  is true") 
      (princ " because of") 
      (terpri) (princ "    the rule") (write-rule rule)
      (push (ruleno var) $used-rule-nums)
      (princ "    so  ") (write-one-pre pre) 
      (princ "  can be removed from the following rewrite rule.") (terpri)))

(defun related-vars (pres-vars res)
  ; If there are variables of pres that is related to some variables in tvars
  ; then return the union of tvars and those vars,  otherwise, nil.
  (sloop with trash for vars in pres-vars
	do (if* (have-common vars res)
	       then (setq res (union res vars))
	            (sloop for vs in trash 
			  if (have-common vs vars) 
			    do (setq res (union res vars)
				     trash (delete0 vs trash)))
	       else (push vars trash))
	   finally (return res)))

(defun related-vars2 (vars-list)
  ; If there are variables of pres that is related to some variables in tvars
  ; then return the union of tvars and those vars,  otherwise, nil.
  (sloop with allvars with flag
	with trash = (ncons (car vars-list))
	for vars in (cdr vars-list) do
    (setq flag nil)
    (sloop for vs in trash 
	  if (have-common vs vars) 
	    do (setq trash (delete0 vs trash)
		     allvars (append allvars vs)
		     flag t))
    (if* (or flag (have-common vars allvars)) 
	then (setq allvars (append allvars vars))
	else (push vars trash))
    finally (return (if* allvars then (rem-dups allvars) 
			else (longest-list vars-list)))))

(defun high-op-posi (ops)
  ; Return the highest op-position of an operator in ops.
  (sloop with h = 0 with p
	for op in ops do 
    (if* (> (setq p (op-position op $operlist)) h) then (setq h p))
    finally (return h)))

;;; Functions to do factorizations as in resolution.

(defun factorization (eqn pres &aux newpres)
  ; Do factorization as in resolution.
  (sloop with sigma for one in pres do
    (sloop for two in newpres
	  if (falsep pres) return pres
	  else if (setq sigma (factorible one two))
		 do (setq pres (handle-factor eqn pres one two sigma))
	  finally (push one newpres))
    finally (return pres)))

(defun handle-factor (eqn pres one two sigma)
  (setq $premises-set (cons '*&* (sloop for pre in pres
				      if (nequal pre one)
					collect (applysubst-pre sigma pre)))
	$var-premises nil)
  (simplify-all-premises)

  (if $try (print-current-premises))

  (if* (not (falsep $premises-set)) then
      (trace-factor eqn one two)
      (setq one (build-eqn-from-pres (cdr $premises-set) eqn))
      (orient-an-eqn one)
      (setq $premises-set (cons '*&* pres)
	    $reduced-premises nil)
      (simplify-all-premises)
      (if* (falsep $premises-set) then $premises-set else (cdr $premises-set))
      else pres))

(defun factorible (one pre &aux l1)
  (if* (and (equal (cadr one) (cadr pre))
	   (setq l1 (unifiers (car one) (car pre))))
      then (car l1)))

(defun trace-factor (eqn one two)
  (if* (> $trace_flag 1) then  
      (terpri) (princ "In ") (write-eqn eqn) 
      (princ "    the premises ") (write-one-pre one)
      (princ " and ") (write-one-pre two)
      (princ " can be factorized.") (terpri)))

;; The following counter example shows that the conditional method
;; fails to report the proof when the equation is of form
;;   not p if p

;option
;prove
;c
;add
;(ay = ax) == false
;mem(f1(ay, y), y) == true if not mem(f1(ay, y), ax) and not (ay = y)
;mem(f1(ay, y), y) == false if mem(f1(ay, y), ax) and not (ay = y) 
;]
;kb
;add
;mem(f1(ay, ax), ax) 
;]
;kb
