;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.
#-lispm (include datamacs.l)

(declare (special l__2 l__3 l__ctr $reduced-premises))
(setq $try nil)

; ********WARNING*********
; *****Parental guidance suggested for children under the age of 17*********
; ********WARNING*********

; The premise set of an equation or a rule is organized as
; a ground rewriting system. 
; The mark of a premise set is "&&".
; Each premise is in form of
;          (lhs rhs property-list)
; lhs is a predicate term. Sometimes lhs is rooted by "and" and sometimes
; is rooted by "=", in this case, two function terms are arguments of "=".
; rhs is either nil, means true or a predicate term.
; We have the following macros for premises.
;    make-pre: make a new premise from a pair of terms.
;    is-premise-set: return t if (eq (car (ctx eqn)) '&&).
;    get-premises: return a list of premises without the mark.
;    get-pre-lhs: return the left-hand side when a premise is viewed as a rule.
;    get-pre-rhs: return the right-hand side when a premise is viewed as a rule.

(defun newinduc-eq-prove (eqn)
  (if (setq eqn (induc-checkeq eqn t)) then
      (if (car eqn) then
	  (princ "No, it is not equational theorem.") (terpri)
	  (princ "Normal form of the left hand side is:") (terpri)
	  (princ "        ") (write-term (lhs eqn)) (terpri) (terpri)
	  (princ "Normal form of the right hand side is:") (terpri)
	  (princ "        ") (write-term-simple (rhs eqn)) (terpri)
	  (if (ctx eqn) then
	      (terpri) (princ "The premises are simplified to:") 
	      (write-premises (cdr (ctx eqn))) (terpri))
	  (setq $induc eqn)
	  eqn
	  else
	  ;(terpri)
	  (princ "Yes, by switching the body and the premises, ") 
	  (princ "the following equation") (terpri)
	  (princ "    ") (write-eqn (cdr eqn))
	  (princ "    is an equational theorem.") (terpri) (terpri)
	  (princ "Do you want to keep the theorem in the system ? ") 
	  (if (ok-to-continue "Answer please !") then (orient-an-eqn (cdr eqn)))
	  nil)
      else
      (princ "Yes, it is equational theorem.") (terpri)
      nil))

(defun induc-checkeq (eqn &optional at-top &aux res)
  (setq $deep-condi $over-rewrite)
  (if (ctx eqn) then
      (setq $used-rule-nums nil)
      (induc-condi-check eqn)
      else
      (setq $premises-set nil
	    $var-premises nil
	    eqn (checkeq-normal eqn))
      (if eqn then
	  (if (setq res (consistent-pair eqn (ctx eqn))) then
	      (justify-eqn eqn res)
	      elseif at-top
	      then eqn
	      else (make-eqn '(false) '(true) nil (eqn-source eqn))))))

(defun post-checkeq (eqn pres-set &aux res)
  ; check whether eqn is consistent, return a new equation if not.
  ; Otherwise, move a premise from pres to make a new body.
  (if (setq res (consistent-pair eqn (ctx eqn)))
      then (change-ctx (justify-eqn eqn res) (remove-irrelevant eqn pres-set))
      else (down-hill-one (cdr pres-set) (change-ctx eqn pres-set))))

(defun pre-crit-checkeq (pair)
  ; If a new critical pair has inconsistant body, then move one premise down.
  (if (equal (first pair) (second pair)) then nil
      elseif (consistent-pair pair (ctx pair))
      then pair
      else (down-hill-one (cdr (ctx pair)) pair nil)))

(defun induc-condi-check (eqn &aux body)
  ; Return 
  ;   1) nil if equation is reduced to identity or one premise is reduced 
  ;      to false.
  ;   2) an reduced equation
  ;   3) a "nil" cons to a reduced equation if one of premieses can be reduced
  ; to false if the body is used as premise.
  (if (is-premise-set (ctx eqn))
      then (setq $premises-set (ctx eqn) $var-premises nil)
      else (setq $premises-set (ncons '|&&|) $var-premises nil)
           (pre-process-premises (ctx eqn)))

  ; using the body to simplify the equation.
  (when (setq body (negate-one-pre (eqn2pre eqn 'body))) 
	(add-premise-end body))
  (setq $reduced-premises nil)
  (simplify-all-premises)

  (if (eq (car $premises-set) '&&) then 
      (reduce-reverse-premises $premises-set nil))
  (if $try then (terpri) (princ "PREMISES: ") (princ $premises-set) (terpri))
      
  (if (falsep $premises-set) 
      then (if (eq $induc 'c)
	       then (setq $premises-set nil $var-premises nil)
	       else (check-body-role eqn (cdr $premises-set)))
      else
      (if (eq $induc 'c) ; (numberp (car (eqn-source eqn)))
	  then (if (no-subsumption (cdr $premises-set))
		   (build-equation-from-prems (cdr $premises-set) eqn))
	  else (restore-equation eqn))))

; >>>>>>> 1/9/89
(defun no-subsumption (premises)
  ; return t iff no rule in $invalid-rules can subsume premises.
  (not (loop for rule in $invalid-rules 
	     thereis (rule-subsumed-premises rule premises))))

(defun rule-subsumed-premises (rule premises)
  ; return t iff rule subsumes premises.
  (loop with sigma
	with body = (negate-one-pre (eqn2pre rule))
	for pre in premises 
	if (and (setq sigma (match-premise body pre))
		(match-premises (cdr (ctx rule)) 
				(remove pre premises 1)
				sigma))
	return t
	finally (return nil)))

(defun simplify-all-premises ()
  ; simplify each premise in $premises-set in turn,
  ; using the rules and all premises except itself.
  (loop with pre with flag = t while flag do 
     (setq flag nil)
     (if (setq pre (pick-out-premise (cdr $premises-set))) then
	 (setq $premises-set (remove pre $premises-set))
	 (simplify-one-pre pre)
	 (if (falsep $premises-set) then
	     (setq $falsed-pre pre
		   flag nil)
	     (return nil))
	 (setq flag t))))

(defun pick-out-premise (pres)
  (loop with first for pre in pres 
	if (not (member pre $reduced-premises))
	  do (if (and (nonvarp (car pre)) (eq 'cond (op-of (car pre))))
		 then (return pre)
		 elseif (null first)
		 then (setq first pre))
	     finally (return first)))

(defun less-size-car (pre1 pre2) (< (size (car pre1)) (size (car pre2))))

(defun check-body-role (eqn pres &aux body used-rules)
  ; At this point, the premises are equal to false.
  (setq body (loop for pre in pres if (memq 'body (cddr pre)) return pre))
  (if (or (assoc 'body-role $var-premises) (and body (is-used-pre body))) then
     ; body is used to simplify others.
     (setq $premises-set (cons '&& (delete body pres))
	   $var-premises nil
	   $reduced-premises (delete body pres)
	   used-rules $used-rule-nums)
     (simplify-one-pre $falsed-pre)
     (simplify-all-premises)
     (setq eqn (checkeq-normal eqn)
	   $used-rule-nums used-rules)
     (if eqn then
	 (setq eqn (change-ctx eqn (remove-irrelevant eqn $premises-set)))
	 (if (consistent-pair eqn t) (cons nil eqn)))))

(defun build-equation-from-prems (pres eqn)
  ; Pick out the maximal literal from the premises "pres" as the body 
  ; to make an equation.
  ; If that one is not old body, then an addtional rewrite is needed.
  ; Delete that body from $premises-set.
  (setq pres (loop for xa in pres if (nonvarp (car xa)) collect xa))
  (if (not (eq (car (eqn-source eqn)) 'user)) 
      (setq pres (remove-irrelevant4 pres)))
  (if (null pres) then 
      (prog1 
	(make-eqn '(false) nil nil 
		  (append (eqn-source eqn) (rem-dups $used-rule-nums)))
	(setq $used-rule-nums nil))
      elseif (falsep pres) then nil
      else (build-eqn-from-pres pres eqn)))
      
(defun build-eqn-from-pres (pres eqn &aux body)
  ; >>>>>>> 1/14/89
  (if (cdr pres) then
      (setq body (loop for pre in pres if (memq 'body pre) return pre))
      (if (and body (eq (car (eqn-source eqn)) 'user)) then
	  (make-one-build body (delete body pres 1) eqn body)
	  else
	  (loop with big = body
		with big-info = (big-pre-info body)
		with new-info 
		for xa in pres 
		if (and (nequal xa body)
			(lrpo-premises 
			 (setq new-info (big-pre-info xa)) big-info))
		do (setq big xa 
			 big-info new-info)
		finally (return (make-one-build 
				 big (delete big pres 1) eqn body))))
      else
      (make-one-down-hill (car pres) nil eqn nil)))

(defun make-one-build (big pres eqn body)
  (if (or (null body) (equal big body))
      then (make-one-down-hill big pres eqn nil)
      else
      (delete big $premises-set 1)
      (if (not (reducible (first big)))
	  then (delq 'body body) (make-one-down-hill big pres eqn nil) 
	  else
	  (process-pre-ass (eqn2assertion big) (cddr big))
	  (simplify-all-premises)
	  (if $try then (terpri) (princ "PREMISES: ") (princ $premises-set)
	      (terpri))	      
	  (if (falsep $premises-set) 
	      (build-equation-from-prems (cdr $premises-set) eqn)))))

(defun restore-equation (eqn &aux body)
  ; Pick out the body from the premises "pres" to make an equation.
  ; Delete that body from $premises-set.
  (setq body (loop for pre in (cdr $premises-set) 
		   if (memq 'body (cddr pre)) return pre))
  (if (and body (nonvarp (car body))) then
      (if (and $try (is-used-pre body)) then (mark body "Used BODY !!!"))
      (delete body $premises-set)
      (setq body (negate-one-pre body)
	    body (make-eqn (get-pre-lhs body) 
			   (get-pre-rhs body)
			   nil
			   (append (eqn-source eqn) 
				   (rem-dups $used-rule-nums)))
	    $used-rule-nums nil)
      (if (and (eq 'def (car (eqn-source eqn)))
	       (match (lhs eqn) (rhs body))
	       (not (match (lhs eqn) (lhs body))))
	  (setq body (change-lhs-rhs body (rhs body) (lhs body))))
      (change-ctx body
		  (remove-irrelevant body $premises-set))
      else 
      (down-hill-one (cdr $premises-set)
		     (change-ctx eqn $premises-set) body)))

(defun eqn2pre (eqn &optional info)
  ; transform unconditional "eqn" into pre with the mark "hypo" added 
  ; if info is nil.
  (if (null info) then (setq info 'hypo))
  (if (variablep (lhs eqn))
      then (make-pre (lhs eqn) (rhs eqn) (ncons info))
      elseif (predicatep (op-of (lhs eqn)))
      then (if (order-pc (rhs eqn) (lhs eqn))
	       then (make-pre (lhs eqn) 
			      (if (not (truep (rhs eqn))) then (rhs eqn))
			      (ncons info))
	       else (make-pre (rhs eqn) 
			      (if (not (truep (lhs eqn))) then (lhs eqn))
			      (ncons info)))
      else (make-pre (list '= (lhs eqn) (rhs eqn)) nil (ncons info))))

(defun justify-eqn (eqn res)
  ; this function always returns an equation. 
  ; "res" is the result returned by "consistent-pair". If "res" contained
  ; a changed equation, then return that equation. Otherwise, return the old one.
  (if (and (neq res t) (neq (car res) 'and)) 
      then (make-eqn (first res) (second res) nil (eqn-source eqn))
      else eqn))

(defun body-less-pre (eqn pres)
  ; return t iff one of premises in pres is "big" than the lhs of eqn.
  (or (and (nonvarp (rhs eqn)) (falsep (rhs eqn)))
      (and (loop with maxop-posi = (high-op-posi (op-list (lhs eqn)))
		 for pre in pres
		 thereis (>= (high-op-posi (pre-ops pre)) maxop-posi))
	   (loop with lhsvars = (var-list (lhs eqn))
		 for pre in pres 
		 thereis (is-subset lhsvars (pre-vars pre))))))

(defun body-less-than-pres (eqn &aux new)
  ; if one of premises is bigger than the body of equation, then switch
  ; the body and that premise.
  (if (and (ctx eqn) (setq new (pre-bigger-than-eqn (cdr (ctx eqn)) eqn))) then
      (setq new (make-one-down-hill 
		  new
		  (cons (negate-one-pre eqn) (remove new (cdr (ctx eqn))))
		  eqn nil))
      (if (> $trace_flag 1) then
	  (terpri) (princ "Equation ") (write-f-eqn eqn)
	  (princ "    is transformed into") (terpri)
	  (princ "    ") (write-f-eqn new))
      new))
		
(defun pre-bigger-than-eqn (pres eqn)
  ; return the premise in "pres" which is bigger then the lhs of "eqn".
  (loop with info = (big-pre-info eqn)
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
  (if (and (is-subset vars2 vars1)
	   (lrpo (car pre1) (car pre2))) then t
      elseif (and (is-subset vars1 vars2)
		  (lrpo (car pre2) (car pre1))) then nil
      elseif (memq $ordering '(s d))
      then
      (if (> (cadr pre1) (cadr pre2))
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
  (loop for rule in rules
	if (ctx rule) nconc (get-pres-ops (cdr (ctx rule)))))

(defun or-condi-eqn (vars eqn &optional info)
  ; eqn is in form of lhs = rhs if (&& P1 P2 ..., Pn)
  ; return ((not P1) (not P2) ... (not Pn) (= lhs rhs)))
  (append1 
    (loop for pre in (negate-premises vars (ctx eqn) info)
	      collect (if (variablep (car pre)) 
			  then `((= ,(car pre) ,(cadr pre)) nil . ,(cddr pre))
			  else pre))
    (eqn2pre eqn info)))

(defun down-hill-one (pres eqn &optional print)
  ; one of premises in "pres" is bigger than the body of "eqn".
  ; return a new equation with the negation of the bigger premise 
  ; as the body and the body of "eqn" as a new premise.
  (if (not (eq $induc 'c)) then
      (setq pres (loop for pre in pres 
		       if (and (nonvarp (car pre)) 
			       (not (and (is-used-pre pre) (is-hypo-pre pre))))
			 collect pre)))
  (if (null pres) then 
      (if (eq $induc 'c)
	  (inconsistent-eqn eqn)
	(make-eqn '(false) nil nil (eqn-source eqn)))
      else
      (loop with big = (car pres)
	    with info = (big-pre-info big)
	    for xa in (cdr pres) 
	    as xainfo = (big-pre-info xa) 
	    if (lrpo-premises xainfo info)
	      do (setq big xa info xainfo)
	    finally (return (make-one-down-hill 
			     big (remove big pres 1) eqn print)))))

(defun make-one-down-hill (pre pres eqn print)
  ; Put the negation of the maximal premise
  ; as the new body, if there are some premises. Otherwise an inconsistency
  ; has been found.
  (let ((new (negate-one-pre pre)) lhs rhs)
    (setq lhs (get-pre-lhs new) 
	  rhs (get-pre-rhs new)
	  new (if pres then (make-term '&& pres))
	  pre (make-eqn lhs rhs new
			(append (eqn-source eqn) 
				(rem-dups $used-rule-nums)))
	  $used-rule-nums nil)
    (if (consistent-pair pre pres) then
	(if (or (> $trace_flag 2) (and print (eq $trace_flag 2))) then
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
        else (make-eqn '(false) '(true) nil (eqn-source eqn)))))

;;; Functions to release some premises

(defun remove-irrelevant (eqn pres &aux vars) 
  ; remove those premises that the lhs is a variable or that have no relation
  ; with other premises.
  (setq pres (loop for pre in (cdr pres) if (nonvarp (car pre)) collect pre)
	vars (loop for pre in pres collect (pre-vars pre))
	pres (loop with vars1 = (related-vars
				  vars
				  (var-list (list 'aaa (lhs eqn) (rhs eqn))))
		   for var in vars
		   for pre in pres 
		   if (and var (have-common var vars1))
		     collect pre))
  (if pres then (cons '&& pres)))

(defun remove-irrelevant2 (eqn pres &aux newpres vars hypo)
  (setq pres (loop for pre in (cdr pres) 
		   if (is-hypo-pre pre) do 
		   (if (not (is-used-pre pre)) (push pre hypo))
		   else if (not (and (neq $induc 'c)
				     (is-used-pre pre)
				     (truep (cadr pre)) 
				     (eq (caar pre) '=)))
			  collect pre)
	vars (loop for pre in pres collect (pre-vars pre)))

  (loop with vars1 = (related-vars vars
				   (var-list (list nil (lhs eqn) (rhs eqn))))
	for pre in pres
	for var in vars 
	if (and var (is-subset var vars1))
	  do (push pre newpres))

  (if hypo then (setq hypo (handle-commu-hypo hypo eqn)))
  (if (eq  'fail (car hypo)) then 
      (loop for hyp in (cdr hypo) do (push (delq 'hypo hyp) newpres))
      (cons 'fail (change-ctx eqn (cons '&& newpres)))
      else
      (if newpres then (setq newpres (cons '&& newpres)))
      (if hypo then (change-ctx hypo newpres) else (change-ctx eqn newpres))))

(defun handle-commu-hypo (hypo eqn &aux lhs rhs) 
  ; If a hypothesis has not been applied, try to use its reverse to apply
  ; on the body of the equation if the equation under proving is 
  ; a commutative relation. 
  ; If a hypothesis has been applied in any way, then throw that premise.
  ; Otherwise give a message to the user.
  (setq lhs (lhs eqn) rhs (rhs eqn))
  (loop with result with lhs2 with rhs2 
	for pre in hypo 
	as prelhs = (get-pre-lhs pre)
	as prerhs = (get-pre-rhs pre) do
    (if (is-commut-pair prelhs prerhs) then
	(setq lhs2 (subst prelhs prerhs lhs)
	      rhs2 (subst prelhs prerhs rhs))
	(if (not (and (equal lhs lhs2) (equal rhs rhs2)))
	    then (setq lhs lhs2 
		       rhs rhs2 
		       result t)))
    finally (return (if result 
			then (make-eqn lhs rhs nil (eqn-source eqn))
			else (cons 'fail hypo)))))

(defun remove-irrelevant3 (eqn &aux ops pres) 
  (if (null (ctx eqn)) then eqn else
      (setq ops (op-list (lhs eqn))
	    ops (append ops (loop for op in ops
				  nconc (ops-in-pres-of-rules 
					 (cdr (assoc op $op_rules)))))
	    pres (loop for pre in (cdr pres) 
		       if (have-common (op-list (first pre)) ops)
			 collect pre))
      (if pres then (setq pres (cons '&& pres)))
      (change-ctx eqn pres)))

(defun remove-irrelevant4 (pres &aux newpres vars vars1 rule) 
  ; If a variable does not appear in the body of the equation and
  ; appears only in one premise, then delete that premise.
  (setq vars (loop for pre in pres collect (pre-vars pre))
	vars1 (related-vars2 vars))
  (loop for pre in pres
	for var in vars 
	if (or (is-subset var vars1)
	       (null (setq rule (good-unit-clause pre))))
	do (push pre newpres)
	else do (trace-remove-irrelevant4 var pre rule))
  newpres)

(defun good-unit-clause (pre)
  ; return a unconditional rule such that pre and the rule have the same
  ; right side and their left sides are unifiable.
 (loop for rule in (rules-with-op (op-of (get-pre-lhs pre)) $op_rules)
       if (and (null (ctx rule))
	       (equal (rhs rule) (get-pre-rhs pre))
	       (unify (get-pre-lhs pre) (lhs rule)))
       return rule
       finally (return nil)))

(defun trace-remove-irrelevant4 (var pre rule)
  (if (> $trace_flag 1) then
      (setq l__2 nil l__3 nil l__ctr 0)
      (terpri) (princ "Assuming  (Exist ") 
      (princ (car var)) 
      (loop for xa in (cdr var) 
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
  (loop with trash for vars in pres-vars
	do (if (have-common vars res)
	       then (setq res (union res vars))
	            (loop for vs in trash 
			  if (have-common vs vars) 
			    do (setq res (union res vars)
				     trash (delete vs trash)))
	       else (push vars trash))
	   finally (return res)))

(defun related-vars2 (vars-list)
  ; If there are variables of pres that is related to some variables in tvars
  ; then return the union of tvars and those vars,  otherwise, nil.
  (loop with allvars with flag
	with trash = (ncons (car vars-list))
	for vars in (cdr vars-list) do
    (setq flag nil)
    (loop for vs in trash 
	  if (have-common vs vars) 
	    do (setq trash (delete vs trash)
		     allvars (append allvars vs)
		     flag t))
    (if (or flag (have-common vars allvars)) 
	then (setq allvars (append allvars vars))
	else (push vars trash))
    finally (return (if allvars then (rem-dups allvars) 
			else (longest-list vars-list)))))

(defun high-op-posi (ops)
  ; Return the highest position of an operator in ops.
  (loop with h = 0 with p
	for op in ops do 
    (if (> (setq p (position op $operlist)) h) then (setq h p))
    finally (return h)))

;;; Functions to do factorizations as in resolution.

(defun factorization (eqn pres &aux newpres)
  ; Do factorization as in resolution.
  (loop with sigma for one in pres do
    (loop for two in newpres
	  if (falsep pres) return pres
	  else if (setq sigma (factorible one two))
		 do (setq pres (handle-factor eqn pres one two sigma))
	  finally (push one newpres))
    finally (return pres)))

(defun handle-factor (eqn pres one two sigma)
  (setq $premises-set (cons '&& (loop for pre in pres
				      if (nequal pre one)
					collect (applysubst-pre sigma pre)))
	$var-premises nil)
  (simplify-all-premises)
  (if $try then (terpri) (princ "PREMISES: ") (princ $premises-set) (terpri))
  (if (not (falsep $premises-set)) then
      (trace-factor eqn one two)
      (setq one (build-eqn-from-pres (cdr $premises-set) eqn))
      (orient-an-eqn one)
      (setq $premises-set (cons '&& pres)
	    $reduced-premises nil)
      (simplify-all-premises)
      (if (falsep $premises-set) then $premises-set else (cdr $premises-set))
      else pres))

(defun factorible (one pre &aux l1)
  (if (and (equal (cadr one) (cadr pre))
	   (setq l1 (unifiers (car one) (car pre))))
      then (car l1)))

(defun trace-factor (eqn one two)
  (if (> $trace_flag 1) then  
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
