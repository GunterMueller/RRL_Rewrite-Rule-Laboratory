;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.
#-lispm (include datamacs.l)

(declare (special $induc-terms))
(setq $try t $first-induc-op nil)

; The data structure of pattern is: <lhs ctx rec-calls>

;;; Obtain COVER_SET from the definition equations.

(defun get-cover-sets ()
  ; Return a list of the cover sets for each arguments of f.
  ; The data structure of a cover-set is in form of:
  ;      (f mode . patterns)
  (loop with cset for op in $operlist
	if (not (or (cover-of op)
		    (memq op $free-constructors)
		    (memq op $bool-ops)
		    (null (setq cset (cover-sets op)))))
	  do (push (cons op cset) $cover-sets)))

(defun cover-sets (op &aux rules patterns)
  ; The data structure of patterns is:
  ;      (<lhs ctx rec-calls> ... <lhs ctx rec-calls>) 
  ; Returns the cover sets of op: (mode . patterns) if "op" has been defined.
  (setq rules (loop for xa in (rules-with-op op $op_rules)
		    if (eq (car (rule-source xa)) 'def) collect xa)
	patterns (loop for xa in rules
		       collect (set-right-hypo-args 
				 (lhs xa) (ctx xa)
				 (rem-dups (subs-of-same-root op (rhs xa))))))

  ; an operator is a cross-operator if in its definition rules,
  ; one variable disappears in a rhs.
  ;(if (and (not (memq op $cross-ops)) (is-cross-op rules)) then (push op $cross-ops))

  (if patterns then 
      (add-defin-depend op rules)
      (cons (decide-defin-mode op patterns) patterns)))

(defun set-right-hypo-args (lhs ctx hypos &aux var-posi)
  ; Let the root symbol of lhs is "f". 
  ; hypos is a list of terms rooted by "f".
  ; If "f" is commutative, then permute eventually the arguments of hypos such that
  ; a variable of lhs appears at the same position in hypos.
  ; return (lhs ctx . hypos)
  (if (ac-c-root lhs) then
      (setq var-posi (loop for arg in (args-of lhs) for n from 1
			   if (variablep arg) collect (cons arg n))
	    hypos (loop for term in hypos collect
			(if (loop for arg in (args-of term) for n from 1
				  always (or (nonvarp arg)
					     (and (assoc arg var-posi)
						  (eq (cdr (assoc arg var-posi)) n))))
			    then term
			    else (make-term (op-of term) (reverse (args-of term)))))))
  (cons lhs (cons ctx hypos)))

(defun is-cross-op (rules)
  ; an operator is a cross-operator if in its definition rules,
  ; there are more than two variables in lhs but rhs is a single variable.
  (loop for rule in rules 
	as lhs = (lhs rule)
	thereis (and (loop for op in (all-ops lhs)
			   thereis (and (not (eq op (op-of lhs)))
					(not (memq op $constructors))))
		     (< (length (all-vars (rhs rule)))
			(length (all-vars lhs))))))

(defun decide-defin-mode (op patterns &aux mode)
  ; Returns the mode of "op", which is the location of defined positions.
  ; Initializing ...
  (setq mode (loop for xa from 1 to (get-arity op) collect nil))

  ; Looking for defining positions.
  (loop for pat in patterns do
    (setq mode
	  (loop with nonlinearvars = (non-linear-vars (first pat))
		for res in mode
		for arg in (args-of (first pat))
		collect (if (nonvarp arg) then 'd
			    elseif res then res
			    elseif (memq arg nonlinearvars) then 'c))))
  
  ; Looking for changed positions.
  (loop for pat in patterns do
    (if (cddr pat) then
	(loop with lhsarg = (args-of (first pat))
	      for rec in (cddr pat) do
	  (setq mode (loop for mod in mode 
			   for x1 in lhsarg
			   for x2 in (args-of rec) 
			   collect (if mod then mod 
				       elseif (eq x1 x2) then nil
				       else 'c))))))
  mode)

(defun subs-of-same-root (op term &aux res)
  ; return all subterms of "term" of which the root is "op".
  (if (nonvarp term) then
    (setq res (loop for xa in (args-of term) nconc (subs-of-same-root op xa))) 
    (if (eq op (op-of term)) then (cons term res) else res)))

(defun add-defin-depend (op rules)
  ; adding the definition dependency.
  (setq	rules (loop for op2 in (rem-dups (mapcan 'ops-of-rule rules))
			     if (cover-of op2) collect op2)
	rules (delq op rules))
  (if rules then (push (cons op rules) $defin-depend)))


;;; Following functions provide a set of heuristics that can choose
;;; automatically an induction scheme for proving an equation.

(defun choose-best-schemes (eqn &optional avoid-op &aux score-subs induc-term)
  ; Return a cons of (var1 ... vark) and
  ;      ((term1, ..., termk) condition (term1, ..., termk)...)s)
  (setq score-subs (induc-subs-of-eqn eqn)
	induc-term (loop with res for s-sub in score-subs		 
			 if (and (neq avoid-op (op-of (car s-sub)))
				 (setq res (inductible s-sub)))
			   collect res))
  (if (null induc-term) then nil
      elseif (null (cdr induc-term))
      then (if (> (cdar induc-term) 0) then (form-conjectures (ncons (caar induc-term))))
      else (setq induc-term (parti-by-vars induc-term))
           (form-conjectures (choose-max-score induc-term))))

(defun induc-subs-of-eqn (eqn &aux ops)
  (setq eqn (append (induc-subs-term (lhs eqn))
		    (induc-subs-term (rhs eqn))
		    (loop for xa in (cdr (ctx eqn))
			  nconc (induc-subs-term (car xa))))
	ops (rem-dups (mapcar 'car eqn))
	ops (set-depend-scores ops))

  ; adding to each term a score depending the dependency and the arity of the 
  ; root operators.
  (loop for term in eqn
	as op = (op-of term)
	collect (cons term
		      ;(+ (times 5 (get-arity op))
		      (+ (times 5 (defining-positions op)) 
			 (position op $operlist)
			 (times 10 (cdr (assoc op ops)))))))

(defun induc-subs-term (term &aux result)
  ; a term can be an inductive term if 
  ; (i) there are some definitions for the rooted fucntion symbol.
  ; (ii) one of subterm is a variable
  (if (null term) then nil
   elseif (variablep term) then nil
   elseif (not (cover-of (op-of term)))
   then (mapcan 'induc-subs-term (args-of term))
   elseif (loop for arg in (args-of term) thereis (variablep arg))
   then (setq result (mapcan 'induc-subs-term (args-of term)))
        (if (ac-c-root term) 
	    then (append (induc-ac-subs (op-of term) (args-of term)) result)
	    else (cons term result))
   else (mapcan 'induc-subs-term (args-of term))))

(defun induc-ac-subs (op args)
  ; return a list of terms of which the arguments are exactly two and are taken
  ; from args and at least one of them is a variable.
  (if (or (memq op $commutative) (eq (length args) 2))
      then (list (make-term op args) 
		 (make-term op (reverse args)))
      elseif (cdr args) then
      (loop with result with first = (car args)
	    for second in (cdr args) 
	    if (or (variablep first) (variablep second))
	      do (push (list op first second) result)
		 (push (list op second first) result)
	    finally (return (append result (induc-ac-subs op (cdr args)))))))

;; Choose the best candidate.

(defun inductible (term-score)
  ; Decide whether term is an inductible term.
  ; Return (term . score) if term is inductible.
  ; Suppose 1, ..., n are all the defining positions of f.
  ; A term t = f(t1, t2, .., tn) is inductible iff
  ;      1. t1, t2, ..., tn are all variables
  ;   or 2. for all lhs of the definition rules of "f",
  ;          2.1. lhs matches t;
  ;       or 2.2. every non-variable ti corresponds a variable of lhs;
  ;       or 2.3. ti coresponds an inconsistent argument of lhs;
  ;       or 2.4. ti is a constant (not always sound !!!!)
  ;   or 3. n = 2 and f is commutative and t1 or t2 is a variable.
  (let ((cover (cdr (cover-of (op-of (car term-score)))))
	(term (car term-score))
	(score (cdr term-score)))
     (if (has-inductive-var (args-of term) (first cover)) then
	 (if (not (ac-c-root term)) then
	     (loop for arg in (args-of term)
		   for mo in (first cover)
		   for n from 1 do
	       (if (and (eq mo 'd) 
			(nonvarp arg) 
			(not (is-constant-term arg))
			(not (compatible-pattern term arg (cdr cover) n)))
		   then (return (setq score -500)))))
	 (cons term score))))

(defun has-inductive-var (args mode)
  ; Return t iff there is an inductive variable in args.
  ; A variable x is said to be an inductive variable if there is
  ; a term "f(.., x, ...)" and x is at the defining position of "f"
  (loop for arg in args	
	for mod in mode
	thereis (and (eq mod 'd) (variablep arg))))

(defun get-induc-vars (term &aux mode)
  (setq mode (second (cover-of (op-of term))))
  (loop for xa in (args-of term)
	for mo in mode
	if (and (variablep xa) (eq mo 'd)) collect xa))

(defun get-scheme-vars (term)
  (loop for xa in (args-of term)
	for mo in (second (cover-of (op-of term)))
	if (and mo (variablep xa)) collect xa))

;;; 

(defun choose-max-score (mterms-sets)
  ; Computing first represents for each multi-term set.
  ; then choose the max score represents,
  ; i.e. a set of terms.
  (setq mterms-sets (loop for mterms in mterms-sets
			  collect (choose-least-cover mterms)))
  (if (cdr mterms-sets) then 
      (loop with result with max = 0
	    for num-terms in mterms-sets do
		(if (eq max (car num-terms))
		    then (push (cdr num-terms) result)
		    elseif (lessp max (car num-terms))
		    then (setq result (ncons (cdr num-terms))
			       max (car num-terms)))
		finally (return (choose-off-close result)))
      elseif (lessp 0 (caar mterms-sets))
      then (cdar mterms-sets)))

(defun choose-off-close (terms-list)
  ; terms-list a list of lists of terms.
  ; Choose one list such that the inductive variables have less appearence
  ; in the whole equation.
  (if (cdr terms-list) then 
      (car terms-list)
      else (car terms-list)))

(defun choose-least-cover (mterms &aux var-terms result)
  ; input: a mult-set of terms.
  ; return a score cons to a list of terms.
  (if (cdr mterms) then

      (loop with op = (pick-max-score-op mterms)
	    with return-op = (get-recursive-return-op op)
	    for mt in mterms do
	(if (eq (op-of (car mt)) op) 
	    then (push mt result)
	    elseif (and return-op (< (cdr mt) 0) (encourage op return-op (car mt)))
	    then (setf (cdr mt) (minus (cdr mt)))))

;      (setq result (pick-max-score-op mterms)
;	    result (same-op-mterms result mterms))

      (if (cdr result) then
	  ; sort result by the number of variables in decreasing order.
	  (setq var-terms (loop for mterm in result
				collect (cons (get-scheme-vars (car mterm)) mterm))
		var-terms (sort var-terms 'car-length-cddr)
		result nil)
	  
	  ; choose the minimal set of terms such that all variables
	  ; are contained in that set.
	  (loop with vars for varterm in var-terms do
	    (if (not (is-subset (car varterm) vars)) then
		(push (cdr varterm) result)
		(setq vars (nconc vars (car varterm))))
		finally (return (cons (add-positive (average result) (average mterms))
				      (mapcar 'car (decide-merge-conj result)))))
	  else 
	  (list (add-positive (cdar result) (average mterms)) (caar result)))
      else (list (cdar mterms) (caar mterms))))

(defun pick-max-score-op (mterms &aux terms)
  ; return the operator that has the maximal score.
  ; at first, pick out all terms that have the maximal scores.
  (loop with max = -1000
	for xa in mterms do
    (if (< max (cdr xa)) then 
	(setq terms (ncons (car xa))
	      max (cdr xa))
	elseif (eq max (cdr xa))
	then (push (car xa) terms)))

  ; then choose the root operator of the terms that appear most times.
  (if (cdr terms) then
      (setq terms (mult-form (mapcar 'car terms)))
      (loop with max = (cons nil 0)
	    for op in terms 
	    if (> (cdr op) (cdr max)) do (setq max op)
	    finally (return (car max)))
      else
      (op-of (car terms))))

(defun encourage (op return-op term &aux recur-term)
  ; return t iff "term" has a subterm rooted by "op" and
  ; "op"'s recursive definition is "f", which is needed by "term"
  ; to be an induction term.
  (if (and (setq recur-term (get-recursive-def-term (op-of term)))
	   (is-linear recur-term)) then
      (loop for arg in (args-of term)
	    for arg2 in (args-of recur-term)
	    thereis (and (nonvarp arg) 
			 (nonvarp arg2)
			 (eq (op-of arg) op)
			 (eq (op-of arg2) return-op)))))

(defun get-recursive-def-term (op &aux l1)
  ; return an operator which is the root of rhs of the recursive definition of "op".
  (if (setq l1 (assoc op $cover-sets)) then
      (loop for tup in (cdr l1) if (cddr tup) return (car tup))))

(defun get-recursive-return-op (op &aux l1)
  ; return an operator which is the root of rhs of the recursive definition of "op".
  (if (setq l1 (get-recursive-def-term op)) then
      (loop for rule in (rules-with-op op $op_rules)
	    if (equal l1 (lhs rule))
	      return (if (nonvarp (rhs rule)) then (op-of (rhs rule))))))

;(defun same-op-mterms (op mterms)
;  ; return the terms that have op as root.
;  (loop for xa in mterms if (eq (op-of (car xa)) op) collect xa))

(defun add-positive (n1 n2) 
  (if (< n1 1) then n1 
      elseif (< (+ n1 n2) 5) then 5 
      else (+ n1 n2)))

(defun car-length-great (x y) (> (length (car x)) (length (car y))))

(defun car-length-cddr (x y) 
   (let ((l1 (length (car x))) (l2 (length (car y))))
     (if (eq l1 l2) then (lessp (cddr y) (cddr x)) else (lessp l2 l1))))

(defun average (ms) (quotient (apply '+ (mapcar 'cdr ms)) (length ms)))

(defun compatible-pattern (term arg cover n)
  ; check if n-th "arg" of a term is good for induction.
  (loop for p in cover 
	as lhs = (car p)
	as lhs-arg = (nth n lhs)
	always (or (variablep lhs-arg) 
		   (if (and (not (is-free-constructor (op-of lhs-arg)))
			    (non-linear-vars lhs))
		       then (applies lhs term)
		       else (applies lhs-arg arg))
		   (not (consistent-pair (list arg lhs-arg) t)))))

(defun set-depend-scores (ops)
  ; ops is a list of operators.
  ; return an assoc list of operators and scores.
  (setq ops (loop for op in ops collect (cons (position op $operlist) op))
	ops (sort ops 'car-lessp)
	ops (mapcar 'cdr ops))
  (loop for xa on ops collect (cons (car xa)
				    (- 10 (max-depend-gap (car xa) (cdr xa))))))

(defun defining-positions (op)
  (loop with num = 0 
	for xa in (second (assoc op $cover-sets))
	if xa do (setq num (add1 num))
	finally (return num)))

(defun car-lessp (s1 s2) (lessp (car s1) (car s2)))

(defun max-depend-gap (op ops)
  ; return the maximal gap between op and one of operators in ops.
  (loop with max = 0
	for op2 in ops 
	if (and (setq op2 (depended-op op2 op))
		(> op2 max))
	  do (setq max op2)
	finally (return max)))

(defun add-old-vars (vars posi tuple)
  (loop with vn for va in vars collect
	(if (setq vn (assoc va posi))
       		then (nth (cdr vn) tuple)
		else va)))

(defun ops-of-rule (rule)
  (append (all-ops (lhs rule)) (all-ops (rhs rule))
	  (if (ctx rule) (loop for pre in (cdr (ctx rule))
			       append (all-ops (car pre))))))  
  
(defun depended-op (op1 op2)
  ; return the gap of op1 and op2 in $defin-depend.
  ; nil if no relation in $defin-depend.
  (if (memq op2 (cdr (assoc op1 $defin-depend))) then 1
      else
      (loop for xa in (cdr (assoc op1 $defin-depend))
	    if (setq xa (depended-op xa op2))
	      return (add1 xa)
	    finally (return nil))))

;;; 

(defun parti-by-vars (term-scores)
  ; partition terms by common inductive variables in them.
  (setq term-scores (merge-duplicate term-scores)
	term-scores (loop for mterm in term-scores
			  collect (list (get-induc-vars (car mterm)) mterm))
	term-scores (sort term-scores 'car-length-great))
  (loop with result = (ncons (car term-scores))
	for mterm in (cdr term-scores) 
	as vars2 = (car mterm) do
    (loop for mterms in result do
      (if (have-common (car mterms) vars2) then
	  (rplaca mterms (union (car mterms) (car mterm)))
	  (nconc mterms (cdr mterm))
	  (return nil))
	  finally (push-end mterm result))
	finally (return (mapcar 'cdr result))))


(defun merge-duplicate (term-scores)
  ; if two terms are equal, then adding the half of the minimal score
  ; to the maximal score.
  (setq term-scores (sort term-scores 'cdr-great))
  (loop with result = (ncons (car term-scores))
	for term in (cdr term-scores) do
    (loop for term2 in result do
      (if (equal (car term) (car term2)) then
	  (rplacd term (+ (cdr term2) (quotient (cdr term) 2)))
	  (return))
      finally (push term result))
    finally (return result)))

(defun cdr-great (s1 s2) (> (cdr s1) (cdr s2)))

(defun decide-merge-conj (term-scores &aux highest)
  ; "term-scores" is a list of terms which has common variables.
  ; decide which terms can be chosen as induction schema.
  (if (cdr term-scores) then
      (setq highest (choose-highest-term term-scores)
	    term-scores (delete highest term-scores 1))
      (loop with res for xa in term-scores 
	    if (mergeble-terms (car xa) (car highest))
	      do (push xa res)
	    finally (return (cons highest res)))
      else
      term-scores))

(defun choose-highest-term (mterms)
  ; Choose the term with the highest score.
  (loop with result = (car mterms)
	for xa in (cdr mterms) do
	  (if (> (cdr xa) (cdr result))
	      then (setq result xa))
	finally (return result)))

(defun mergeble-terms (term1 term2 &aux var p1 p2)
  ; two terms are mergeble in one induction if
  ;   1. they have the same root symbol;
  ;   2. they have only one common variable;
  ;   3. the arguments corresponding to that variable in the 
  ;      recursive defintion of the root symbol are simliar terms.
  (if (same-op term1 term2) then
      (setq var (intersection (get-induc-vars term1) 
			      (get-induc-vars term2)))
      (if (eq (length var) 1) then
	  (setq var (car var)
		p1 (get-position var term1)
		p2 (get-position var term2))
	  (if (eq p1 p2) then t else
	      (loop for pat in (cddr (cover-of (op-of term1)))
		    always (or (null (cddr pat))
			       (similar-term (nth p1 (car pat))
					    (nth p2 (car pat)))))))))
	      