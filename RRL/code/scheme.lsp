;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

(in-package "USER")

;;; The data structure of pattern is: <lhs ctx rec-calls>

(defun get-cover-sets ()
  ; Return a list of the cover sets for each arguments of f.
  ; The data structure of a cover-set is in form of:
  ;      (f mode . patterns)
  (sloop with cset for op in $operlist
	if (not (or 
		    ;(cover-of op)
		    (memq op $free-constructors)
		    (memq op $bool-ops)
		    (query-insert op $complete-ops) 
		    ;; $complete-ops contains ops which are tested, 
		    ;; but not necessarily complete.
		    (null (setq cset (cover-sets op)))
		    (is-partial-op op)
		    ))
	do (push (cons op cset) $cover-sets)))

(defun cover-sets (op &aux rules patterns)
  ; The data structure of patterns is:
  ;      (<lhs ctx rec-calls> ... <lhs ctx rec-calls>) 
  ; Returns the cover sets of op: (mode . patterns) if "op" has been defined.
  (setq rules (sloop for xa in (rules-with-op op $op_rules)
		    if (eq (car (rule-source xa)) 'def) collect xa)
	patterns (sloop for xa in rules
		       collect
		       (set-right-hypo-args 
			(lhs xa) (ctx xa)
			(rem-dups 
			 (nconc (subs-of-same-root op (rhs xa))
				(sloop for xb in (cdr (ctx xa))
				      nconc 
				      (subs-of-same-root op (car xb))))))))
  (if* patterns then 
      (add-defin-depend op rules)
      (cons (decide-defin-mode op patterns) patterns)))

(defun set-right-hypo-args (lhs ctx hypos &aux var-posi)
  ; Let the root symbol of lhs is "f". 
  ; hypos is a list of terms rooted by "f".
  ; If "f" is commutative, then permute eventually the arguments of hypos such that
  ; a variable of lhs appears at the same position in hypos.
  ; return (lhs ctx . hypos)
  (if* (ac-c-root lhs) then
      (setq var-posi (sloop for arg in (args-of lhs) for n from 1
			   if (variablep arg) collect (cons arg n))
	    hypos (sloop for term in hypos collect
			(if* (sloop for arg in (args-of term) for n from 1
				  always (or (nonvarp arg)
					     (and (assoc arg var-posi)
						  (eq (cdr (assoc arg var-posi)) n))))
			    then term
			    else (make-term (op-of term) (reverse (args-of term)))))))
  (cons lhs (cons ctx hypos)))

(defun is-cross-op (rules)
  ; an operator is a cross-operator if in its definition rules,
  ; there are more than two variables in lhs but rhs is a single variable.
  (sloop for rule in rules 
	as lhs = (lhs rule)
	thereis (and (sloop for op in (all-ops lhs)
			   thereis (and (not (eq op (op-of lhs)))
					(not (memq op $constructors))))
		     (< (length (all-vars (rhs rule)))
			(length (all-vars lhs))))))

(defun decide-defin-mode (op patterns &aux mode)
  ; Returns the mode of "op", which is the location of defined positions.
  ; Initializing ...
  (setq mode (sloop for xa from 1 to (get-arity op) collect nil))

  ; Looking for defining positions.
  (sloop for pat in patterns do
    (setq mode
	  (sloop with nonlinearvars = (non-linear-vars (first pat))
		for res in mode
		for arg in (args-of (first pat))
		collect (if* (nonvarp arg) then 'd
			    elseif res then res
			    elseif (memq arg nonlinearvars) then 'c))))
  
  ; Looking for changed positions.
  (sloop for pat in patterns do
    (if* (cddr pat) then
	(sloop with lhsarg = (args-of (first pat))
	      for rec in (cddr pat) do
	  (setq mode (sloop for mod in mode 
			   for x1 in lhsarg
			   for x2 in (args-of rec) 
			   collect (if* mod then mod 
				       elseif (eq x1 x2) then nil
				       else 'c))))))
  mode)

(defun subs-of-same-root (op term &aux res)
  ; return all subterms of "term" of which the root is "op".
  (if* (nonvarp term) then
    (setq res (sloop for xa in (args-of term) nconc (subs-of-same-root op xa))) 
    (if* (eq op (op-of term)) then (cons term res) else res)))

(defun add-defin-depend (op rules)
  ; adding the definition dependency.
  (setq	rules (sloop for op2 in (rem-dups (mapcan 'ops-of-rule rules))
			     if (cover-of op2) collect op2)
	rules (delete0 op rules))
  (if* rules then (push (cons op rules) $defin-depend)))


;;; Following functions provide a set of heuristics that can choose
;;; automatically an induction scheme for proving an equation.

(defun choose-best-schemes (eqn &optional avoid-terms &aux score-subs induc-term)
  ; Return a cons of (var1 ... vark) and
  ;      ((term1, ..., termk) condition (term1, ..., termk)...)s)
  (setq score-subs (induc-subs-of-eqn eqn)
	induc-term (sloop with res for s-sub in score-subs		 
			 if (and (not (member0 (car s-sub) avoid-terms))
				 (setq res (inductible s-sub)))
			 collect res))
  (if* (null induc-term) then nil
      elseif (null (cdr induc-term))
      then (if* (> (cdar induc-term) 0) then (make-one-scheme (ncons (caar induc-term))))
      else (setq induc-term (parti-by-vars induc-term))
           (make-one-scheme (choose-max-score induc-term))))

(defun induc-subs-of-eqn (eqn &aux ops)
  (setq eqn (append (induc-subs-term (lhs eqn))
		    (induc-subs-term (rhs eqn))
		    (sloop for xa in (cdr (ctx eqn))
			  nconc (induc-subs-term (car xa))))
	ops (rem-dups (mapcar 'car eqn))
	ops (set-depend-scores ops))

  ; adding to each term a score depending the dependency and the arity of the 
  ; root operators.
  (sloop for term in eqn
	as op = (op-of term)
	collect (cons term
		      (quotient 
		       (+ (times 5 (defining-positions op)) 
			  (op-position op $operlist)
			  (times 10 (cdr (assoc op ops))))
		       (if* (ac-c-root term) 2 1))))) ;; 2 HZ: 8/5/91

(defun induc-subs-term (term &aux result)
  ; a term can be an inductive term if 
  ; (i) there are some definitions for the rooted fucntion symbol.
  ; (ii) one of subterm is a variable
  (if* (null term) then nil
   elseif (variablep term) then nil
   elseif (not (cover-of (op-of term)))
   then (mapcan 'induc-subs-term (args-of term))
   elseif (sloop for arg in (args-of term) thereis (variablep arg))
   then (setq result (mapcan 'induc-subs-term (args-of term)))
        (if* (ac-c-root term) 
	    then (append (induc-ac-subs (op-of term) (args-of term)) result)
	    else (cons term result))
   else (mapcan 'induc-subs-term (args-of term))))

(defun induc-ac-subs (op args)
  ; return a list of terms of which the arguments are exactly two and are taken
  ; from args and at least one of them is a variable.
  (if* (or (memq op $commutative) (= (length args) 2))
      then (list (make-term op args) 
		 (make-term op (reverse args)))
      elseif (cdr args) then
      (sloop with result with first = (car args)
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
     (if* (has-inductive-var (args-of term) (first cover)) then
	 (if* (not (ac-c-root term)) then
	     (sloop for arg in (args-of term)
		   for mo in (first cover)
		   for n from 1 do
	       (if* (and (eq mo 'd) 
			(nonvarp arg) 
			(not (is-constant-term arg))
;			(not (compatible-pattern term arg (cdr cover) n))
			)
		   then (return (setq score -100))))) ;; -500 ------ HZ 8/5/91.
	 (cons term score))))

(defun has-inductive-var (args mode)
  (sloop for arg in args	
	for mod in mode
	thereis (and (eq mod 'd) (variablep arg))))

(defun have-inductive-vars (args mode)
  ; Return t iff whenever there is a definiting position in mode,
  ; there is a variable in args.
  ; A variable x is said to be an inductive variable if there is
  ; a term "f(.., x, ...)" and x is at the defining position of "f"
  (sloop for arg in args	
	for mod in mode
	always (or (null mod) (variablep arg) (is-value-term arg))))

(defun eligible-induc-terms (terms)
  (let ((cover (cdr (cover-of (op-of (car terms))))))
    (when cover
	  (setq terms (sloop for term in terms 
			     if (have-inductive-vars (args-of term) (first cover))
			     collect term))
	  (if (not $multi-term-induc) (setf terms (last terms)))
	  terms)))

(defun get-induc-vars (term &aux mode)
  (setq mode (second (cover-of (op-of term))))
  (sloop for xa in (args-of term)
	for mo in mode
	if (and (variablep xa) (eq mo 'd)) collect xa))

(defun get-scheme-vars (term)
  (sloop for xa in (args-of term)
	for mo in (second (cover-of (op-of term)))
	if (and mo (variablep xa)) collect xa))

;;; 

(defun choose-max-score (mterms-sets)
  ; Computing first represents for each multi-term set.
  ; then choose the max score represents,
  ; i.e. a set of terms.
  (setq mterms-sets (sloop for mterms in mterms-sets
			  collect (choose-least-cover mterms)))
  (if* (cdr mterms-sets) then 
      (sloop with result with max = 0
	    for num-terms in mterms-sets do
		(if* (= max (car num-terms))
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
  (if* (cdr terms-list) then 
      (car terms-list)
      else (car terms-list)))

(defun choose-least-cover (mterms &aux var-terms result)
  ; input: a mult-set of terms.
  ; return a score cons to a list of terms.
  (if* (cdr mterms) then

      (sloop with op = (pick-max-score-op mterms)
	    with return-op = (get-recursive-return-op op)
	    for mt in mterms do
	(if* (eq (op-of (car mt)) op) 
	    then (push mt result)
	    elseif (and return-op (< (cdr mt) 0) (encourage op return-op (car mt)))
	    then (setf (cdr mt) (minus (cdr mt)))))

;      (setq result (pick-max-score-op mterms)
;	    result (same-op-mterms result mterms))

      (if* (cdr result) then
	  ; sort result by the number of variables in decreasing order.
	  (setq var-terms (sloop for mterm in result
				collect (cons (get-scheme-vars (car mterm)) mterm))
		var-terms (sort var-terms 'car-length-cddr)
		result nil)
	  
	  ; choose the minimal set of terms such that all variables
	  ; are contained in that set.
	  (sloop with vars for varterm in var-terms do
	    (if* (not (is-subset (car varterm) vars)) then
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
  (sloop with max = -1000
	for xa in mterms do
    (if* (< max (cdr xa)) then 
	(setq terms (ncons (car xa))
	      max (cdr xa))
	elseif (= max (cdr xa))
	then (push (car xa) terms)))

  ; then choose the root operator of the terms that appear most times.
  (if* (cdr terms) then
      (setq terms (mult-form (mapcar 'car terms)))
      (sloop with max = (cons nil 0)
	    for op in terms 
	    if (> (cdr op) (cdr max)) do (setq max op)
	    finally (return (car max)))
      else
      (op-of (car terms))))

(defun encourage (op return-op term &aux recur-term)
  ; return t iff "term" has a subterm rooted by "op" and
  ; "op"'s recursive definition is "f", which is needed by "term"
  ; to be an induction term.
  (if* (and (setq recur-term (get-recursive-def-term (op-of term)))
	   (is-linear recur-term)) then
      (sloop for arg in (args-of term)
	    for arg2 in (args-of recur-term)
	    thereis (and (nonvarp arg) 
			 (nonvarp arg2)
			 (eq (op-of arg) op)
			 (eq (op-of arg2) return-op)))))

(defun get-recursive-def-term (op &aux l1)
  (if (setq l1 (assoc op $cover-sets)) 
      (sloop for tup in (cddr l1) if (cddr tup) return (car tup))))

(defun have-many-recursive-eqns (op &aux l1 first)
  (if (setq l1 (assoc op $cover-sets)) 
      (sloop for tup in (cddr l1) if (cddr tup) do
	     (if first (return t) (setq first t)))))

(defun get-recursive-return-op (op &aux l1)
  ; return an operator which is the root of rhs of the recursive definition of "op".
  (if* (setq l1 (get-recursive-def-term op)) then
      (sloop for rule in (rules-with-op op $op_rules)
	    if (equal l1 (lhs rule))
	      return (if* (nonvarp (rhs rule)) then (op-of (rhs rule))))))

;(defun same-op-mterms (op mterms)
;  ; return the terms that have op as root.
;  (sloop for xa in mterms if (eq (op-of (car xa)) op) collect xa))

(defun add-positive (n1 n2) 
  (if* (< n1 1) then n1 
      elseif (< (+ n1 n2) 5) then 5 
      else (+ n1 n2)))

(defun car-length-great (x y) (> (length (car x)) (length (car y))))

(defun car-length-cddr (x y) 
   (let ((l1 (length (car x))) (l2 (length (car y))))
     (if* (= l1 l2) then (lessp (cddr y) (cddr x)) else (lessp l2 l1))))

(defun average (ms) (quotient (apply '+ (mapcar 'cdr ms)) (length ms)))

(defun compatible-pattern (term arg cover n)
  ; check if n-th "arg" of a term is good for induction.
  (sloop for p in cover 
	as lhs = (car p)
	as lhs-arg = (nth n lhs)
	always (or (variablep lhs-arg) 
		   (if* (and (not (is-free-constructor (op-of lhs-arg)))
			    (non-linear-vars lhs))
		       then (applies lhs term)
		       else (applies lhs-arg arg))
		   (not (consistent-pair arg lhs-arg t)))))

(defun set-depend-scores (ops)
  ; ops is a list of operators.
  ; return an assoc list of operators and scores.
  (setq ops (sloop for op in ops collect (cons (op-position op $operlist) op))
	ops (sort ops 'car-lessp)
	ops (mapcar 'cdr ops))
  (sloop for xa on ops collect (cons (car xa)
				    (- 10 (max-depend-gap (car xa) (cdr xa))))))

(defun defining-positions (op)
  (sloop with num = 0 
	for xa in (second (assoc op $cover-sets))
	if xa do (setq num (1+ num))
	finally (return num)))

(defun car-lessp (s1 s2) (lessp (car s1) (car s2)))

(defun max-depend-gap (op ops)
  ; return the maximal gap between op and one of operators in ops.
  (sloop with max = 0
	for op2 in ops 
	if (and (setq op2 (depended-op op2 op))
		(> op2 max))
	  do (setq max op2)
	finally (return max)))

(defun add-old-vars (vars posi tuple)
  (sloop with vn for va in vars collect
	(if* (setq vn (assoc va posi))
       		then (nth (cdr vn) tuple)
		else va)))

(defun ops-of-rule (rule)
  (append (all-ops (lhs rule)) (all-ops (rhs rule))
	  (if* (ctx rule) (sloop for pre in (cdr (ctx rule))
			       append (all-ops (car pre))))))  
  
(defun depended-op (op1 op2)
  ; return the gap of op1 and op2 in $defin-depend.
  ; nil if no relation in $defin-depend.
  (if* (memq op2 (cdr (assoc op1 $defin-depend))) then 1
      else
      (sloop for xa in (cdr (assoc op1 $defin-depend))
	    if (setq xa (depended-op xa op2))
	      return (1+ xa)
	    finally (return nil))))

;;; 

(defun parti-by-vars (term-scores)
  ; partition terms by common inductive variables in them.
  (setq term-scores (merge-duplicate term-scores)
	term-scores (sloop for mterm in term-scores
			  collect (list (get-induc-vars (car mterm)) mterm))
	term-scores (sort term-scores 'car-length-great))
  (sloop with result = (ncons (car term-scores))
	for mterm in (cdr term-scores) 
	as vars2 = (car mterm) do
    (sloop for mterms in result do
      (if* (have-common (car mterms) vars2) then
	  (rplaca mterms (union (car mterms) (car mterm)))
	  (nconc mterms (cdr mterm))
	  (return nil))
	  finally (push-end mterm result))
	finally (return (mapcar 'cdr result))))


(defun merge-duplicate (term-scores)
  ; if two terms are equal, then adding the half of the minimal score
  ; to the maximal score.
  (setq term-scores (sort term-scores 'cdr-great))
  (sloop with result = (ncons (car term-scores))
	for term in (cdr term-scores) do
    (sloop for term2 in result do
      (if* (equal (car term) (car term2)) then
	  (rplacd term (+ (cdr term2) (quotient (cdr term) 2)))
	  (return))
      finally (push term result))
    finally (return result)))

(defun cdr-great (s1 s2) (> (cdr s1) (cdr s2)))

(defun decide-merge-conj (term-scores &aux highest)
  ; "term-scores" is a list of terms which has common variables.
  ; decide which terms can be chosen as induction schema.
  (if* (cdr term-scores) then
      (setq highest (choose-highest-term term-scores)
	    term-scores (delete0 highest term-scores 1))
      (sloop with res for xa in term-scores 
	    if (mergeble-terms (car xa) (car highest))
	      do (push xa res)
	    finally (return (cons highest res)))
      else
      term-scores))

(defun choose-highest-term (mterms)
  ; Choose the term with the highest score.
  (sloop with result = (car mterms)
	for xa in (cdr mterms) do
	  (if* (> (cdr xa) (cdr result))
	      then (setq result xa))
	finally (return result)))

(defun mergeble-terms (term1 term2 &aux var p1 p2)
  ; two terms are mergeble in one induction if
  ;   1. they have the same root symbol;
  ;   2. they have only one common variable;
  ;   3. the arguments corresponding to that variable in the 
  ;      recursive defintion of the root symbol are simliar terms.
  (if* (same-op term1 term2) then
      (setq var (intersection (get-induc-vars term1) 
			      (get-induc-vars term2)))
      (if* (= (length var) 1) then
	  (setq var (car var)
		p1 (get-position var term1)
		p2 (get-position var term2))
	  (if* (equal p1 p2) then t else
	      (sloop for pat in (cddr (cover-of (op-of term1)))
		    always (or (null (cddr pat))
			       (similar-term (nth p1 (car pat))
					    (nth p2 (car pat)))))))))
	      

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The data structure of pattern is: <lhs ctx rec-calls>
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-one-scheme (terms)
  ; Return a cons of (var1 ... vark) and
  ;           ((term1, ..., termk) condition (term1, ..., termk)...)
  (if* (setq terms (eligible-induc-terms terms)) then

    ;; If there are more than one in terms, then check that if
    ;; there is a single recursive equation for the root symbol of "terms".
    (if* (and (cdr terms) (have-many-recursive-eqns (op-of (car terms))))
	(setq terms (ncons (car terms))))

    (setq $induc-terms terms)
    (setq $induc-vars (rem-dups (mapcan #'get-induc-vars terms)))

    (sloop with first = (form-patterns-single (car terms))
	  for term in (cdr terms) do
	  (setq first (add-patterns term first))
	  finally (return first))))

(defun form-patterns-single (term &aux cover l1)
  ; make patterns from the definitions of the root of term.
  (setq	cover (cdr (cover-of (op-of term)))
	l1 (compatible-patterns term (cdr cover))
	l1 (sloop for pat in l1 
		  collect (one-pattern (first cover) (args-of term) pat)))
  (remove-dup-vars (get-scheme-vars term) l1))

(defun compatible-patterns (term patterns)
  ; return a list of patterns that are compatible with "term".
  ; A pattern is compatible with "term" if for each argument y of "term",
  ; either y is a variable, or the correspoding argument in the pattern 
  ; subsums y.
  (sloop with sigma 
	for pt in patterns 
	as pat = (rename-pattern pt)
	if (or (and (setq sigma (applies (car pat) term))
				 (setq pat (applysubst sigma pat)))
	       (sloop for xa in (args-of term)
		     for xb in (args-of (car pat))
		     always (or (and (setq sigma (applies xb xa))
				     (setq pat (applysubst sigma pat)))
				(variablep xa))))
	  collect pat))

(defun one-pattern (mode args pat &aux lhs condi pattern)
  ; return (premises lhs . hypotheses), an internal representation
  ; of a pattern, where lhs is a tuple of terms reserved for each
  ; inductive variables; premises is the condition in the definition
  ; and hypotheses are a list of tuples of terms, of which the terms
  ; in each tuple are reserved for each inductive variables.
  (setq mode (sloop for m in mode
		   for arg in args 
		   collect (and m (variablep arg)))
	; Now a "t" in mode denotes a correspoding inductive variable position.
	lhs (sloop for arg in (args-of (first pat))	
		  for mod in mode if mod collect arg) 
	condi (second pat) 
	pattern (if* (sloop for xa in lhs thereis (listp xa)) then
		  (sloop for term in (cddr pat) 
			collect (sloop for arg in (args-of term)
				      for mod in mode 
				      if mod collect arg))))
  (cons condi (cons lhs pattern)))

(defun has-nonlinear-vars (vars)
  ; return the two positions of a single variable if that variable
  ; occurs more than once in vars.
  (sloop with res for n1 from 0 for va on vars 
        if (setq res (sloop for n2 from (1+ n1) 
			   for vb in (cdr va) 
			   if (eq vb (car va))
			   return (cons n1 n2)
			   finally (return nil)))
	 return res
      finally (return nil)))

(defun remove-dup-vars (vars patterns &aux n1 n2)
  ; If a variable appears in "vars" more than once, then remove one of them
  ; and check if the inductive patterns are compatible.
  (if* (setq n2 (has-nonlinear-vars vars)) then
      (setq n1 (car n2) 
	    n2 (cdr n2)
	    vars (delete0 (nth n1 vars) vars 1)
	    patterns (sloop for pattern in patterns 
			if (setq pattern (rem-dup-vars pattern n1 n2))
			  collect pattern))
      (remove-dup-vars vars patterns)
      else (cons vars patterns)))

(defun rem-dup-vars (pattern n1 n2 &aux condi t1 t2 sigma)
  (setq condi (first pattern))
  (sloop with result for tup in (cdr pattern) do
    (setq t1 (nth n1 tup)
	  t2 (nth n2 tup))
    (if* (setq sigma (applies t1 t2))
	then (setq condi (applysubst sigma condi)
		   tup (delete0 t1 tup 1))
	     (push tup result)
	elseif (setq sigma (applies t2 t1))
	then (setq condi (applysubst sigma condi)
		   tup (delete0 t2 tup 1))
	     (push tup result)
	else (return nil))
    finally (return (cons condi (reverse result)))))

(defun add-patterns (term patterns) 
  (let (result posi stock1 stock2 newpatterns newvars vars tuple)
    ; patterns is (vars . list-of-<condition, tuples>)
    ; return the same data structure as patterns.
    (setq newpatterns (form-patterns-single term)
	  newvars (set-diff (car newpatterns) (car patterns))
	  vars (append (car patterns) newvars))
    (sloop for pattern in (cdr patterns) do
      (if* (cddr pattern)
	  then (setq stock1 pattern) ;; Assume a single recursive equation.
	  else (push (list (car pattern) (append (cadr pattern) newvars)) result)))
    
    (setq posi (sloop for n from 0 
		     for va in (car newpatterns) 
		     collect (cons va n)))

    (sloop for pattern in (cdr newpatterns) do
      (if* (cddr pattern)
	  then (setq stock2 pattern) ;; Assume a single recursive equation.
	  else (setq tuple (add-old-vars vars posi (cadr pattern)))
	       (push (list (first pattern) tuple) result)))

    (if (setq posi (merge-two-patterns stock1 stock2 vars posi))
	(cons vars (remove-subsumed-patterns (cons posi result)))
      patterns)))

(defun merge-two-patterns (stock1 stock2 vars posi	&aux condi tuple sigma)
  ; merge two induction schemes with hypotheses into one.
  (setq sigma (find-merge-sigma (cadr stock1) (cadr stock2) vars posi))
  (if* sigma then 
    (setq stock2 (applysubst sigma stock2)
	  condi (merge-premises (car stock1) (car stock2))
	  tuple (merge-two-tuples (cadr stock1) (cadr stock2) vars posi)
	  stock1 (sloop for xa in (cddr stock1) append
		       (sloop for xb in (cddr stock2) 
			     collect (merge-two-tuples xa xb vars posi))))
    (cons condi (cons tuple (rem-dups stock1)))))

(defun find-merge-sigma (tu1 tu2 vars posi &aux vn2 sigma)
  ;; POSI contains the variables used in tu2.
  ;; VARS contains all the variables.
  ;; Return a sigma iff for any common var used in tu1 and tu2,
  ;; the corresponding terms are matchable.
  (sloop for t1 in tu1
	for var in vars do
	;; If var is used in both tu1 and tu2, then make a sigma out of
	;; the terms in tu1 and tu2 corresponding to var.
	(setq vn2 (assoc var posi))
	(when vn2
	      (setq sigma (match (nth (cdr vn2) tu2) t1 sigma))
	      (if* (null sigma) (return nil))))
  sigma)

(defun merge-two-tuples (tu1 tu2 vars posi &aux t1)
  (sloop for n1 from 0 
	for va in vars collect
	(if* (setq t1 (nth n1 tu1))
	    t1
	  (nth (cdr (assoc va posi)) tu2))))

(defun rename-pattern (pat)
  (if* (car pat)
      then (cdr (newvarsin (cons 'xxx pat)))
      else (newvarsin pat)))

(defun remove-subsumed-patterns (patterns)
  ; remove patterns in "patterns" that is subsumed by others.
  (sloop with result for cs on patterns 
	as xa = (car cs) do
	  (if* (not (sloop for xb in (cdr cs) 
		      thereis (subsumed-tuple xa xb)))
	      then (push xa result))
	  finally (return result)))

(defun subsumed-tuple (con1 con2)
  ; return t iff both "con1" and "con2" do not have hypotheses and
  ; "con1" is an instance of "con2".
  (and (null (cddr con1)) 
       (null (cddr con2))
       (applies (cons 'x (second con2)) (cons 'x (second con1)))))
