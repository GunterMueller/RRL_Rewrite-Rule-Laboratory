(in-package "USER")

(defun reduce-eq-term (term &optional rules &aux res)
  ;; This function first tries to find a rule whose lhs is an eq
  ;; with the same number of arguments as "term".
  ;; If it can use such a rule for rewriting then it will do so.
  ;; Otherwise it looks for a rule wth eq that will rewrite some
  ;; subset of the args of "term" to false in this case it returns false.
  ;; otherwise it returns nil.  
  (setq rules (or rules (rules-with-op *eq* $op-rules)))
  (if* (setq res (reduce-eq-exactly term rules)) then res else
      (sloop with largs = (length term)
	    with desired = nil
	    with rest-args = nil
	    for args = (args-of term)
		     then ; Deleting an arg from "args", 
		(sloop for arg in args 
		      if (not (memq arg rest-args)) 
			return (removen arg args 1)
		      finally (cdr args))
	    while (and (null desired) (cdr args)) ; If more than one args left,
	    do
	(setq $false-rhs nil
	      desired
	      (sloop for rule in rules
		    with sigma
		    with temp
		    if (and (< (length (lhs rule)) largs) (not (falsep (rhs rule))))
		      do
			(if* (setq sigma (match-set (lhs rule) (make-term *eq* args))) 
			    ;; Structure of the value returned by match-set:
			    ;;    (rest-of-args . substitution)
			    then (setq rest-args (car sigma)
				       sigma (cdr sigma)
				       temp (norm-term
					      (flat-applysigma
						sigma (rhs rule))))
			    (if* (falsep temp) then
				 (remember-used-rule-num (ruleno rule))
				 (return temp)))
		    finally (return nil)))
            ; desired is non nil only if it is false.
	    finally (return desired))))

(defun reduce-eq-exactly (term rules)
  ; Returns nil if there doese not exist a rule
  ; whose lhs is of the form: (eq t1, ..., tn)
  ; where n is the length of args and there is a sigma, 
  ; st sigma(lhs) = term. 
  ; if there is such a rule then this returns sigma(rhs).
  (sloop	with largs = (length term)
	with res-subst
	for rule in rules
	as lhs = (lhs rule)
	as llhs = (length lhs)
	when (and (>= largs llhs)
		  (or (setq $false-rhs (falsep (rhs rule)))
		      (eq largs llhs))
		  (setq res-subst (eq-match lhs term))
		  (or (remember-used-rule-num (ruleno rule)) t)
		  )
	return (norm-term (flat-applysigma res-subst (rhs rule)))))

(defun eq-tr (terms)
  ;  Returns term with arguments passed through the eq-find.
  (let (others eqlist)
     (sloop for term in terms do
            (cond ((eq (op-of term) *eq*) (push term eqlist))
                  (t (push term others))))
     (append (if eqlist (eq-find eqlist)) others)))

(defun eq-find (eq-pairs)
  ; Control function for the union find algorithm.
  ; Returns terms with appropriate eq's joined.
  (sloop with eqlists = nil for xa in eq-pairs 
	do (setq eqlists (eq-add (args-of xa) eqlists))
	finally (return (sloop for xa in eqlists collect
		         (cond ((null (cdr xa)) *trueterm*)
	                       (t (make-term *eq* (sort xa 'total-term-ordering))))))))

(defun eq-add (elist eqlists)
  ; Adds a set of equivalent terms to the equivalent classes for the
  ; eq-find algorithm. Returns the new equaivalence classes.
  ; The union function is also used to filter out doubles.
  (cond ((null eqlists) (ncons (rem-dups elist)))
        ((intersection (car eqlists) elist)
         (eq-join (union (car eqlists) elist) elist (cdr eqlists)))
        (t (cons (car eqlists) (eq-add elist (cdr eqlists))))))

(defun eq-join (elist1 elist2 eqlists)
  ; Looks for possible union of equivalence classes do to elist2.
  ; Returns new list of equivalence classes.
  (cond ((null eqlists) (list elist1))
        ((have-common (car eqlists) elist2)
         (eq-join (union (car eqlists) elist1) elist2 (cdr eqlists)))
        (t (cons (car eqlists) (eq-join elist1 elist2 (cdr eqlists))))))

(defun idem-eq-critical (rule l1 ruleno &aux l2)
   ; Computing critical pairs with EQ predicate.
   (sloop while (cdr l1) do
      (setq l2 (pop l1))
      (sloop for xa in l1 do
          (setq xa (unifier l2 xa))
	  (if* xa then
	     (setq $ncritpr (add1 $ncritpr)
  	           xa (applysubst xa (list *xor* *trueterm* (lhs rule) (rhs rule))))
  	     (trace-message 4 "" (trace-crit ruleno xa t))
	     (process-ass-simple (make-flat xa) ruleno)))))

(defun is-inconsi-pair (t1 t2)
   (or (and (variablep t1) (or (variablep t2) (null (args-of t2))))
       (and (variablep t2) (null (args-of t1)))))

(defun consistent-check (eqn)
  ; Check if "eqn" is a consistent equation using Huet and Hullot's 
  ; criteria. If not, prints an error message and throws "*incons*" to 
  ; the catch in "induc-prove".
  (let ((t1 (lhs eqn)) (t2 (rhs eqn)))
    (cond ((variablep t1) 
	   (cond ((variablep t2) (inconsistent-eqn eqn))
		 ((occurs-in t1 t2) (exchange-lr eqn) t)
		 (t (inconsistent-eqn eqn))))
	  ((variablep t2)
	   (if (not (occurs-in t2 t1)) (inconsistent-eqn eqn)))
	  ((truep t1) (if* (falsep t2) then (inconsistent-eqn eqn)))
	  ((falsep t1) (if* (truep t2) then (inconsistent-eqn eqn)))
	  (t t))))

#|
(defun consistent-rule (rule)
  ; Check if "rule" is a consistent equation. If not, prints an error 
  ; message and throws "*incons*" to the catch in "induc-prove".
  (if* (and (not (and (eq (car (rule-source rule)) 'deleted)
		     (memq 'ac-op (rule-source rule))))
	   (is-constructor-term (lhs rule))
	   (caseq $prove-method 
	     (q (not (quasi-reducible (lhs rule))))
	     (s (rule-destroyable (lhs rule)))))
    then
    (terpri $out-port) 
    (if $ac (princ "A possibly " $out-port))
    (princ "Inconsistent Relation derived:" $out-port) (terpri $out-port)
    (princ "   " $out-port) (write-rule rule)
    (setq $used-rule-nums rule)
    (throw 'prove '*incons*)))
|#

(defun consistent-pair (pair &optional var)
  ; Return t if "pair" is a consistent equation.
  (let ((t1 (car pair)) (t2 (cadr pair)))
    (cond ((equal t1 t2) t)
	  ((truep t2) (not (falsep t1)))
	  ((variablep t1) 
	   (if* var 
	       then (or (variablep t2)
			(not (is-free-constructor (op-of t2)))
			(not (is-constructor-term t2))
			(not (is-subterm t1 t2)))
	       elseif (variablep t2) then nil
	       elseif (memq (op-of t2) $free-constructors) 
	       then nil
	       else (is-subterm t1 t2)))
	  ((variablep t2)
	   (if* var 
		then (or (variablep t1)
			 (not (is-free-constructor (op-of t1)))
			 (not (is-constructor-term t1))
			 (not (is-subterm t2 t1)))
		elseif (memq (op-of t1) $free-constructors)
		then nil
		else (is-subterm t2 t1)))
	  ((is-free-constructor (op-of t1))
	   (if* (eq (op-of t1) (op-of t2)) 
		(sloop for xa in (args-of t1) 
		       for xb in (args-of t2) 
		       if (nequal xa xb) 
		       do
		       (return (list xa xb)))
		(not (is-free-constructor (op-of t2)))))
	  (t t))))

#|
(defun consistent-check-testset (eqn)
  ; Check if "eqn" is a consistent equation. If not, prints an error message
  ; and throws "*incons*" to the catch in "induc-prove".
  (let ((t1 (lhs eqn)) (t2 (rhs eqn)))
    (cond ((variablep t1) 
	   (cond ((variablep t2) (inconsistent-eqn eqn))
		 ((occurs-in t1 t2)
		  (if* (destroyable t2 $testset) 
		      then (inconsistent-eqn eqn)))
		 (t (inconsistent-eqn eqn))))
	  ((variablep t2)
	   (if* (occurs-in t2 t1)
	       then (if* (destroyable t1 $testset)
			then (inconsistent-eqn eqn))
	       else (inconsistent-eqn eqn)))
	  (t (setq t1 (destroyable t1 $testset))
	     (if* (and t1 (not (applies t2 t1))) then
		 (if* (destroyable t2 $testset)
		     then (inconsistent-eqn eqn)))))))

(defun consistent-check-quasi (eqn)
  ; Check if "eqn" is a consistent equation. If not, prints an error 
  ; message and throws "*incons*" to the catch in "induc-prove".
  (let ((t1 (lhs eqn)) (t2 (rhs eqn)))
    (cond ((variablep t1) 
	   (cond ((variablep t2) (inconsistent-eqn eqn))
		 ((occurs-in t1 t2)
		  (if* (and (is-constructor-term t2)
			   (not (quasi-reducible t2)))
		      then (inconsistent-eqn eqn)))
		 (t (inconsistent-eqn eqn))))
	  ((variablep t2)
	   (if* (occurs-in t2 t1)
	       then (if* (and (is-constructor-term t1)
			     (not (quasi-reducible t1)))
			then (inconsistent-eqn eqn))
	       else (inconsistent-eqn eqn)))
	  ((truep t1) (if* (falsep t2) (inconsistent-eqn eqn)))
	  ((falsep t1) (if* (truep t2) (inconsistent-eqn eqn)))

	  ((and (is-constructor-term t1)
		(is-constructor-term t2))
	   (if* (lrpo t1 t2)
	       then (if* (not (quasi-reducible t1)) (inconsistent-eqn eqn))
	       elseif (not (quasi-equivalent t1 t2))
	       then (inconsistent-eqn eqn))))))
|#

(defun inconsistent-eqn (rule)
  ; Auxillary function to "consistent-check".
  (setq rule (make-rule rule (incf $nrules) 1000 5))
  (when (neq $out-port poport) 
	(terpri) (princ "A proof has been found.") (terpri))
  (terpri $out-port)
  (if $ac (princ "A Possibly " $out-port))
  (princ "Inconsistent Relation Derived:" $out-port) (terpri $out-port)
  (princ "    " $out-port) (write-rule rule)
  (push-end rule $rule-set)
  (setq $used-rule-nums rule)
  (throw 'refuted '*incons*))

(defun trace-inconsistency (rule &optional (port poport))
  (trace-rule rule port))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Following are brand-new codes.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro cancellation (eqn) `(divisible-check ,eqn))

(defmacro divisible-check2 (t1 t2 avoid unity)
  `(if (or (ac-root ,t1) (comm-root ,t1))
      (divisible-ac-check ,t1 ,t2 ,avoid ,unity)
      (divisible-nonac-check ,t1 ,t2 ,avoid ,unity)))

(defmacro cancel-common-terms ()
  `(let ()
    (setq avoid (second op-term)
	  unity (third op-term))
    (if avoid (setq avoid (ncons avoid)))
    (if unity (setq unity (ncons unity)))
    (while (and (nonvarp t1) 
		(eq (op-of t1) (car op-term))
		(setq pair (divisible-check2 t1 t2 avoid unity)))
      (setq t1 (car pair) t2 (cdr pair) done t))
    ))

(defun divisible-check (eqn &aux (t1 (lhs eqn)) (t2 (rhs eqn))
			    op-term avoid unity done pair)
  ; return a pair if t1 and t2 can be simplified by cancelation rules.
  (when (and (nonvarp t1) (member (op-of t1) $free-constructors)
	     (nonvarp t2) (eq (op-of t1) (op-of t2)))
      (setq eqn (separated eqn))
      (when eqn (setq t1 (lhs eqn) t2 (rhs eqn))))

  (when eqn
	(if (and (nonvarp t1) (setq op-term (assoc (op-of t1) $divisible)))
	    (cancel-common-terms)
	  (when (and (nonvarp t2) (setq op-term (assoc (op-of t2) $divisible)))
		(psetq t1 t2 t2 t1)
		(cancel-common-terms)
		(psetq t1 t2 t2 t1)
		))
	(when done
	      (trace-message 4 "" (trace-divisible t1 t2 eqn))
	      (if (equal t1 t2) 
		  nil
		(change-lhs-rhs eqn t1 t2)))
	 )
  eqn)
	  
(defun divisible-nonac-check (t1 t2 avoid unity &aux op res)
  ; check whether t1 and t2 can be simplified by cancellation law,
  ; where t1 is rooted by a non-ac operator.
  (if* (and unity (avoidable avoid t2)) then
      (if* (equal (left-arg (setq op (op-of t1)) t1) t2) then
	  (setq t1 (remove-left-arg op t1)
		t2 unity)
	  (if* (equal t1 t2)
	      (setq res '(nil))
	    (setq res (cons t1 t2)))
	  elseif (equal (right-arg op t1) t2) then 
	  (setq t1 (remove-right-arg op t1)
		t2 unity)
	  (if* (equal t1 t2)
	      (setq res '(nil))
	    (setq res (cons t1 t2)))))

  (if* res then res 
      elseif (not (and (nonvarp t2) (equal (setq op (op-of t1)) (op-of t2))))
      then nil
      elseif (op-has-rl-status op)
      then (if* (setq res (divisible-right-check op t1 t2 avoid))
	       then res
	       else (divisible-left-check op t1 t2 avoid))
      elseif (setq res (divisible-left-check op t1 t2 avoid))
      then res
      else (divisible-right-check op t1 t2 avoid)))

(defun divisible-left-check (op t1 t2 avoid &aux res)
  (if* (and (equal (left-arg op t1) (left-arg op t2))
	   (avoidable avoid (left-arg op t1))
	   (not (reducible (setq res (remove-left-arg op t1)))))
      then (cons res (remove-left-arg op t2))))

(defun divisible-right-check (op t1 t2 avoid &aux res)
  (if* (and (equal (setq res (right-arg op t1)) (right-arg op t2))
	   (avoidable avoid (right-arg op t1))
	   (not (reducible (setq res (remove-right-arg op t1)))))
      then (cons res (remove-right-arg op t2))))
	  
(defun divisible-ac-check (t1 t2 avoid unity &aux term)
  ; check whether t1 and t2 can be simplified by cancellation law,
  ; where t1 is rooted by an ac operator.
  (when (and unity (avoidable avoid t2) (member0 t2 t1)) 
    (setq t1 (removen t2 t1 1)
	  t2 unity)
    (if (null (cddr t1)) (setq t1 (cadr t1)))
    (if (equal t1 t2) (setq term '(nil)) (setq term (cons t1 t2))))
  
  (if* term then term 
       elseif (and (nonvarp t2)
		   (same-root t1 t2)
		   (setq term (avoid-common-term
				avoid (args-of t1) (args-of t2))))
       then
       (setq t1 (removen term t1 1)
	     t2 (removen term t2 1))
       (if (null (cddr t1)) (setq t1 (cadr t1)))
       (if (null (cddr t2)) (setq t2 (cadr t2)))
       (cons t1 t2)))

(defun avoidable (avoid term)
  (if* (null avoid) then t
      elseif (variablep term) then nil
      elseif (equal avoid term) then nil
      elseif (is-ground term) then t
      else nil))

(defun avoid-common-term (avoid arg1 arg2)
  (sloop for term in arg1 
	if (and (member0 term arg2) (avoidable avoid term)) return term
	finally (return nil)))

(defun right-arg (op term)
  (if* (and (memq op $associative) (op-has-status op))
      then (right-arg2 op term) else (second-arg term))) 


(defun remove-right-arg (op term)
  (if* (op-has-rl-status op) 
      then (first-arg term) 
      else (remove-right-arg2 op term)))

(defun left-arg (op term)
  ; return the leftest arguments of the operator "op".
  (if* (and (memq op $associative) (op-has-rl-status op))
      then (left-arg2 op term) else (first-arg term)))

(defun remove-left-arg (op term)
  ; Remove the leftest arguments of the operator "op".
  (if* (op-has-lr-status op) 
      then (second-arg term) 
      else (remove-left-arg2 op term)))

(defun right-arg2 (op term)
  (if* (variablep term) then term
      elseif (eq op (op-of term)) then (right-arg2 op (second-arg term))
      else term))

(defun remove-right-arg2 (op term &aux new)
  (if* (variablep term) then nil
      elseif (eq op (op-of term)) 
      then (if* (setq new (remove-right-arg2 op (second-arg term)))
	       then (make-term op (list (first-arg term) new))
	       else (first-arg term))))

(defun left-arg2 (op term)
  ; return the leftest arguments of the operator "op".
  (if* (variablep term) then term
      elseif (eq op (op-of term)) then (left-arg2 op (first-arg term))
      else term))

(defun remove-left-arg2 (op term &aux new)
  ; Remove the leftest arguments of the operator "op".
  (if* (variablep term) then nil
      elseif (eq op (op-of term)) 
      then (if* (setq new (remove-left-arg2 op (first-arg term)))
	       then (make-term op (list new (second-arg term)))
	       else (second-arg term))))

(defun trace-divisible (t1 t2 eqn)
  (princ "By cancellation law, the pair of the terms") (terpri)
  (princ "    [") (write-term (lhs eqn)) (princ ", ") 
  (write-term-simple (rhs eqn)) (princ "]") (terpri)
  (princ "    is simplified to: ") 
  (princ "    [") (write-term t1) (princ ", ") 
  (write-term-simple t2) (princ "]") (terpri)
  )

;;;;;;;;;;;;;;;;
;;; functions delt with associative operators.
;;;;;;;;;;;;;;;;

(defun new-rule-from-assoc (rule)
  ; make a new rule for "rule" by associativity.
  (let (op var lhs rhs)
    (setq op (op-of (lhs rule)))
    (when (and (member op $associative)
	       (op-has-status op)) 
	  (setq var (make-new-variable))
	  (if* (op-has-lr-status op)
	       then (setq lhs (insert-term-at-right op (lhs rule) var))
	       elseif (op-has-rl-status op)
	       then (setq lhs (insert-term-at-left  op (lhs rule) var)))
	  
	  (when (not (reducible lhs)) 
		(if* (op-has-lr-status op)
		     then (setq rhs (insert-term-at-right op (rhs rule) var))
		     elseif (op-has-rl-status op)
		     then (setq rhs (insert-term-at-left  op (rhs rule) var)))
		(setq rule (make-eqn lhs rhs nil (list 'asso (ruleno rule))))
		(setq rule (make-new-rule rule))
		(add-rule-time rule)))))

(defun insert-term-at-right (op t1 t2)
  ; t1 is as if a binary tree with the node "op". 
  ; Insert "t2" at the right most leaf of the tree.
  (if* (and (nonvarp t1) (eq op (op-of t1)))
      then (make-term op (list (first-arg t1) 
				(insert-term-at-right op (second-arg t1) t2)))
      else (make-term op (list t1 t2))))

(defun insert-term-at-left (op t1 t2)
  (if* (and (nonvarp t1) (eq op (op-of t1)))
      then (make-term op (list (insert-term-at-left op (first-arg t1) t2)
				(second-arg t1)))
      else (make-term op (list t2 t1))))
      
(defun separated (eqn &aux (tt (args-of (lhs eqn)))
		      res  (ss (args-of (rhs eqn))))
  ; "tt" is in form of f(t1, t2, ... tn) and "ss" is in form of
  ; f(s1, s2, ..., sn). This function throws the equations
  ; "t1 == s1", "t2 == s2", ... "tn == sn" to the higher levels.
  (while (and tt (equal (car tt) (car ss)))
    (setq tt (cdr tt) ss (cdr ss)))
  (when tt
    (change-lhs-rhs eqn (pop tt) (pop ss))
    (sloop for xa in tt for xb in ss do
	   (unless (equal xa xb)
	     (push (make-eqn xa xb (ctx eqn) (eqn-source eqn)) res)))
    eqn))
