(in-package "USER")

(defmacro new-rule-rename-vars ()
  `(when vars
	 (setq vars (sort vars '>))
	 (setq vars (sloop for new from 1
			   for old in vars 
			   collect (cons old (upto-var new))))
	 (setf (lhs eqn) (applysubst vars (lhs eqn)))
	 (setf (rhs eqn) (applysubst vars (rhs eqn)))
	 (if (abs-ctx eqn) (setf (abs-ctx eqn) (applysubst vars (abs-ctx eqn))))

	 ;; The experiment shows no gains ------ 06/10/91.
	 ;;(set-lhs-vars eqn (vars2-list (lhs eqn)))

	 (set-lhs-vars eqn (applysubst vars (get-lhs-vars eqn)))
	 (set-rhs-vars eqn 1)
	 ))

#|
(defmacro new-rule-condi-info ()
  `(when (and $condi (setq lhs (ctx eqn)))
	(setq rhs nil)
	(sloop for pre in (cdr lhs) do
	       (sloop for var in (pre-vars pre) do
		      (if (not (member var vars))
			  (query-insert var rhs))))
	;; if $condi, (ref-cvars rule) gives the variables in the condition.
	(if rhs (setf (ref-condi-vars nrule) rhs))
	))
|#

(defmacro new-rule-ac-info ()
  `(when $ac ;; if $ac, (ref-rvars rule) stores the symmetry info and 
	;; top variables in the lhs.
	 (if $symmetry-check (set-symmetry-info eqn))
	 (if (and $top-only-var-check (ac-root (lhs eqn)))
	     (set-top-only-vars eqn))
	 ))

(defun make-new-rule (eqn &optional (type 1) nrule size &aux
			  (lhs (lhs eqn))
			  (rhs (rhs eqn))
			  vars)
  (if (= type 4)
      (setq vars (union (get-lhs-vars eqn) (get-rhs-vars eqn)))
    (setq vars (get-lhs-vars eqn)))

  (set-linear-flag eqn (= (length (get-lhs-vars eqn)) 
			  (length (all-vars-of (lhs eqn)))))

  (new-rule-rename-vars)

  (setq vars (get-lhs-vars eqn)
	size (if* size then size
		  elseif $polynomial 
		  then (+ (poly-size lhs) (quotient (poly-size rhs) 50))
		  else (get-rule-size lhs rhs (eqn-source eqn) t)))
  (if (null nrule) (setq nrule (incf $nrules)))

  (setq nrule (make-rule eqn nrule size type))
  (new-rule-ac-info)

  nrule)

#|
(defun is-condi-rule-candidate (eqn oneway)
  ;  Tries to make a rule from terms T1 and T2.
  ;         Returns:  0 - if no variables.
  ;                   1 - if varset(T1) properly contains varset(T2) and
  ;                          varset(T1) contains varset(C)
  ;	      	      2 - if varset(T2) properly contains varset(T1) and
  ;                          varset(T2) contains varset(C)
  ;	      	      3 - if varset(T1) = varset(T2)
  ;                          varset(T1) contains varset(C)
  ;	    	    nil - if neither varset contains the other or
  ;                          neither varset(T1) nor varset(T2)
  ;                                  contains varset(C)
  ;
  ; In the last case, when no rule can be made out of T1 and T2, call the
  ; function INVALID-RULE which will introduce a new operator and try to
  ; form two rules.
  ;
  (let ((vart1 (get-lhs-vars eqn)) 
	(vart2 (get-rhs-vars eqn)) 
	(varc (if* (null $condi) (var-list (ctx eqn))))
	 l4 l5)
    (setq l4 (length vart1)
	  l5 (length vart2))
    (cond ;((and (eq l4 0) (eq l5 0)) 0)
	  ((and (eq l4 l5) (is-subset vart2 vart1))
           (if* (is-subset varc vart1)
             3
	     (invalid-rule eqn vart1 vart2)))
	  ((and (not oneway) (lessp l4 l5) (is-subset vart1 vart2))
           (if* (is-subset varc vart2)
             2
             (invalid-rule eqn vart2 vart1)))
	  ((and (is-subset vart2 vart1) (is-subset varc vart1)) 1)
          (t (invalid-rule eqn vart1 vart2)))))
|#

(defun is-rule-candidate (eqn oneway)
  ; Returns:
  ;           0 - if no variables
  ;           1 - if varset(T1) properly contains varset(T2) 
  ;	      2 - if varset(T2) properly contains varset(T1) 
  ;	      3 - if varset(T1) = varset(T2)
  ;	    nil - if neither varset contains the other.
  ; In the last case, when no rule can be made out of T1 and T2, call the
  ; function INVALID-RULE which will introduce a new operator and try to
  ; form two rules.
  (let ((t1 (lhs eqn)) (t2 (rhs eqn)) l1 l2)
    (when (variablep t1) (exchange-lr eqn) (psetq t1 t2 t2 t1))
    (cond ((is-inconsi-pair t1 t2)
	   (if* $fopc
	       then (if* (equal (ctx eqn) t2) 
			then (inconsistent-eqn eqn)
			else (add-rule-time (make-eq eqn (lhs eqn) (rhs eqn)))
			)
	       else (inconsistent-eqn eqn))
	   nil)
	  ((is-commut-pair t1 t2)
	   (make-ass-com-op (op-of t1) eqn (assoc-op-p (op-of t1))) 
	   (reset-kb '*changekb*))
          ((is-assoc-under-c t1 t2) (make-ass-com-op (op-of t1) eqn t) nil)
	  (t (if (is-assoc-pair t1 t2) (push (op-of t1) $associative))
	     (setq t1 (get-lhs-vars eqn) 
		   t2 (get-rhs-vars eqn)
		  l1 (length t1)
	          l2 (length t2))
            (cond 
		  ((and (eq l1 l2) (is-subset t1 t2)) 
		   (if oneway 1 3))
		  ((and (not oneway) (lessp l1 l2) (is-subset t1 t2))
		   2)
		  ((is-subset t2 t1) 		   
		   1)
	  	  (t (invalid-rule eqn t1 t2)))))))

(defun invalid-rule (eqn varl varr)
  ; Called when an equation to be oriented is not valid either way
  ; or when the user explicitly wants to introduce a new operator.
  ; If introduces the operator as a function of the intersection
  ; of the varsets.
  (trace-message 1 "This equation cannot be oriented into a rule: "
		 (write-eqn eqn))
  (if* (or $akb-flag $automatic)
      then (if* (or (eq $post-posi 1) (and $automatic (> $new-sym-num 4)))
		then (push eqn $post-set) nil
		else (add-operator-defn eqn varl varr))
      else
      (user-menu 
	(abort "       Abort to the top level" (reset))
	(left-right "  As it is. The rule will not be used for reduction." 
		(add-crit-rule eqn))
	(makeeq "      Introduce the equality predicate"
		(make-eq eqn (lhs eqn) (rhs eqn)))
	(operator "    Introduce a new operator" 
		  (add-operator-defn eqn varl varr))
	(postpone "    Postpone the equation" (push eqn $post-set))
	(right-left "  From right to left. The rule will not be used for reduction" 
		    (exchange-lr eqn)
		    (add-crit-rule eqn))
	)
      nil))

(defun make-theory-rule (eqn)
  ;;(setq eqn (make-eqn (lhs eqn) (rhs eqn) nil (eqn-source eqn)))
  (setq $eqn-set (delete1 eqn $eqn-set))
  (setq eqn (make-rule eqn 0 0 5))
  (trace-message 2 "  Add Theory Rule: " (write-rule eqn))
  (push eqn $theory-rules)
  )

(defun make-dummy-rule (eqn &optional real-size)
  (incf $nrules)
  (setq real-size (if real-size 
		      (+ 2 (* 2 (size (lhs eqn))) (size (rhs eqn))) 
		    1000))
  (setq eqn (make-rule eqn $nrules real-size 5))
  (trace-message 4 "  Add Dummy Rule: " (write-rule eqn))
  (if $keep-deleted-rules (push eqn $del-rules))
  eqn)

(defun make-p-commut-rule (eqn &aux lhs)
  ; A p-commutative rule is of form
  ;       + n(x*y) == + n(y * x)
  ; where + is AC operator, n is a natural number and (x * y)'s are the only 
  (if (total-term-ordering (first-arg (lhs eqn)) (first-arg (rhs eqn))) 
      (exchange-lr eqn))
  (setq eqn (make-new-rule eqn 5 nil 100000))
  (push-end eqn $rule-set)
  (trace-message 2 "Add Pseudo-commutative Rule: " (write-rule eqn))
  (setq lhs (lhs eqn))
  (push (setq lhs (list (ruleno eqn) 
			 (op-of lhs)
			 (op-of (first-arg lhs))
			 (length (args-of lhs))))
	$p-commut-rules)
  (p-commut-reduce-others lhs))

(defun get-rule-size (lhs rhs source red)
  (case $rule-size
	(s (size lhs))
	(w (w-size lhs))
	(o (if (falsep rhs) 
	       (- (* 2 (w-size lhs)) 5) ; 10
	     (+ (* 2 (w-size lhs)) (w-size rhs))))
	(d (+ (* 10 (depth lhs)) (quotient (depth rhs) 2) 
	      (quotient (w-size lhs) 5) (quotient (w-size rhs) 5)))
	;; (d (+ (* 50 (depth lhs)) (* 2 (depth rhs)) (w-size lhs) (w-size rhs)))
	(l (+ (* (if red 20 5) (literal-num lhs)) (w-size lhs) (w-size rhs)))
	(u (unknown-size lhs (w-size rhs) source (if red 20 5)))))

(defun unknown-size (term pres-size source weight &aux level)
  ; This function is named because of its experimental status.
  (setq level (if* (and (numberp (first source)) (numberp (second source)))
		  then (add1 (min (get-rule-level (first source)) 
				  (get-rule-level (second source))))
		  else (caseq (first source)
			 (idem (get-rule-level (second source)))
			 (deleted (max 0 (sub1 (get-rule-level (second source)))))
			 (t 0))))
  (add $ncritpr (times 100 level) (times weight (size term)) pres-size))

(defun get-rule-level (ruleno)
  ; we define simply that the level of a rule is the size of the rule divided by 50.
  (sloop for rule in $rule-set 
	as rulno = (ruleno rule)
	if (eq ruleno rulno) return (quotient (lhsize rule) 100)
	finally (return 0)))

(defun add-operator-defn (eqn varl varr &aux l1)
  ; Called when new operators are needed to orient an equation into a rule.
  (setq l1 (new-term varl varr $akb-flag)
	varl (make-eqn (rhs eqn) l1 nil (eqn-source eqn)))

  (set-rhs-vars eqn (args-of l1))
  (setq eqn (change-rhs eqn l1))
  (push eqn $eqn-set)

  (trace-message 2 "Introduce a new operator: " (write-eqn eqn))

  (set-rhs-vars varl (args-of l1))
  (set-lhs-vars varl varr)
  (push varl $eqn-set)

  (if (eq $kb '*distree*) (re-init-distree))

  (reset-kb '*newop*))

(defun make-rule-from-ass (ass source)
  ; Sort maximal items onto the left side of the rule.  If this
  ; cannot be done, add whatever equations are necessary to 
  ; the equation set and return nil.
  (setq ass
	(if (eq (op-of ass) *xor*) 
	    (if (member0 *trueterm* ass)
		(delete0 *trueterm* (cdr ass))
		(cons *trueterm* (args-of ass)))
	    (list *trueterm* ass)))

  (if (eq $ordering 's) 
      (make-rule-size-order ass source)
    (make-rule-lrpo-order ass source)
    ))

(defun make-rule-size-order (ass source &aux (max 0) lhs rhs)
  ;; put all monomials of the maximal size into lhs.
  (sloop with lnum for xa in ass do
	 (cond
	  ((> (setq lnum (literal-num xa)) max)
	   (setq max lnum
		 rhs (nconc rhs lhs)
		 lhs (ncons xa)))
	  ((= lnum max) (push xa lhs))
	  (t (push xa rhs))))

  ;; remove those which are less from lhs.
  (sloop for xa in lhs do
	 (pop lhs)
	 (if (sloop for ya in lhs thereis (compare-monomial ya xa))
	     (push xa rhs)
	     (setq lhs (append1 lhs xa))))

  ; max contains the variables of the potentail lhs of the rule.
  (setq max (var-list (make-term *xor* lhs)))
  (sloop for xa in rhs
	for xavars = (all-vars-of xa) do
	(pop rhs)
	(if* (is-subset xavars max)
	    then (setq rhs (append1 rhs xa))
	    else
	    (push xa lhs) 
	    (setq max (union xavars max))))

  (setq ass (make-eqn (simp-xor-simp lhs) (simp-xor-simp rhs) nil source))
  (set-lhs-vars ass max) ;; what's in max?
  (make-new-rule ass))

(defun make-rule-lrpo-order (ass source &aux l2)
  (sloop for xa in ass do
	 (pop ass)
	 (if (sloop for ya in ass thereis (compare-item ya xa))
	     (push xa l2)
	   (append1 ass xa t)))
  (setq ass (make-eqn (simp-xor-simp ass) (simp-xor-simp l2) nil source))
  (update-used-rules ass)
  (make-new-rule ass)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;  PICK ONE RULE TO COMPUTE CRITICAL PAIRS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pick-unmarked-rule ()
  ; Goes through the rule set and picks the unmarked rule with
  ; the smallest left-hand-side size.  If there are more than
  ; one such pick, the earliest or latest is choosen depending
  ; on the critical-pair strategy.  If a rule is found, mark it
  ; and return it.  If all rules are marked already, return NIL.

  ;; At first, clean up the deleted rules.
  (clean-new-del-rules)

  (if* (eq $pick-rule-str 'm) then (manual-pick)
       ;; elseif (eq $condi 'i) then (induc-pick-unmark)
       elseif $ac then (pick-ac-pair)
       elseif (eq $pick-rule-str 'f)
       then (sloop for rule in $rule-set 
		   if (crit-unmarked rule) return (set-crit-mark rule))
       else (pick-one-unmarked-rule))
  )

(defun induc-pick-unmark ()
  ; Return a definition rule if there is an unmarked one.
  ; Otherwise return a property one that is not big than any other rules.
  (sloop for xa in $rule-set 
	if (and (crit-unmarked xa) 
		(eq (car (rule-source xa)) 'def))
	  return (set-crit-mark xa)
	finally (return nil)))

(defun is-big-enough-rule (rule)     
  ; return t iff (lhs rule) is bigger than some marked rules other than "rukenos".
  (sloop with lhs = (lhs rule)
	for xb in (cdr (assoc (op-of lhs) $op-rules))
	thereis (is-sub-nonvar-term (lhs xb) lhs)))

(defun manual-pick (&aux rules)
  ; pick a rule for computing critical pairs.
  (setq rules (sloop for r1 in $rule-set 
		     if (crit-unmarked r1) collect r1))
  (if* rules then
    (if* (null (cdr rules)) then (set-crit-mark (car rules)) else
     (terpri)
     (format t "There are ~n candidates for the first rule. Which one ? " 
	     (length rules))
     (terpri)
     (prog ((l3 rules) n1 l2)
	loop-here	       
        (setq l2 l3
              l3 (nthcdr 10 l3))
	(terpri)
	(if* l3 then (princ "Following 10 rules are displaied first: ")
	            (terpri))
	(sloop for xa in l2 for n2 from 1 to 10 do (write-rule xa))
	(terpri)
	(setq n1 nil)
	(ask-number n1 "Please type a rule number, 0 for none, 999 to quit: ")
	(if* (not (memq n1 '(0 999))) then
  	   (setq n1 (sloop for xa in rules 
			if (equal (ruleno xa) n1) 
			    return (case $crit-with-str 
                                      ((h1 h2) (rule-x-to-y xa))
	                              (t (set-crit-mark xa)))
			finally (return 0))))
	(if* (eq n1 0) 
	   then (if* (null l3) then
		    (princ "You must choose one rule !") (terpri)
		    (setq l3 rules))
		(go loop-here)
	   elseif (eq n1 999) then (return (reset))
	   else (return n1))))))

(defmacro is-scheme-rule (rule)
  ;; a term t is a scheme-term iff t = f(x1, x2, ..., xn)
  ;; where x_i are distinct variables.
  `(and (is-linear-rule ,rule)
	(sloop for xa in (args-of (lhs ,rule)) always (variablep xa))
	))

(defun organize-rule-by-size (rule &aux (size (lhsize rule)) l1)
  ;; Use $pair-set for organizing unmarked rules.
  ;; Insert the rule by its size.
  (if (setq l1 (assoc size $pair-set))
      (if (eq $pick-rule-str 'l)
	  (setf (cdr l1) (cons rule (cdr l1)))
	(nconc l1 (ncons rule)))
    (setq $pair-set (insert (list size rule) $pair-set #'car-lessp)))
  )

(defun pick-one-unmarked-rule (&aux l1)
  ;; Return an undeleted rule from $piar-set.
  ;; The structure of $pair-set is
  ;;  ((weight1 r11 r12 r13 ...)
  ;;   (weight2 r21 r22 r23 ...)
  ;;    ... ...
  ;;   (weightn rn1 rn2 rn3 ...))
  (if (eq $unmark-rule-str 'l)
      (while t
	(if* (null $pair-set) 
	     then (return-from pick-one-unmarked-rule nil)
	     elseif (null (cdar $pair-set))
	     then (setq $pair-set (cdr $pair-set))
	     else
	     (setq l1 (car $pair-set))
	     (sloop for xa in (cdr l1) do
		    (setf (cdr l1) (cddr l1))
		    (if (not (is-deleted-rule xa))
			(return-from pick-one-unmarked-rule 
				     (set-crit-mark xa))))
	     ))
    (sloop with ssize = 999999 
	   for r1 in $rule-set 
	   if (crit-unmarked r1)
	   do (if* (lessp (lhsize r1) ssize)
		   then (setq ssize (lhsize r1) l1 r1)
		   elseif (and (eq $pick-rule-str 'l) (equal ssize (lhsize r1)))
		   then (setq l1 r1))
	   finally (if l1 (return (set-crit-mark l1))))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;  PICK  SECOND  RULES  TO  COMPUTE  CRITICAL  PAIRS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun intro-with-rules (rule)
  ; Return a list of rules that will be computed crtical pairs WITH "rule".
  ; Called when maintaining a list of marked rules to insert
  ; a newly picked rule for critical pairs.
  ; The flag $MARK-RULE-STR determines the discipline of marked rules (stack,
  ; queue, or sorted).  Sorted pays off in many examples.
  (case $crit-with-str 
	((h1 h2) 
	 (choose-by-hand
	  rule
	  (sloop for xa in $rule-set 
		 if (and (not (is-deleted-rule xa))
			 (not (superposed rule xa)))
		 collect xa)))
	(o $rule-set)
	(m (if (and (or (not $input-superpose) 
			(is-source-type rule 'user)
			(is-source-type rule 'sos))
		    (or (not $unit-superpose) (unitp rule))
		    (or (not $support) (not (is-source-type rule 'user)))
		    )
	       (case $mark-rule-str 
		     (l (insert rule $aux-rules 'comp-rule))
		     (q (append1 $aux-rules rule t))
		     (s (cons rule $aux-rules)))))
	(a $rule-set)))

(defun choose-by-hand (rule rules &aux n1)
  ; pick a rule from "rules" so that we compute critical pairs between
  ; it and "rule". One case is to display rules, the other is not.
  (if* (null rules) then
      (set-crit-mark rule)
      (terpri) (princ "No rules can be chosen.") (terpri) 
      nil
      elseif (null (cdr rules)) then rules
      else
      (format t "~%There are ~n candidates as the second rule. ~%" (length rules))
      (if* (eq $crit-with-str 'h1) then
	  (prog ((l2 rules))
	     loop-here	       
	     (terpri)
	(sloop for xa in l2 for n2 from 1 to 10 do (write-rule xa))
	(setq n1 (man-pick-2nd-rule rule rules))
	(if* (eq n1 999) then (return (reset))
             elseif (eq n1 0) then
  	     (terpri)
	     (if* (null (setq l2 (nthcdr 10 l2))) then
 	        (setq l2 rules)
 	        (princ "Choose again !")
	        else 
                (princ "Choose next rules !"))
             (terpri)
 	     (go loop-here)
  	     else 
    	     (return n1)))
     else
     (princ "Which one ? ")
     (setq n1 (man-pick-2nd-rule rule rules))
     (if* (eq n1 999) then (reset)
	elseif (eq n1 0) then
        (terpri) (princ "Try again !") (terpri)
        (choose-by-hand rule rules)
        else n1))))

(defun man-pick-2nd-rule (rule rules &aux n1)
  ; pick a rule from "rules" so that we compute critical pairs between
  ; it and "rule".
  (terpri)
  (setq n1 nil)
  (ask-number n1 "Please type a rule number, 0 for none, 999 to abort: ")
  (if* (not (memq n1 '(999 0))) then
      (setq n1 (sloop for xa in rules 
		     if (equal (ruleno xa) n1) 
		       return (last-check-2nd-rule xa rule)
		     finally (return 0))))
  n1)

(defun last-check-2nd-rule (rule2 rule)
  ; check whether "rule2" has been computed critical pairs with "rule".
  ; If yes, yielding a warning message and return 0. 
  ; Otherwise, return a list containing "rule2".
  (if* (not (superposed rule rule2)) then
      (format t "~%Critical pairs between [~n] and [~n] has been done.~%"
	      (ruleno rule2) (ruleno rule))
      0
      else
      rule2))

(defmacro superposed (rule1 rule2)
  ; Determine whether we have done critical pairs between rule1 and rule2.  
  `(if (< (ruleno ,rule2) (ruleno ,rule1)) 
       (memq (ruleno ,rule1) (pairswith ,rule2))
     (memq (ruleno ,rule2) (pairswith ,rule1))))

(defmacro mark-superposed (rule1 rule2)
  ; Mark "rule1" and "rule2" such that the superposition
  ; has taken place between "rule1" and "rule2".
  ; We put the mark into the rule with the lesser number.
  `(if (< (ruleno ,rule2) (ruleno ,rule1)) 
       (setf (pairswith ,rule2) (cons (ruleno ,rule1) (pairswith ,rule2)))
     (setf (pairswith ,rule1) (cons (ruleno ,rule2) (pairswith ,rule1)))))

