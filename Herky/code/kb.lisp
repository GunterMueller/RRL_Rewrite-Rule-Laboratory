(in-package "USER")

;--- This file contains functions for running the Knuth-Bendix completion 
;--- procedure. and also for ac. Ac and non-ac share a lot of code but
;--- conditional left as is. Again does not have any problems
;--- converting to Franz/Zeta lisp.

(defun start-kb ()
  (if (and $theory-eqns (not $polynomial)) (digest-theory-eqns))
  (if $automatic (set-short-hand-flag))

  (cond
   ($confluent 
    (terpri)
    (if (or $discarded (eq $kb '*condi*) $input-superpose $unit-superpose)
	(princ "Your system is possibly canonical." $out-port)
      (if $lrpo
	  (princ "Your system is already canonical." $out-port)
	(princ "Your system is already locally-confluent." $out-port)))
    (terpri $out-port)
    (return-from start-kb nil))
   ((not (or $eqn-set $rule-set))
    (princ "No axioms are presented!") (terpri) 
    (return-from start-kb nil))
   )

  (sys-flag-init)
  (run-kb-display)
  (setq $confluent t)
  )

(defun run-kb-display (&aux resu)
  ;; Start up the running of Knuth-Bendix and
  ;; print the proof results if there are any.
  (setq resu (knuth-bendix))
  (terpri $out-port)

  (cond
   (resu
    (if* $prove-eqns
	 then
	 (report-proof poport)
	 (if (neq $out-port poport) (report-proof $out-port))
	 else
	 (princ "Your system is not consistent." $out-port) 
	 (terpri $out-port))

    (when $trace-proof ;; $used-rule-nums contains a rule at present.
	  (terpri $out-port)
	  (trace-rule $used-rule-nums) 
	  (terpri $out-port)
	  )
    (setq $prove-eqn nil $prove-eqns nil $used-rule-nums nil)
    )

   ($prove-eqns 
    (princ "Failed to prove the following equation[s]:") (terpri)
    (dolist (eqn $prove-eqns) (princ "    ") (write-eqn eqn))
    )

   ((null $rule-set) (princ "Rule set is empty."))

   (t
    (cond 
     ($condi
      (if (neq $condi 'c)
	  (princ "Critical pairs between user's axioms are computed.")
	  (princ "Your system is possibly canonical." $out-port))
      )

     ($input-superpose
      (princ "Critical pairs with input equations are done.")
      )

     ($unit-superpose
      (princ "Critical pairs with input equations are done.")
      )

     ($discarded
      (princ "Some equations are discarded; your system is possibly confluent.")
      )

     ($lrpo 
      (princ "Your system is canonical." $out-port)
      )

     (t (princ "Your system is locally confluent." $out-port)
	))

    (terpri) (terpri)
    (list-undeleted-rules $rule-set)
    ))

  ;; Prints the results when done: rule set, timing, etc...
  (terpri) (display-kb-stat)
  )

(defmacro is-pure-input ()
  `(or $pure
       (setq $pure
	     (not (or $ac $commutative $condi $fopc)))))

(defmacro reset-kb (mes) `(throw 'kb-top ,mes))

(defmacro knuth-bendix-scheme (&body completion)
  `(while t 
     (runtime-max-warning $proc-time)

     (let ((t1 (start-timer)))
       (setq result (catch 'refuted (catch 'kb-top ,@completion)))
       (setq $proc-time (+ $proc-time (run-time t1))))

     (if (null result) (return nil)
       (if (eq result '*changekb*) (return result)
	 (if (memq result '(*incons* *refuted* *witness*)) (return t))))
     ))

(defmacro decide-which-kb ()
  `(setq $kb 
	(cond ($fopc (if $chiang '*ply* '*bool*))
	      ($polynomial (if *-* '*poly2* '*poly1*))
	      ($ac '*ac*)
	      ($commutative '*ac*)
	      ($condi '*condi*)
	      ((eq $kb '*pure*) $kb)
	      (t (if (< $del-rule-str 2) (setq $del-rule-str 2))
		 '*distree*)
	      )))

(defun knuth-bendix (&aux result)
  (while t
    (decide-which-kb)
    (setq $keep-deleted-rules (or $keep-deleted-rules $trace-proof))
    (setq $save-y-rule (or $ac (eq $pick-rule-str 'm)))

    (setq result
	  (case $kb
		(*distree* (knuth-bendix-scheme (distree-knuth-bendix)))
		(*pure* (knuth-bendix-scheme (pure-knuth-bendix)))
		(*poly1* (knuth-bendix-scheme (poly1-knuth-bendix)))
		(*poly2* (knuth-bendix-scheme (poly2-knuth-bendix)))
		(*ac* (knuth-bendix-scheme (ac-knuth-bendix)))
		(*bool* (knuth-bendix-scheme (bool-knuth-bendix)))
		(*ply* (knuth-bendix-scheme (ply-knuth-bendix)))
		(t (knuth-bendix-scheme (normal-knuth-bendix)))
		))
    (if (neq result '*changekb*) (return result))
    ))

(defmacro empty-post-set ()
  ;; Called when $eqn-set is empty.
  ;; Reset kb when $post-set is not empty.
  `(when $post-set
	 (trace-message 3 "Process all postponed equations ..." nil)
	 (setq $eqn-set $post-set 
	       $post-set nil 
	       $old-nrules $nrules
	       $discard-eqn-max-size $discard-eqn-2max-size)
	 (reset-kb t)
	 ))

(defun pure-knuth-bendix (&aux xa)
  ; The main body of pure knuth-bendix completion procedure.
  (while $del-eqns (pure-process-equation (cdr (pop $del-eqns))))
  (while $eqn-set (pure-process-equation (pop $eqn-set)))

  (if (setq xa (pick-unmarked-rule))
      (reset-kb (pure-critical-pairs xa))
    (empty-post-set)
    ))

(defun normal-knuth-bendix (&aux xa)
  ; The main body of knuth-bendix completion procedure.
  (while $del-eqns (process-equation (cdr (pop $del-eqns))))
  (while $eqn-set (process-equation (pop $eqn-set)))

  (if (setq xa (pick-unmarked-rule))
      (reset-kb (critpairs xa))
    (empty-post-set)
    ))

(defmacro process-equation (eqn)
  `(case $kb
	(*distree* (distree-process-equation ,eqn))
	(*pure* (pure-process-equation ,eqn))
	(*bool* (bool-process-equation ,eqn))
	(*poly1* (poly1-process-equation ,eqn))
	(*poly2* (poly2-process-equation ,eqn))
	(t (ac-process-equation ,eqn))
	))

(defun pure-process-equation (eqn)
  (trace-message 4 "Process " (write-eqn eqn))
  (setq eqn (add-time $norm-time (pure-normal-eqn eqn)))
  (if (and eqn (setq eqn (pure-orient-an-eqn eqn)))
      (add-rule-time eqn)))

(defun process-input-eqn (eqn)
  ; process an input equation for first time.
  (when (member (eqn-source-type eqn) '(user def))
    (cond ($polynomial
	   (change-lhs-rhs 
	     eqn
	     (poly-simplify (lhs eqn))
	     (poly-simplify (rhs eqn))))
	  ($ac
	   (change-lhs-rhs 
	     eqn
	     (first-ac-flat (lhs eqn))
	     (first-ac-flat (rhs eqn))))
	  ((or $condi (rhs eqn))
	   (change-lhs-rhs-ctx 
	     eqn
	     (btp-trans (lhs eqn))
	     (if (rhs eqn)
		 (if $condi 
		     (top-first-trans (rhs eqn))
		     (btp-trans (rhs eqn))))
	     (if (ctx eqn) 
		 (if $condi 
		     (top-first-trans (ctx eqn))
		     (btp-trans (ctx eqn))))))))
  eqn)

(defun add-rule (rule)
  (case $kb
	(*distree* (distree-add-rule rule))
	(*ac* (ac-add-rule rule))
	(*pure* (pure-add-rule rule))
	(*poly1* (poly-add-rule rule))
	(*poly2* (poly-add-rule rule))
	(*ply* (ply-add-rule rule))
	(*bool* (bool-add-rule rule))
	(t (add-rule-complete rule))
	))

(defun add-crit-rule (rule)
  ;; Type 4 rule has nonempty disjoint variable set at both sides.
  (setq rule (make-new-rule rule 4))
  (trace-message 2 "Add a no-reduction rule:"
		 (terpri $out-port) (princ "    " $out-port) 
		 (write-rule rule))
  (push-end rule $subsume-rules)
  (push-end rule $rule-set)
  (when (and $ac (not (is-scheme-rule rule)))
    (if $idem-superpose (add-pairs (rule-x-to-y rule) rule))
    (add-all-pairs (rule-x-to-y rule)))
  )

(defmacro make-eqn-from-deleted-rule (rule lhs ruleno)
  ; >>>>>> 10/5/90. 
  `(if (or $keep-deleted-rules $ac)
      (make-eqn ,lhs (rhs ,rule) nil 
		(list 'deleted (ruleno ,rule) ,ruleno))
     (let ()
       (set-lhs-vars ,rule 1)
       (set-rhs-vars ,rule 1)
       (setf (car (eqn-source ,rule)) 'deleted)
       (setf (cadr (eqn-source ,rule)) (ruleno ,rule))
       (change-lhs ,rule ,lhs)
       )))

(defmacro process-del-rule (eqn rule)
  ; >>>>>> 5/5/89.
  `(case $del-rule-str
     (1 (process-equation ,eqn))
     (2 (push-end ,eqn $eqn-set))
     (3 (push-end ,eqn $eqn-set))
     (4 (setq $del-eqns (insert (cons (lhsize ,rule) ,eqn)
				$del-eqns #'car-lessp)))
     (t (break "Invalid $del-rule-str"))))

(defun add-rule-primitive (rule)
  (trace-message 2 "Add Rule: " (write-rule rule))
  (push-end rule $rule-set)
  (if (is-scheme-rule rule)
      (set-crit-mark rule)
    (if (and (not $ac) (eq $unmark-rule-str 'l) (memq $pick-rule-str '(l e)))
	(organize-rule-by-size rule)))
  (if $prove-eqns (check-witness rule))
  )

(defun pure-add-rule (rule &aux l2)
  (add-rule-primitive rule)
  (setq $op-rules (warning-add-rule rule $op-rules))

  (sloop with rnum = (ruleno rule)
	 for xa in $rule-set 
	 if (not (or (is-deleted-rule xa)
		     (equal rnum (ruleno xa)))) do
	 
	 (if* (is-deleted-rule rule) then (return nil)
	      elseif (setq l2 (pure-reduce-by-one-rule (lhs xa) rule)) 
	      then
	      (trace-message 3 "" (trace-reduce-lhs xa))
	      (clean-rule xa) 
	      (setq l2 (make-eqn-from-deleted-rule xa l2 rnum))
	      (process-del-rule l2 xa)

	      elseif (and (> $reduce-system 2)
			  (setq l2 (pure-reduce-by-one-rule (rhs xa) rule))) 
	      then
	      (setq l2 (pure-norm-term l2))
	      (trace-message 3 "" (trace-reduce-rhs xa l2))
	      (change-rhs xa l2))
	 ))

(defun add-rule-complete (rule)
  ; Adds RULE to existing rule set.
  ; First, add RULE to the data-structure that organizes rules by outermost
  ; operator (for normalization use) using the global variable OP-LIST.
  ; Then add the new rule at the end of the rule set.
  (if (not (is-nilpotent-rule rule t))
      (setq $op-rules (warning-add-rule rule $op-rules)))

  (add-rule-primitive rule)

  (if (> $reduce-system 0) (reduce-other-rules rule))
  (when (and $ac (not (is-scheme-rule rule)))
	(if $idem-superpose (add-pairs (rule-x-to-y rule) rule))
	(add-all-pairs (rule-x-to-y rule)))
  )

(defun reduce-other-rules (rule &aux l2 (rnum (ruleno rule)))
  ; Next, loop through the current rule set and try to do the following:
  ;   (i) Check if the left-hand-side is reducible by the new rule.
  ;	  If so, first put the rule-number of the deletable rule in the
  ;	  global-variable $DEL-RULES (helps in critical-pair computation).
  ;	  Then cleanup this rule from the organization of rules by
  ;	  outermost operator.  Then delete this rule from the rule set and
  ;	  put the new equation obtained in $EQN-SET.
  ;
  ;  (ii) If the lhs is not reducible by the new rule, try to rewrite the
  ;	  rhs of the old rule.  If possible, update the data-structures
  ;	  containing the rules.
  ;  ; keep the system reduced.
  ;
  ; special critical pair computing strategy is supported here.
  (setq $used-rule-nums nil)

  (dolist (xa $rule-set)

    (unless (is-deleted-rule xa)
	    ;; (and $condi (equal (car (rule-source xa)) 'def))

     (if* (or (is-deleted-rule rule) (<= rnum (ruleno xa)))
	 then (return nil)
	 elseif (setq l2 (reduce-by-one-rule (lhs xa) rule)) then
	 (trace-message 3 "" (trace-reduce-lhs xa))
	 (clean-rule xa)
	 (setq l2 (make-eqn-from-deleted-rule xa l2 rnum))
	 (process-del-rule l2 xa)

	 else

	 (if* (and (> $reduce-system 2)
		   (setq l2 (reduce-by-one-rule (rhs xa) rule))) 
	      then
	      (setq l2 (if* (variablep l2) l2 (norm-term l2)))
	      (trace-message 3 "" (trace-reduce-rhs xa l2))
	      (when $trace-proof (update-used-rules xa))
	      (change-rhs xa l2))
	 )))
  )

(defun warning-add-rule (rule rule-list)
  ; Add RULE in RULE-LIST.
  (when (> $nrules (+ $old-nrules $newrule-max))
	(terpri) (princ "WARNING: More than ")
	(princ (- $nrules $old-nrules)) (princ " new rules generated ")
	(princ "without any change of the precedence.")
	(terpri)
	(setq $old-nrules $nrules)
;	(if* $akb-flag then
;	     (princ "I undo it to last interaction.") (terpri) 
;	     (undo)
;	     else
;	     (if (not (ok-to-continue)) (reset))
;	     )
	)
  (add-associate-list (op-of (lhs rule)) rule rule-list)
  )

(defun runtime-max-warning (time)
  (if* (and (neq $runtime-max 0) (< $runtime-max time)) then
      (terpri) (princ "WARNING: Run time limit (")
      (princ $runtime-max) (princ " seconds) has been reached.")
      (terpri)
      (if* (ok-to-continue "Continue with a larger limit? ")
	  (setq $runtime-max (times 1.7 $runtime-max))
	(reset))))

(defmacro clean-new-del-rules ()
  `(when $del-new-rules 
	 (dolist (xa $del-new-rules) 
		 (setq $aux-rules (delete1 xa $aux-rules))
		 (setq $rule-set (delete1 xa $rule-set)))
	 (if $keep-deleted-rules 
	     (setq $del-rules (nconc $del-rules $del-new-rules)))
	 (setq $del-new-rules nil)))

(defun clean-rule (rule)
  ; Called when a rule gets deleted to cleanup the auxiliary
  ; data-structure that organizes rules by outermost-operator.
  (push rule $del-new-rules)
  (set-deleted-mark rule)
  (incf $num-del-rules)

  (if $polynomial (setq $poly-rules (delete1 rule $poly-rules)))
  ; clean $poly-multi-1p-rules.
  (sloop for r-list in $poly-multi-1p-rules do
	(if* (member0 rule (cdr r-list)) 
	    then (delete0 rule r-list) (return)))

  ; clean $op-rules.
  (if (eq $kb '*distree*)
      (distree-clean-rule rule)
    (if $ac-distree
 	(ac-distree-clean-rule rule)
      (delete0 rule (assq (op-of (lhs rule)) $op-rules))))
  )

(defun rules-in (rules)
  (terpri) (princ "[ ")
  (sloop for xa in rules do (princ (ruleno xa)) (princ " "))
  (princ "]") (terpri))

#|

(defun condi-add-rule (rule)
  (if* (eq $condi 'i)
     then (induc-add-rule rule)
     elseif (is-reduction rule)
     then (condi-add-rule-complete rule)
     else (add-crit-rule rule)))

(defun induc-reduce-other-rules (rule &aux l2)
  (sloop with rnum = (ruleno rule)
	for xa in (rules-with-op (op-of (lhs rule)) $op-rules) 
	if (and (ctx xa)
		(not (equal (car (rule-source xa)) 'def))
		(not (equal rnum (ruleno xa)))
		(setq l2 (condi-limit-reduce-by-one (lhs xa) rule (ctx xa))))
	  do
	  (trace-message 3 "" (trace-reduce-lhs xa))
	  (clean-rule xa) 
	  (if* (nequal l2 (rhs xa)) then
	       (setq l2 (make-eqn l2 (rhs xa) (ctx xa) 
				  (list 'deleted (ruleno xa) rnum)))
	       (push l2 $eqn-set))
	  (setq $used-rule-nums nil)))


(defun condi-reduce-other-rules (rule &aux l2 (rnum (ruleno rule)))
  ; Next, loop through the current rule set and try to do the following:
  ;   (i) Check if the left-hand-side is reducible by the new rule.
  ;	  If so, first put the rule-number of the deletable rule in the
  ;	  global-variable $DEL-RULES (helps in critical-pair computation).
  ;	  Then cleanup this rule from the organization of rules by
  ;	  outermost operator.  Then delete this rule from the rule set and
  ;	  put the new equation obtained in $EQN-SET.
  ;
  ;  (ii) If the lhs is not reducible by the new rule, try to rewrite the
  ;	  rhs of the old rule.  If possible, update the data-structures
  ;	  containing the rules.
  ;  ; keep the system reduced.
  ;
  ; special critical pair computing strategy is supported here.
  (setq $used-rule-nums nil)

  (dolist (xa $rule-set)

    (unless (or (is-deleted-rule xa)
		(eq rnum (ruleno xa))
		(and $condi (equal (car (rule-source xa)) 'def)))
     (setq $premises-set (ctx xa))

     (if* (is-deleted-rule rule) 
	 then (return nil)
	 elseif (setq l2 (reduce-by-one-rule (lhs xa) rule)) then
	 (trace-message 3 "" (trace-reduce-lhs xa))
	 (clean-rule xa)
	 (setq l2 (make-eqn l2 (rhs xa) (ctx xa) 
			    (list 'deleted (ruleno xa) rnum)))

	 (setq l2 (condi-crit-checkeq l2))
	 (process-del-rule l2 xa)

	elseif (and (> $reduce-system 1)
		    (null (ctx rule)) (is-condi-rule xa)
		    (sloop for pre in (cdr (ctx xa))
			  thereis (reduce-by-one-rule (car pre) rule))) then
	  (trace-message 3 ""
			 (trace-reduce-lhs xa " because of its condition"))
	  (clean-rule xa) 
	  (setq l2 (make-eqn (lhs xa) (rhs xa) (ctx xa) 
			     (list 'deleted (ruleno xa) rnum)))
	  (setq	l2 (condi-crit-checkeq l2))
	  (process-del-rule l2 xa)
        else

	(if* (and (> $reduce-system 2)
		  (setq l2 (reduce-by-one-rule (rhs xa) rule))) 
	     then
	     (setq l2 (if* (variablep l2) then l2 (norm-rhs l2)))
	     (trace-message 3 "" (trace-reduce-rhs xa l2))
	     (when $trace-proof (update-used-rules xa))
	     (change-rhs xa l2))
	))))

|#