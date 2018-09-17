;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")


;--- This file contains functions for running the Knuth-Bendix completion 
;--- procedure. and also for ac. Ac and non-ac share a lot of code but
;--- conditional left as is. Again does not have any problems
;--- converting to Franz/Zeta lisp.

(defun start-kb ()
  ;  Starts up Knuth-Bendix by testing if the user wishes to set
  ;  any options before actually running kb.
  (prog ((total-time 0))
    (cond
        ($confluent 
	  (if* $lrpo
	    then (princ "Your system is already canonical.")
	    else (princ "Your system is already locally-confluent."))
	  (terpri)
	  (return nil))
	((not (or $eqn-set $rule-set))
	   (princ "No axioms are presented!") (terpri) (return nil)))
    (sys-flag-init)
    (start-push-history)
    (setq $newrule-num 1 $small-depth 3)
    (add-time total-time (run-kb))
    (if* (not $induc) (setq $confluent t))
    (terpri) (display-kb-stat total-time)))

(defun run-kb (&aux port)
  ; Starts up the running of Knuth-Bendix and prints the results when done:
  ; rule set, timing, etc... Returns nil.
  (if* (*catch 'refuted (knuth-bendix1)) 
     then (if* $prove-eqn 
	   then (*throw 'prove '*incons*)
	   else
	   (if* $guest-eqn then
	       (terpri)
	       ; >>>> 1/30/89
	       (princ "A proof of the following equation has been found:")
	       (terpri) (princ "    ") (write-eqn $guest-eqn))
	   (if* $trace-proof then
	       ; $used-rule-nums contains a rule at present.
	       (trace-inconsistency $used-rule-nums) (terpri)
	       (if* (and (ok-to-continue "Save the result in file ? ")
			(setq port (open-write-file "out")))
		   then (trace-inconsistency $used-rule-nums port)
		        (close port))
	       else
	       (terpri) (princ "Your system is not consistent.") (terpri)
	       ))
     else
     (terpri)
     (if* $narrow then
	 (princ "Run kb again to see possible other solutions.")
	 elseif (and (> $idem 1) (or $prove-eqn $guest-eqn)) then
	 (princ "Unit strategy fails to give the proof.")
	 elseif $induc then
	 (if* (eq $induc 'c)
	     then (princ "Your system is possibly canonical.")
	     else (princ "Critical pairs between definitions are computed."))
	 elseif $lrpo then
	 (princ "Your system is canonical.")
	 else
	 (princ "Your system is locally confluent."))
     (terpri) (terpri)
     (if* $rule-set then (list-rules $rule-set)))
  nil)

(defun knuth-bendix1 ()
  ; Run Knuth-Bendix until no equation in the postponed set.
  (if* (or $ac $commutative) then
     (setq $eqn-set (sloop for eq in $eqn-set collect (flatten-eqn eq)))
     (setq $post-set (sloop for eq in $post-set collect (flatten-eqn eq))))
  (sloop with xa while t do
	(add-time $proc_time 
		  (setq xa (*catch 'refuted 
				(*catch 'kb-top
					(if* (is-pure-input)
					    (pure-knuth-bendix2)
					  (knuth-bendix2))))))
	(if* (null xa) 
	    (return nil)
	  (if* (memq xa '(*incons* *refuted* *witness*))
	      (*throw 'refuted xa)))))

(defun is-pure-input ()
  (not (or $ac $commutative $induc $ckb_flag $narrow $in-fopc $prove-eqn)))

(defun reset-kb (mes) (*throw 'kb-top mes))

(defun knuth-bendix2 (&aux xa)
  ; the main loop of knuth-bendix completion procedure.
  (runtime-max-warning $proc_time)
  (sloop while $del-eqns do (process-equation (cadr (pop $del-eqns))))
  (sloop while $eqn-set do (process-equation (pop $eqn-set)))
  (if* (not (and $narrow $ans-rule)) then
    (if* (setq xa (if* $narrow then (pick-goal) else (pick-unmarked-rule)))
	then
        (critpairs xa)
	(reset-kb '*next*)
        elseif $post-set then
	(terpri) (princ "Processing all postponed equations ...") (terpri)
	(setq $eqn-set $post-set $post-set nil $newrule-num 0)
	(reset-kb '*next*)
	elseif $post-ass-set then
	(terpri) (princ "Processing all postponed assertions ...") (terpri)
	(sloop for i from 1 
	      if (and (< i $immediate) (setq xa (pop $post-ass-set)))
	      do (if* (= $trace_flag 3) then (terpri)
		     (princ "Process proposition: ") 
		     (write-assertion (cdr xa)))
	      (order-ass (cddr xa) (cadr xa)) 
	      else return nil)
	(reset-kb '*next*)
	)))

(defun pure-knuth-bendix2 (&aux xa)
  ; the main loop of knuth-bendix completion procedure.
  (runtime-max-warning $proc_time)
  (sloop while $del-eqns do (pure-process-equation (cadr (pop $del-eqns))))
  (sloop while $eqn-set do (pure-process-equation (pop $eqn-set)))
  (if* (setq xa (pick-unmarked-rule))
      then (pure-critpairs xa)
      (reset-kb '*next*)
      elseif $post-set 
      then
      (terpri) (princ "Processing all postponed equations ...") (terpri)
      (setq $eqn-set $post-set $post-set nil $newrule-num 0)
      (reset-kb '*next*)
      ))

(defun process-equation (eqn &optional not-set-flag &aux eqn1)
  ; process an input axiom for first time.l
  (if* (equal-term (lhs eqn) (rhs eqn)) then nil
       elseif $induc then (cover-norm-order eqn)
       else
   (if* (= $trace_flag 3) 
	then (terpri) (princ "Processing  ") (write-eqn eqn))
   (if* (not not-set-flag) then (setq $var-type-list nil))
   (setq eqn1 (add-time $norm_time (normalize eqn)))
   (cond ((null eqn1) nil)
	 ($ckb_flag
	  ;; ------------- 11/11/90.
	  (if* (and-lhs-true-rhs eqn1)
	      (sloop for new in (split-lhs-and eqn1) 
		    do (process-equation new))
	    (orient-an-eqn eqn1)))
	 ((truep (rhs eqn1)) (process-assertion eqn1))
         (t (orient-an-eqn eqn1))
	 )))

(defun pure-process-equation (eqn)
  ; process an input axiom for first time.
  (if* (= $trace_flag 3)
      then (terpri) (princ "Processing  ") (write-eqn eqn))
  (setq eqn (add-time $norm_time (pure-checkeq-normal eqn)))
  (if* eqn (pure-orient-an-eqn eqn)))

(defun first-process-eqn (eqn)
  ; process an input equation for first time.  ;; 6/21/92.
  (if (memq (car (eqn-source eqn)) '(user def))
      (if $induc
	  (let ((ctx (if (ctx eqn) (new-first-ctx-trans (ctx eqn))))
		(lhs (new-trans-simp (lhs eqn)))
		(rhs (if (rhs eqn) (new-trans-simp (rhs eqn)))))
	    (change-lhs-rhs-ctx eqn lhs rhs ctx))
	(if (rhs eqn)
	    (let ((ctx (if (ctx eqn) (simp-first-trans (ctx eqn))))
		  (lhs (simp-first-trans (lhs eqn)))
		  (rhs (if (rhs eqn) (simp-first-trans (rhs eqn)))))
	      (change-lhs-rhs-ctx eqn lhs rhs ctx))
	  eqn))
    eqn))

(defun add-rule (rule)
  (if* (and $polynomial (is-homogeneous-rule rule))
      (poly-add-homo-rules rule))
  (if* $narrow
     then (add-rule-linear rule)
     elseif (and $induc (neq $induc 'c))
     then (induc-add-rule rule)
     elseif (is-reduction rule)
     then (add-rule-complete rule)
     else (add-crit-rule rule)))

(defun pure-add-rule (rule &aux l2)
  (if* (> $trace_flag 1) then (terpri) (princ "Adding Rule: ") 
	(write-rule rule))
  (setq $op_rules (add-rule3 rule $op_rules))
  (setq $rule-set (nconc $rule-set (ncons rule)))
  (if* $witness-eqn (check-witness rule))
  (sloop with rnum = (ruleno rule)
	for xa in $rule-set 
	if (not (= rnum (ruleno xa))) do

     (if* (memq rnum $del-rule-nums) 
	 then (return nil)
	 elseif (setq l2 (pure-reduce-by-one-rule (lhs xa) rule)) then
	 (if* (> $trace_flag 1) then
	     (terpri) (princ "  Deleting rule:") (write-rule xa))
	 (clean-rule xa) ; removes from op_rules and if ac corr. pairs.
	 (setq l2 (make-eqn l2 (rhs xa) (ctx xa) 
			    (list 'deleted (ruleno xa) rnum)))

	 (caseq $del_rule_str
		(1 (pure-process-equation l2))
		(2 (push l2 $eqn-set))
		(3 (setq $del-eqns (insert (list (lhsize xa) l2)
					   $del-eqns 'car-lessp t)))
		(t (break "Invalid $del_rule_str")))

	 elseif (and (> $reduce-system 2)
		     (setq l2 (pure-reduce-by-one-rule (rhs xa) rule))) then
	    (if* (> $trace_flag 1) then
		(terpri) (princ "  The right hand side is reducible:") 
		(terpri) (princ "    ") (write-rule xa))
	    (setq l2 (if* (variablep l2) then l2 else (pure-norm l2)))
	    (replace xa (change-rhs xa l2)))))

(defun add-crit-rule (rule)
  (if* (> $trace_flag 1) then
      (terpri) (princ "Following rule will not be used for reduction.") 
      (terpri)
      (princ "    ") (write-rule rule) nil)
  (set-no-reduction-mark rule)
  (push-end rule $invalid-rules)
  (push-end rule $rule-set)
  nil)

(defun add-rule-complete (rule &aux pres)
  ; Adds RULE to existing rule set.
  ; First, add RULE to the data-structure that organizes rules by outermost
  ; operator (for normalization use) using the global variable OP_LIST.
  ; Then add the new rule at the end of the rule set.
  ;
  (if* (> $trace_flag 1) then (terpri) (princ "Adding Rule: ") 
	(write-rule rule))

  (if* $prove-eqn (consistent-rule rule))

  (if* (not (is-character-rule rule t))
      (setq $op_rules (add-rule3 rule $op_rules)))

  (setq $rule-set (nconc $rule-set (ncons rule)))

  (if* $witness-eqn (check-witness rule))

  (if* (and $check-symmetry $ac 
	   (setq pres (get-symmetry-terms rule))) 
      (set-symmetry-mark rule pres))

  (if* (and $induc (neq $induc 'c))
      ; If a rule can be used to eliminate high degree operators in 
      ; the cover-set method, then save it.
      then (induc-reduce-other-rules rule)
      elseif (= $reduce-system 0)
      then (if* $ac (sloop for xa in $rule-set do (add-pairs rule xa)))
      elseif (setq pres (ctx rule))
      then (if* (if* (eq (car pres) '*&*)
		   then (sloop for pre in (cdr pres) thereis (pre-vars pre))
		   else (all-vars pres))
	       then (reduce-other-rules rule)
	       elseif $ac then
	       (sloop for xa in $rule-set do (add-pairs xa rule)))
      else (reduce-other-rules rule)))

(defun reduce-other-rules (rule &aux l2)
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
  (if* (or $polynomial (and $ac (= $idem 1))) (add-pairs rule rule))
  (sloop with rnum = (ruleno rule)
	for xa in $rule-set 
	if (not (= rnum (ruleno xa))) do

;     (if* (and $induc (eq (car (rule-source xa)) 'def)) then
;	 (if* $ac (add-pairs rule xa))
;	 else)

     (if* $induc (setq $premises-set (ctx xa)))
     (if* (memq rnum $del-rule-nums) 
	 then (return nil)
	 elseif (setq l2 (reduce-by-one-rule (lhs xa) rule)) then
	 (if* (> $trace_flag 1) then
	     (terpri) (princ "  Deleting rule:") (write-rule xa))
	 (clean-rule xa) ; removes from op_rules and if ac corr. pairs.
	 (if* $induc then 
	     (setq l2 (make-eqn (norm-ctx l2) (rhs xa) (ctx xa) 
				(append (list 'deleted (ruleno xa) rnum)
					(rem-dups $used-rule-nums)))
		   $used-rule-nums nil
		   l2 (pre-crit-checkeq l2))
	     else
	     (setq l2 (make-eqn l2 (rhs xa) (ctx xa) 
				(list 'deleted (ruleno xa) rnum))))
	 (process-del-rule l2 xa)
	 ; contextual rewriting;
	elseif (and (> $reduce-system 1)
		    (null (ctx rule)) (is-condi-rule xa) (eq $induc 'c)
		    (sloop for pre in (cdr (ctx xa))
			  thereis (reduce-by-one-rule (car pre) rule))) then
	  (if* (> $trace_flag 1) then
	    (terpri) (princ "  Deleting rule because of its condition:")
	    (terpri) (princ "    ") (write-rule xa))
	  (clean-rule xa) ; removes from op_rules and if ac corr. pairs.
	  (setq l2 (make-eqn (lhs xa) (rhs xa) (ctx xa) 
			     (append (list 'deleted (ruleno xa) rnum)
				     $used-rule-nums))
		$used-rule-nums nil
		l2 (pre-crit-checkeq l2))
	  (process-del-rule l2 xa)
        else

	(if* $ac (add-pairs rule xa))

	(if* (and (> $reduce-system 2) (setq l2 (reduce-by-one-rule (rhs xa) rule))) then
	    (if* (> $trace_flag 1) then
		(terpri) (princ "  The right hand side is reducible:") 
		(terpri) (princ "    ") (write-rule xa))
	    (setq l2 (if* (variablep l2) then l2
			 elseif (predicatep (op-of l2))
			 then (norm-rhs l2)
			 else (norm-ctx l2)))
	    (replace xa (change-rhs xa l2)))

	; old contextual rewriting;
;	(if* (and $ckb_flag (> $reduce-system 2) (is-condi-rule xa)	
;		 (setq l2 (reduce-by-one-rule (ctx xa) rule))) then
;	    (if* (> $trace_flag 1) then
;		(terpri) (princ "  The condition is reducible:") 
;		(terpri) (princ "    ") (write-rule xa))
;	    (setq l2 (norm-ctx l2)
;		  l2 (if* (nequal l2 '(true)) then l2))
;	    (replace xa (change-ctx xa l2)))
	)
    (if* $post-ass-set then (reduce-post-ass rule))))

(defun add-rule-linear (rule)
  ; Insert rules generated in linear completion into $goal-set.
  ; Presently generated rule are not inserted in $op-rules so
  ; they are not used for normalization. Must make sure that same rule
  ; is not added more than once. Do not add rules of the form
  ; $anspred ---> false, they are meaningless.
  ; Do not do critical pairs with rules of the form
  ; $anspred ---> true.
  ; Do not do critical pairs with rules of the form
  ; pred ---> $anspred and $anspred is ground.
  (if* (and (not-in-set rule $goal-set)
	   (not (and (eq (op-of (lhs rule)) $anspred)
		     (falsep (rhs rule))))
	   (or $in-fopc 
	       (not (and (eq (op-of (rhs rule)) $anspred)
			 (null (all-vars (rhs rule))))))) then
      ; If not add to $goal-set.
      ; If doing reduction by goal rules, also add to $op_goal_rules.
      ; If $ac is set add proper pairs to $pair-set
      
      (if* $goal-reduce then 
	  (setq $op_goal_rules (add-rule3 rule $op_goal_rules)))
      (setq $goal-set (nconc $goal-set (ncons rule)))
      ;(if* $ac then (extend-rule-stickel rule)) 
      (if* (and $narrow $ac) then
	  (sloop for xa in $rule-set do (add-pairs rule xa)))

      ; Check if rule represents has $anspred as top level predicate.
      ; If so then mark so not used for critical pairs.
      ; If rule is answer() ---> true, add to answer rule.
      
      (if* (equal (car (lhs rule)) $anspred) then
	  (set-crit-mark rule)
	  (if* (truep (rhs rule)) then (push rule $ans-rule)))
      (if* (> $trace_flag 1) then (terpri) (princ "Adding Rule: ") 
	  (write-rule rule))))

(defun reduce-post-ass (rule &aux l2)
  ; use "rule" to reduce the assertions in $post-ass-set. If one is get
  ; reduced, then process it immediately.
   (setq l2 $post-ass-set
	 $post-ass-set nil)
   (sloop with xb for xa in l2 do
     (if* (setq xb (reduce-by-one-rule (cddr xa) rule)) 
	then (if* (= $trace_flag 3) then (terpri)
		     (princ "Process proposition: ")
		     (write-assertion (cdr xa)))
	     (process-ass-simple xb (cadr xa))
        else (setq $post-ass-set (nconc $post-ass-set (ncons xa))))))

(defun add-rule3 (rule rule-list)
  ; Add RULE in RULE-LIST.
  (if* (> $newrule-num $newrule-max) then
      (if* $akb_flag then
	    (terpri) (princ "WARNING: More than ")
	    (princ $newrule-max) (princ " new rules generated ")
	    (princ "without any change of the precedence.")
	    (princ "I undo it to last interaction.")
	    (terpri) 
	    (setq $newrule-num 1) (undo)
	else
	    (terpri) (princ "WARNING: More than ")
	    (princ $newrule-max) (princ " new rules generated ")
	    (princ "without any change of the precedence.")
	    (terpri)
	    (setq $newrule-num 1)
	    (if* (not (ok-to-continue)) then (reset))))
  (setq $newrule-num (1+ $newrule-num))
  (add-associate-list (op-of (lhs rule)) rule rule-list))

(defun runtime-max-warning (time)
  (if* (and (nequal $runtime-max 0) (< $runtime-max time)) then
      (terpri) (princ "WARNING: Run time limit (")
      (princ $runtime-max) (princ " seconds) has been reached.")
      (terpri)
      (if* (ok-to-continue "Continue with a larger limit? ")
	  (setq $runtime-max (times 1.7 $runtime-max))
	(reset))))

(defun clean-rule (rule &aux ruleno l1)
  ; Called when a rule gets deleted to cleanup the auxiliary
  ; data-structure that organizes rules by outermost-operator.
  (push (setq ruleno (ruleno rule)) $del-rule-nums)
  (setq $rule-set (delete0 rule $rule-set 1))

  ; Predicate Calculus Trace 
  (if* $trace-proof (push rule $del-rules)) 

  ; Auto-ordering
  (if* (> $newrule-num 2) then (setq $newrule-num (sub1 $newrule-num))) 

  ; clean $poly-homo-rules.
  (sloop for r-list in $poly-homo-rules do
	(if* (member0 rule (cdr r-list)) 
	    then (delete0 rule r-list) (return)))

  ; clean $op_rules, $cycle-op-rules.
  (cond	((member0 rule (setq l1 (assq (op-of (lhs rule)) $op_rules)))
	 (delete0 rule l1))
	((member0 rule (setq l1 (assq (op-of (lhs rule)) $cycle-op-rules)))
	 (delete0 rule l1)))

  (if* $ac (remove-pairs-with rule)) ;;***why was this franz-dep??****;;

  ; clean $condi-dominate-rules.
  (setq $condi-dominate-rules (delete0 rule $condi-dominate-rules 1))

  ; clean $build-rules.
  (sloop for xa in $build-rules
	if (= (ruleno (third xa)) ruleno) 
	  do (setq $build-rules (delete0 xa $build-rules))))

(defun check-witness (rule &aux new)
  ; trace to reduce $witness-eqn using rule;
  ; if $witness-eqn is reducible, then normalize $witness-eqn;
  ; if $witness-eqn is normalized to nil, then report the success.
  (when (or (reduce-by-one-rule (lhs $witness-eqn) rule)
	    (reduce-by-one-rule (rhs $witness-eqn) rule))
    (setq new (if $induc 
		  (cover-normalize $witness-eqn)
		(checkeq-normal $witness-eqn)))
    (if new
	(setq $witness-eqn new)
      (found-witness (rhs $witness-eqn)))))

(defun flatten-witness (source)
  (setq $witness-eqn (flatten-eqn $witness-eqn))
  (when (equal (lhs $witness-eqn) (rhs $witness-eqn))
	(setq $used-rule-nums
	      (cons 'ac-op
		    (if* (eq (car source) 'deleted)
			(list (car source) (cadr source) (caddr source))
		      (list (car source) (cadr source)))))
	(found-witness (rhs $witness-eqn))))

(defun found-witness (term)
  (setq $used-rule-nums 
	(make-new-rule term term nil
		       (append (eqn-source $witness-eqn) $used-rule-nums))
	$witness-eqn nil)
  (*throw 'refuted '*witness*))
