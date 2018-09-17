(in-package "USER")

(defun run-kb-options ()
  ;  Lets the user set the flags and strategies used in Knuth-Bendix.
  (user-menu
;   (ackb "         Set ac-completion flags" (ac-kb-choice))
    (automatic "   Set automatic flag" (automatic-flag))
    (autoorder "   Set auto ordering flags" (auto-options))
    (brake "       Set limits of time, number and size of rule, etc." (brake-choice))
    (critical "    Set critical pair strategies" (crit-strategy-options))
    (fastkb "      Set options for removing unnecessary superpositions" 
	    (fastkb-choices))
    (fopc "        Set strategy to process propositions" (fopc-stra))
    (instance "    Set instantiating flag" (instant-choice))
    (list "        Show current system" (display) (setq failed t)) 
    ;; stay here after listing
    (norm "        Set normalization strategies" (norm-strategy))
    (operator "    Set operator precedence or status" (operator-options))
    (order "       Set the ordering for ensuring termination of rewrite rules."
	   (order-str))
    (postpone "    Set strategies for postponine equations" (post-posi-stra))
    (prove "       Set proof methods" (proof-methods))
    (reduce "      Reduce system" (reduce-system-str))
    (trace "       Set trace options" (trace-options))
    (type "        Set relation between types" (ext-type-relation))
))

(defun crit-strategy-options ()
  ;  Lets the user set the strategies relating to critical pairs and rules.
  (user-menu
   (deleted "     Set strategy for processing deleted rules." (im-del-rules))
   (unmarked "    Set strategy for organizing unmarked rules." (unmarked-rules-strat))
   (marked "      Set strategy for organizing marked rules." (marked-rules-strat))
   ;;    (paramodu "    Set flag for paramodulation." (paramod-str))
   (pick "        Set strategy for picking a rule for superposition." (pick-strategy))
   (input "       Set the input-superposition strategy" (input-superpose-stra))
   (unit "        Set the unit-superposition strategy" (unit-superpose-stra))
   (restrict "    Set restrictions on making superpositions." (restrict-superpose-stra))
   (rulesize "    Specify a measure for the size of rules." (size-depth-str))
   (with "        Set strategies for choosing the second rule(s) for superposition."
	 (with-strategy))
   ))

(defun operator-options ()
  ;  Lets the user set the ordering on operators.
  (user-menu
   (acoperator "  Declare operators to be associative and commutative." 
		   (ext-operator 'ac))
   (commutative " Declare operators to be commutative." 
		(ext-operator 'commutative))
   (constructor " Declare operators to be constructor." 
		(ext-operator 'constructors))
   (display "     Display precedence and status of operators for ordering."
		(display-op-stats) (setq failed t))
   (cancellation "Declare operators to satisify the cancellation law." 
		(ext-operator 'divisible))
   (equivalence " Specify operators whose precedence is equivalent."
		(ext-equivalence)) 
   (precedence "  Specify precedence on operators for ordering."
		(ext-precedence))
   ;;(quit "         Quit to top level." nil)
   (skolem "      Specify skolem functions for igoring its arguments." (ext-operator 'skolem))
   (status "      Specify the status of an operator for ordering." (ext-status))
   (weight "      Specify the weight of functions for computing rulesize." 
		(ext-weight))))

(defun automatic-flag ()
  (ask-choice $automatic '(nil t) "Set the automatic flag or not: ")
  (when $automatic (setq $trace-flag 2) (set-automatic-flags)))

(defun reduce-system-str ()
  (ask-choice $reduce-system '(0 1 2 3)
"Do not reduce system (0), only lhs (1), plus condition (2), rhs, too (3): "))

(defun order-str ()
  (ask-choice $ordering '(m l s d)
"Orient by hand (m), or by lrpo (l) or by size (s) or by depth (d) ?"))

(defun proof-methods ()
  (ask-choice $prove-method '(b f h k)
'(  "Following methods are available:"
    "  Deduction:"
    "     (b) refutation        --- using boolean-ring method"
;    "     (c) refutation        --- using clause representation"
    "     (f) forward reasoning --- putting the conjecture aside"
    "     (h) completion        --- using discrimination tree techniques"
    "     (k) completion        --- using the standard Knuth-Bendix procedure"
;    "  Induction:"
;    "     (e) explicit          --- using the cover-set method"
;    "     (s) inductionless     --- using the test set method"
;    "     (g) inductionless     --- using the ground-reducibility method"
    "Please make your choice: "))
  (case $prove-method
    (f (setq $condi nil $trace-proof t $keep-deleted-rules t $reduce-system 2))
    (h (setq $condi nil $trace-proof nil $prove-method 'q $kb '*distree*)
       (if (< $del-rule-str 2) (setq $del-rule-str 2)))
    (k (setq $condi nil $trace-proof nil $prove-method 'q $kb '*pure*))
    (c (setq $condi 'c  $trace-proof t $reduce-system 2 
	     $over-rewrite 1)
       (terpri)
       (princ "The maximal depth of conditional rewriting is set to 1.")
       (terpri))
    ;;(e (setq $condi 'i  $trace-proof t $reduce-system 2))
    ;;(g (setq $condi nil $trace-proof nil $prove-method 'q))
    (t (setq $condi nil $trace-proof nil $prove-method 's $kb '*pure*))))

(defun trace-options ()
  (ask-choice $trace-flag '(1 2 3 4)
      "Use normal trace (3), or extended trace (4), or less trace (1,2) ?"))

(defun with-strategy ()
  ; Sets critical-pair strategy by updating the flag $CRIT-with-STR.
  ; (Called by CRIT-STRATEGY-OPTIONS.)
  (ask-choice $crit-with-str '(m o a) 
"Compute critical pairs with marked (m), or older (o), or all (a) rules."))

(defun pick-strategy (&aux (old $pick-rule-str))
  (ask-choice $pick-rule-str '(e l f m)
      (list  "Pick earliest smallest (e) or latest smallest (l) or first (f) "
        "  or manually chosen (m) unmarked rule?"))
  (if* (eq $pick-rule-str 'm) then
     (if* (ok-to-continue
	    "When choosing the second rule, do you want to display them ? ")
         then (setq $crit-with-str 'h1)
         else (setq $crit-with-str 'h2))
     elseif (eq old 'm)
     then (setq $crit-with-str 'a)))

(defun unmarked-rules-strat ()
  ;  Sets discipline of marked rules by updating the flag MARK-RULE.
  (ask-choice $unmark-rule-str '(q l)
"Organize the unmarked rules as queue (q), or sorted list (l) ?"))

(defun marked-rules-strat ()
  ;  Sets discipline of marked rules by updating the flag MARK-RULE.
  (ask-choice $mark-rule-str '(s q l)
"Organize the marked rules as stack (s), queue (q), or sorted list (l) ?"))

(defun im-del-rules ()
  ;  Sets deleted rules strategy by updating the flag $DEL-RULE-STR.
  ;            (Called by CRIT-STRATEGY-OPTIONS.)
  (ask-choice $del-rule-str '(1 2 3 4) (list 
"Process a deleted rule at once (1), or after a rule is added completely (2),"
"or after the superposition process (3), or after sorting deleted rules "
"in addition to case 3 (4)."
))
  (when (and (< $del-rule-str 2) (eq $kb '*distree*))
    (princ 
"WARNING: the strategy is set to 2 because the discrimination tree is in use."
    )
    (terpri)
    (setq $del-rule-str 2)))

(defun fopc-stra ()
  (user-menu
   (break-ass "    Specify how big assertions should be broken down." 
	      (break-ass-str))
   (bound "        Give a bound on number of rules made from critical pairs."
	      (ass-rule-bound))
   (restrict "     Set restrictions on making superpositions." (restrict-superpose-stra))
   (list "         Set strategy for organizing formulas." (post-ass-list))
   (match "        Set strategy for boolean matching." (bool-match-str))
;   (paramodulate " Set flag for paramodulate." (paramod-str))
;   (quit "         Quit to top level." nil)
   ))

#|
(defun paramod-str ()
  (ask-choice $paramodulate '(y n)
	      "Use paramodulation (y) or not (fast & incomplete) (n) ?"))
|#

(defun bool-match-str ()
  (ask-choice $fast-match '(1 2)
"Use set matching (1) or sequence match (fast & incomplete) (2) ?"))

(defun post-ass-list ()
  (ask-choice $post-ass-list '(s q l)
	      "Organize assertions as stack (s) queue (q) or sorted list (l) ?"))

(defun crit-pair-process ()
  (ask-choice $post-ass-list '(s q l)
	      (list "Process critcal pairs after (q), inside (l) unification or"
		    "after superposition (l) ?")))

(defun break-ass-str ()
  (ask-choice $more-break '(m l n) 
	      "Break more assertions (m), or less (l) or none (n) ?" ))

(defun ass-rule-bound ()
  (ask-number $immediate
	      "What is the bound of number of rules made in one section ?"))

(defun restrict-superpose-stra ()
  (user-menu
   (idem "        Set the idempotent superposition strategy" (idem-superpose-stra))
   (input "       Set the input-superposition strategy" (input-superpose-stra))
   (one "         Set the one's rule superposition strategy" (one-superpose-stra))
   (unit "        Set the unit-superposition strategy" (unit-superpose-stra))
   ))

(defun one-superpose-stra ()
  (ask-choice $one-superpose '(t nil)
	      "Set the one's rule superposition strategy on or off? "))

(defun input-superpose-stra ()
  (ask-choice $input-superpose '(t nil)
	      "Set the input-superposition strategy on or off? "))

(defun unit-superpose-stra ()
  (ask-choice $unit-superpose '(t nil)
	      "Set the unit-superposition strategy on or off? "))

(defun idem-superpose-stra ()
  (ask-choice $idem-superpose '(t nil)
	      "Superpose a rule with (t) or without itself (nil) ?"
	      ))

(defun size-depth-str ()
  (ask-choice $rule-size '(s d w l o)
  (list "Set the size of a rule to be the size (s), or the depth (d), or the"
	"   weighted size (w), or the number of literals (l) of its lhs, "
        "   or the optimal (i.e., 2*lhs + 1*rhs) (o) ?"
	))
  (if (eq $rule-size 'd) (setq $ex1 5 $ex2 10)))

(defun over-rewrite-premises ()
  ; Decide what is the number of over-rewrite premises.
  (ask-number $over-rewrite
	      "What is the maximal depth of conditional rewriting ? "))

(defun norm-strategy ()
  ;  Sets normalization strategy by updating the flag $NORM-STR.
  ;            (Called by RUN-KB-OPTIONS.)
  (terpri)
  (princ "The options are available only for unconditional rewriting") (terpri)
  (princ "    modulo an empty set of equations") (terpri)
  (if* (not (or $condi $ac $commutative)) then
    (ask-choice $norm-str '(i e o m)
(list "Set normalization strategy to innermost (i), efficient innermost (e),"
" outermost (o) or efficient outermost (or mixed) (m) ? " ))))

(defun ext-precedence ()
  ; Sets the precedence relation between two operators specified by
  ; the user by updating $GLOB-PREC.
  (when (io-eoln $in-port) 
    (princ "Type operators in decreasing precedence") (terpri)
    (princ "  (eg. 'i * e' to set i > * > e) ") (terpri)
    (princ "--> "))
  (let ((op1 (read-atom 'noend)) 
	ops2 op2 o1 o2)
    (if* (setq o1 (get-op-id op1))
	 then
	 (setq ops2 (progn (if (io-eoln $in-port) 
			       (princ (uconcat op1 " > operators ? ")))
			   (read-args)))
	 (sloop for op2 in ops2 
		for o2 = (get-op-id op2) do
		(unless o2 
		  (princ (uconcat
			   op2 ": unknown operator, precedence not set."))
		  (terpri)
		  (return (setq ops2 nil))))
	 else 
	 (princ (uconcat op1 ": unknown operator, precedence not set."))
	 (terpri))

    (terpri $out-port)
    (setq op2 op1 o2 o1)
    (while ops2
      (setq op1 op2
	    o1 o2
	    op2 (pop ops2)
	    o2 (get-op-id op2))
      (if* (is-prec-related o1 o2)
	   then
	   (format $out-port "Precedence relation between ~s and ~s exists.~%" op1 op2)
	   else
	   (format $out-port "Precedence relation, ~s > ~s, is added.~%" op1 op2)
	   (add-sugg o1 o2))
      )
    ))

(defun ext-weight (&aux pairs op w i)
  ; set the weigth of some operators.
  (if* (io-eoln $in-port) then
      (princ "Type each operator followed by its weight (the default weight is 1)." $out-port) 
      (terpri $out-port)
      (princ "  (eg. 'i 2 * 4' to set weigth(i) = 2, weight(*) = 4." $out-port)
      (terpri $out-port)
      (princ "--> " $out-port))
  (setq pairs (read-args))
  (sloop while pairs do
    (setq op (pop pairs))
    (when (setq i (get-op-id op)) 
      (setq w (read-from-string (pop pairs)))
      (if* (not (numberp w))
	   (setq w  (let () 
		      (princ (uconcat op ": what is its weight ? " $out-port)) 
		      (ask-a-number))))
      (push (cons i w) $f-weights))))

(defun ext-status ()
  ;; Sets the status for an operator and updates relevant info.
  ;; Return t iff some operator gets a status.
  (when (io-eoln $in-port)
    (princ "Type operator you wish to set status for: "))
  (let ((op (read-atom 'end)) o)
    (if* (setq o (get-op-id op))
        then 
	(if* (op-has-status o)
	     then (princ "Status exists already, sorry.") (terpri)
	     elseif (sloop for op1 in (ops-equiv-to o) thereis
			   (commutativep op1))
	     then 
	     (princ "It's commutative, or its equivalent operators")
	     (princ " are commutative, sorry.") (terpri) 
	     else
	     (user-menu
	       (lr "          Left-to-right" (set-op-status o 'lr))
	       (rl "          Right-to-left" (set-op-status o 'rl)))
	     (format $out-port "The status of ~s is set to ~s.~%" 
		     op (get-op-status-name o))
	     t)
 	else 
	(princ (uconcat "Sorry, the operator is not known: " op))
	(terpri))))

(defun add-status (op status)
  ;  Add STATUS to the equivalent class of OP. 
  (sloop for oper in (ops-equiv-to op) do (set-op-status oper status))
  (if* (ok-prev-rules op) then t
       else (sloop for oper in (ops-equiv-to op) do
		   (rem-op-status oper))
       nil))

(defun ext-operator (status &aux flag opid)
  ; Sets the STATUS status for a list of operator and updates relevant info.
  (if (io-eoln $in-port)
    (format $out-port "Type operators you wish to be ~s : " status))
  (dolist (op (read-args))
    (setq opid (get-op-id op))
    (if opid
	(setq flag (or (case status
			 (constructors (ext-constructor opid))
			 (divisible   (ext-divisible opid))
			 (skolem      (ext-skolem opid))
			 (commutative (ext-commutative opid))
			 (ac          (ext-ac opid)))
		       flag))
	(progn
	  (format t "Sorry, that operator is not known: ~s~%" op)
	  (format t "You may input it as [~s : type -> type] using `Add'.~%" op))))

  (when (and flag (eq status 'constructor))
	(display-constructors $type-constructors))
  (when flag
    (case status
      (commutative (flatten-everything (car $commutative) 'c-permutation))
      (ac          (flatten-everything (car $ac)))))
  flag)

(defun ext-constructor (op)
  (when (not (constructorp op)) 
    (set-constructor op)
    (if (multi-typed)
	(add-associate-list (get-op-type op) op $type-constructors))
    (if* (is-constant-op op)
	 then (push op $free-constructors)
	 elseif (and (not (assoc op $op-rules))
		     (ok-to-continue
		       (uconcat "Is '" (op-name op) "' a free constructor? ")))
	 then (push op $free-constructors))
    t))

(defun ext-divisible (op &aux l1 l2 constants names) 
  (if* (neq (get-arity op) 2) 
      then (terpri) (princ "Only binary operators are accepted.") (terpri)
      elseif (assoc op $divisible) 
      then (terpri $out-port) 
      (princ "This operator has the property." $out-port) (terpri $out-port)
      else
      (terpri $out-port) 
      (setq constants (get-constants (every-ops)))
      (setq names (sloop for xa in constants 
			 collect (read-from-string (op-name xa))))

      (if* (ok-to-continue (uconcat "Does '" (op-name op)
				    "' have the identity function? "))
	   then
	  (if* (cdr constants)
	      then 
	      (ask-choice l1 names "Please type it: ")
	      (sloop for xa in constants for xb in names 
		     if (eq l1 xb) return (setq l1 xa)
		     finally (setq l1 nil))
	      else
	      (princ (uconcat "I assume it is '" (op-name (car constants)) "'.") $out-port) 
	      (terpri $out-port)
	      (setq l1 (car constants))))

      (if* (and $instant
		(ok-to-continue
		  (uconcat "Does the '" (op-name op)
			   "' have the exception for cancellation ? "))) 
	   then
	   (if* (cdr constants)
		then 
		(ask-choice l2 names "Please type it: ")
		(sloop for xa in constants for xb in names 
		       if (eq l2 xb) return (setq l2 xa)
		       finally (setq l2 nil))
		else 
		(princ (uconcat "I assume it is '" (op-name (car constants)) "'.") $out-port) 
		(terpri $out-port)
		(setq l2 (car constants))))

      (push (list op l2 l1) $divisible)))

(defun ext-skolem (op)
  (unless (memq op $skolem-ops)
	  (format $out-port "~s is a Skolem operator now.~%" (op-name op)) 
	  (push op $skolem-ops)))

(defun ext-commutative (op)
  (unless (or (memq op $commutative) (memq op $ac))
    (if (op-has-status op) (cancel-status op))
    (format $out-port "~%The operator ~s is commutative.~%" (op-name op)) 
    (sys-flag-init)
    (set-commutative op)))

(defun ext-ac (op)
  (unless (memq op $ac)
    (if (op-has-status op) (cancel-status op))
    (format $out-port
	    "~%The operator ~s is associative & commutative (AC).~%" (op-name op)) 
    (init-ac-arrays)
    (sys-flag-init)
    (setq $norm-str 'o
	  $block-cps 0)
    (push op $ac)))

; The following functions are used to add an equivalence relation
; between two operators in the precednce relation. This needs us to

(defun ext-equivalence ()
  ; modifies: $eqop-list $precedence
  ; Adds an equivalence relation between two operators in the
  ; precedence relation.
  ; $GLOB-PREC and $EQOP-LIST have to be updated after checking consistency
  ; of the status and equivalence.
  (if* (io-eoln $in-port)
      then (princ "Type the two operators you wish to make equivalent" $out-port)
           (terpri $out-port) (princ "separated by a blank: ") $out-port)
  (let ((op1 (read-atom 'noend)) op2)
    (setq op2 (progn (when (io-eoln $in-port) 
		       (princ "Type second operator: "))
                     (read-atom 'end)))
    (if* (not (and (setq op1 (get-op-id op1)) (setq op2 (get-op-id op2))))
	 then (princ "Sorry, operators are not in the current system.") (terpri)
	 elseif (eqops op1 op2) 
	 then (princ "Already equivalent." $out-port) (terpri $out-port)
	 elseif (is-prec-related op1 op2)
	 then (princ "Sorry, inconsistent equivalence.") (terpri)
	 else (now-make-equi op1 op2))))

(defun now-make-equi (o1 o2)
  ;  Check the status of OP1 and OP2. Try to make OP1 and OP2 to be 
  ;            equivalent and consistent with their status. 
  (let ((s1 (op-has-status o1)) 
	(s2 (op-has-status o2))
	(op1 (op-name o1)) 
	(op2 (op-name o2)))
    (cond ((and s1 s2) 
           (if* (eq s1 s2) then
		(princ (uconcat op1 " and " 
				op2 " made equivalent.") $out-port) 
		(terpri $out-port)
		(add-equ o1 o2)
		else
		(princ "Operators have opposite status, sorry.") (terpri)))
          (s1 (if* (have-common (ops-equiv-to o2) $commutative)
		   then (princ (uconcat op1 " has status while " op2
			" is commutative or equivalent to commutative ones.")
			       $out-port)
		   (terpri $out-port)
		   else 
		   (warn-stat op1 o1 o2)
		   (add-equ o1 o2)))
          (s2 (if* (have-common (ops-equiv-to o1) $commutative)
		   then (princ (uconcat op2 " has status while " op1
			"is commutative or equivalent to commutative ones.")
			       $out-port) 
		   (terpri $out-port)
		   else 
		   (warn-stat op2 o2 o1)
		   (add-equ o2 o1)))
	  (t (princ (uconcat op1 " and " op2 " made equivalent.") $out-port)
	     (terpri $out-port)
             (add-equ o1 o2)))))

(defun add-equ (op1 op2)
  ; Local function.  Called by EXT-EQUIV.
  ; Does the actual adding of the relation OP1 equivalent to OP2.
  (let ((eqs1 (ops-equiv-to op1)) (eqs2 (ops-equiv-to op2)))
    (if* (equal eqs1 (ncons op1))
      then
      (if* (equal eqs2 (ncons op2)) 
	   then (push (list op1 op2) $eqop-list)
	   else (add-at-end eqs2 op1))
      else 
      (if* (equal eqs2 (ncons op2)) 
	   then (add-at-end eqs1 op2)
	   else (setq $eqop-list (delete0 eqs1 (delete0 eqs2 $eqop-list)))
	   (push (append eqs1 eqs2) $eqop-list)))
    (setq eqs1 (assoc op1 $precedence)
          eqs2 (assoc op2 $precedence)) 
    (if* eqs1 then
	 (rplacd eqs1 (union (cdr eqs1) (cdr eqs2)))
	 (update-by-eq op1)
	 elseif eqs2 
	 then (update-by-eq op2))
    
    (sloop for xa in $precedence do
	   (if* (or (eq (car xa) op1) (eq (car xa) op2)) then ()
		elseif (member op1 xa) then (add-at-end xa op2)
		elseif (member op2 xa) then (add-at-end xa op1)))
    t))

(defun warn-stat (name1 op1 op2 &aux status)
  ; Local function.  Called by EXT-EQUIV when making OP1 equivalent to OP2 to
  ;                      ensure that they have consistent status.
  (format $out-port "Operator, ~s, has status: ~s"  
	  name1 (setq status (get-op-status-name op1)))
  (terpri $out-port)
  (sloop for op in (ops-equiv-to op2) do
    (princ (uconcat "Operator, " (op-name op) ", being given same status.")
	   $out-port) 
    (terpri $out-port)
    (set-op-status op status)))

(defun fastkb-choices ()
  (user-menu
   (blocking "    Set blocking critcal pair checking" (block-choice))
;    (composite "Set left-composite critical pair checking" 
;		    (prime-choice))
;    (left-composite "Set left-composite critical pair checking" 
;		    (left-prime-choice))
   (polynomial "  Set polynomial processing option" (poly-choice))
   (prime-acu "   Set flag for checking prime ac unifiers." 
	       (prime-acu-choice))
;   (quit "        Quit fast kb option setting" nil)
    (restrict "   Set restrictions on making superpositions." (restrict-superpose-stra))
    (symmetry "   Set symmetry flag for critcal pairs" (symmetry-choice))))

(defun prime-choice ()
  (ask-choice $prime-cps '(t nil)
  "Set prime/composite critical pair checking on or off? " )
  (if $prime-cps (setq $prime-cps 0)))

(defun left-prime-choice ()
  (ask-choice $left-cps '(t nil)
  "Set left-composite critical pair checking on or off? " )
  (if $left-cps (setq $left-cps 0)))

(defun block-choice ()
  (ask-choice $block-cps '(t nil)
  "Set blocking flag on or off (good for AC operators)? " )
  (if $block-cps (setq $block-cps 0)))

(defun symmetry-choice ()
  (ask-choice $symmetry-check '(nil t)
    "Set flag for checking symmetry relation (good for AC operators)? " ))

(defun prime-acu-choice ()
  (ask-choice $prime-acu '(nil t)
	      "Set flag for checking prime/composite AC unifiers or not? " )
  (setq $top-only-var-check $prime-acu))

(defun instant-choice ()
  (ask-choice $instant '(t nil)
	      "Make instances of non-terminating or big rules ? " ))

(defun poly-choice ()
  (ask-choice $polynomial '(t nil)
	      (list 
  "Set the polynomial flag on means that the following axioms are built in:"
  "             x + y == y + x               z * (x + y) == (z * x) + (z * y)"
  "       (x + y) + z == x + (y + z)         (x + y) * z == (x * z) + (y * z)"
  "             x + 0 == x    "
  "Do you want to set it ? " ))
  (if $polynomial 
      (poly-initialize)
      (format t "~%You should re-initialize RRL.~%"))
  (terpri))

(defun brake-choice ()
  ; >>>>> 1/16/89
  (user-menu 
   (deleted "     Set the option for keep in deleted rules." (keep-deleted-rules-stra))
   (depth "       Set depth of conditional rewriting" (over-rewrite-premises))
   (discard "     Discard big equations" (discard-eqn-stra))
   (normalize "   Set maximal rewritings in a normalization" (normalize-bound))
   (postpone "    Set the maximal number of postponed equations." (post-limit-stra))
   (rules "       Set the maximal size of the system." (new-rule-stra))
   (runtime "     Set the limit of run time." (time-limit-stra))
   (superpose "   Set restrictions on making superpositions." (restrict-superpose-stra))
   ))

(defun discard-eqn-stra ()
  (user-menu
   (size "        Set the maximal size of an equation" (maximal-eqn-size-stra))
   (depth "       Set the maximal depth of an equation" (maximal-eqn-depth-stra))
   (degree "      Set the maximal degree of an equation" (maximal-eqn-degree-stra))
   ))

(defun maximal-eqn-size-stra ()
  (ask-number $discard-eqn-max-size
	      "What is the limit of the size of an equation ? ")
  (setq $discard-poly-max-size (* 4 $discard-eqn-max-size)
	$discard-eqn-2max-size (* 2 $discard-eqn-max-size)
	))

(defun maximal-eqn-depth-stra ()
  (ask-number $discard-eqn-max-depth
	      "What is the limit of the depth of an equation ? "))

(defun maximal-eqn-degree-stra ()
  (ask-number $discard-eqn-max-degree
	      "What is the limit of the degree of an equation ? "))

(defun time-limit-stra ()
  (ask-number $runtime-max
	      "What is the limit of run time ? "))

(defun normalize-bound ()
  (ask-number $reduce-max
	      "How many of rewritings in a normalization (0 = unlimited)? "))

(defun keep-deleted-rules-stra ()
  (ask-choice $keep-deleted-rules '(t nil)
	      "Keep the deleted rules in the system ?"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun auto-options ()
  ;  Lets the user set the strategies relating to critical pairs and rules.
  (user-menu 
   (eq-pre "      Set priority of inequivalence or equivalence relation."
                 (eq-pre-strat) (setq failed t)) 
   (lr-rl "       Set priority to left-right or right-left status"
                 (lr-rl-strategy) (setq failed t)) 
   (new-oper "    Set new operator introducing stratedgy." 
		(operator-stra) (setq failed t)) 
   (postpone "    Set postponing equation strategy." 
		(post-posi-stra) (setq failed t)) 
   (post-limit "  Set the limit of postponed equations." 
		  (post-limit-stra) (setq failed t)) 
   (rule-limit "  Set the limit of increasing size of the system."
	       (new-rule-stra) (setq failed t)) 
   ))

(defun operator-stra ()
  (ask-choice $newop-first '(1 2)
"Introduce a new operator as posssible (1), or when really needed (2) ?"))

(defun eq-pre-strat ()
  (ask-choice $pre-first '(1 2)
     "Equivalence relation first (1), or inequivalence relation first (2) ?"))

(defun new-rule-stra ()
  (ask-number $newrule-max
	      "What is the limit of new rules under a new precedence ? "))

(defun post-posi-stra ()
  (ask-choice $post-posi '(1 2 3) 
  (list "Postpone an equation before precedence suggestion (1), "
        "  or after precedence suggestion and before status suggestion (2)"
        "  or after status suggestion (3) ?")))

(defun lr-rl-strategy ()
  (ask-choice $rl-first '(1 2)
	      "left-to-right-status first (1), or rl-status first (2) ?"))

(defun arity-eq-strategy ()
  (ask-choice $eq-arity '(t nil)
       "Operators with the same arity can be equivalent or not ?"))

(defun post-limit-stra ()
  (ask-number $post-max
	      "What is the maximum number of postponed equations ?"))
