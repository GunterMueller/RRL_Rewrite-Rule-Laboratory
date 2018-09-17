;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

(defun run-kb-options ()
  ;  Lets the user set the flags and strategies used in Knuth-Bendix.
  (user-selectq
    (ackb "Set ac-completion flags" (ac-kb-choice))
    (autoorder "Set auto ordering flags" (auto-options))
    (brake "Set limits of time, number and size of rule, etc." (brake-choice))
    (critical "Set critical pair strategies" (crit-strategy-options))
    (cycle "Set cycle-rule flag for reduction" (cycle-choice)) 
    (fastkb "Set options for removing unnecessary superpositions" 
	    (fastkb-choices))
    (fopc "Set strategy to process propositions" (fopc-stra))
    (history "Set strategy to save RRL states into the history stack" 
	     (undo-strategy))
    (list  "Show current system" (display) (setq failed t)) 
					;stay here after listing
    (manualorder "Set manual ordering option" (manual-options))
    (norm "Set normalization strategies" (norm-strategy))
    (operator "Set operator precedence or status" (operator-options))
    (order "Choose the ordering for ensuring termination of rewrite rules."
	   (order-str))
    (prove "Set proof methods" (proof-methods))
    (quit  "Return to rrl" nil)
    (reduce "Reduce system" (reduce-system-str))
    (instance "Set instantiating flag" (instant-choice))
    (support "Declare set of support" (support-eqn))
    (trace "Set trace options" (trace-options))
    (type "Set relation between types" (ext-type-relation))
))

(defun undo-strategy ()
  (user-selectq
    (no-history "No states will be saved in the history; undo will be useless."
		(setq $no-history t))
    (history "Save states into the history to allow to do undo." 
	     (setq $no-history nil))
    (quit "Quit setting strategy" nil)))

(defun crit-strategy-options ()
  ;  Lets the user set the strategies relating to critical pairs and rules.
  (user-selectq
    (delete     "Set strategy for processing deleted rules." (im-del-rules))
    (organize   "Set strategy for organizing marked rules." (int-rule-strat))
    (paramodulation "Set flag for paramodulation." (paramod-str))
    (pick       "Set strategy for picking a rule for superposition." 
		(pick-strategy))
    (quit       "Quit." nil)
    (restrict  "Set restrictions on making superpositions."
	       (restrict-crit-stra))
    (rulesize   "Specify a measure for the size of rules." (size-depth-str))
    (with  "Set strategies for choosing the second rule(s) for superposition."
		(with-strategy))
))

(defun operator-options ()
  ;  Lets the user set the ordering on operators.
  (user-selectq
   (acoperator  "Declare operators to be associative and commutative." 
		(ext-operator 'ac))
   (commutative "Declare operators to be commutative." 
		(ext-operator 'commutative))
   (constructor "Declare operators to be constructor." 
		(ext-operator 'constructors))
   (display     "Display precedence and status of operators for ordering."
		(display-op-stats) (setq failed t))
   (divisible   "Declare operators to be left- or right-divisible." 
		(ext-operator 'divisible))
   (equivalence "Specify operators whose precedence is equivalent."
		(ext-equivalence)) 
   (precedence  "Specify precedence on operators for ordering."
		(ext-precedence))
   (quit        "Quit to top level." nil)
   (status      "Specify the status of an operator for ordering." (ext-status))
   (transitive  "Declare operators to be transitive." 
		(ext-operator 'transitive))
   (weight      "Specify the weight of functions for computing rulesize." 
		(ext-weight))))

(defun reduce-system-str ()
  (ask-choice $reduce-system '(0 1 2 3)
"Do not reduce system (0), only lhs (1), plus condition (2), rhs, too (3): "))

(defun order-str ()
  (ask-choice $ordering '(m l s d)
    "Orient by hand (m), or by lrpo (l) or by size (s) or by depth (d) ?")
  (if (eq $ordering 'm) (initialize-manual-ordering)))

(defun manual-options ()
  (ask-number $manual-history-frequency
"Set frequency for saving history of manual ordering decisions"
" (0 means always save history)")
  (setq $manual-history-number 0))

(defun print-warning ()
  (terpri) 
  (princ "Orientation of equations being done manually.") (terpri) (terpri)
  (princ "!!!!!! Warning: Rewriting may not terminate !!!!") (terpri)
  (princ "!!!!!! Warning: Resulting system will be locally-confluent;") 
  (terpri) (princ "         But it may not be canonical  !!!!")
  (terpri) (terpri))

(defun proof-methods ()
  (ask-choice $prove-method '(f c e s g)
    "Following methods are available:"
    "  Deduction:"
    "     (f) forward reasoning --- using completion"
    "     (s) refutation        --- using boolean-ring method"
    "     (c) refutation        --- using conditional rules"
    "  Induction:"
    "     (e) explicit          --- using the cover-set method"
    "     (s) inductionless     --- using the test set method"
    "     (g) inductionless     --- using the ground-reducibility method"
    "Please make your choice: ")
  (caseq $prove-method
    (e (setq $induc 'i  $trace-proof t $reduce-system 1))
    (c (setq $induc 'c  $trace-proof t $reduce-system 2 
	     $over-rewrite 1)
       (terpri)
       (princ "The maximal depth of conditional rewriting is set to 1.")
       (terpri))
    (f (setq $induc nil $trace-proof t))
    (g (setq $induc nil $trace-proof nil $prove-method 'q))
    (t (setq $induc nil $trace-proof nil $prove-method 's))))

(defun trace-options ()
  (ask-choice $trace_flag '(1 2 3)
      "Use normal trace (2), or extended trace (3), or off trace (1) ?"))

(defun with-strategy ()
  ; Sets critical-pair strategy by updating the flag $CRIT-with-STR.
  ; (Called by CRIT-STRATEGY-OPTIONS.)
  (ask-choice $crit-with-str '(m o a) 
"Compute critical pairs with marked rules (m) or older rules (o) or all (a)"))

(defun pick-strategy (&aux (old $pick-rule-str))
  (ask-choice $pick-rule-str '(e l f m)
        "Pick earliest smallest (e) or latest smallest (l) or first (f) "
        "  or manually chosen (m) unmarked rule?")
  (if (eq $pick-rule-str 'm) then
     (if (ok-to-continue
           "When choosing the second rule, do you want to display them ? ")
         then (setq $crit-with-str 'h1)
         else (setq $crit-with-str 'h2))
     elseif (eq old 'm)
     then (setq $crit-with-str 'a)))

(defun int-rule-strat ()
  ;  Sets discipline of marked rules by updating the flag MARK_RULE.
  ;            (Called by CRIT-STRATEGY-OPTIONS.)
  (ask-choice $mark_rule_str '(s q l)
 "Organize the marked rules as stack (s), queue (q), or sorted list (l) ?"))

(defun im-del-rules ()
  ;  Sets deleted rules strategy by updating the flag $DEL_RULE_STR.
  ;            (Called by CRIT-STRATEGY-OPTIONS.)
  (ask-choice $del_rule_str '(1 2 3) 
"Process a deleted rule at once (1), or all deleted rules together (2), or "
"after the superposition process (3)"))

(defun fopc-stra ()
  (user-selectq
   (break-ass "Specify how big assertions should be broken down." 
	      (break-ass-str))
   (bound     "Give a bound on number of rules made from critical pairs."
	      (ass-rule-bound))
   (restrict  "Set restrictions on making superpositions."
	      (restrict-crit-stra))
   (list      "Set strategy for organizing formulas." (post-ass-list))
   (match     "Set strategy for boolean matching." (bool-match-str))
   (paramodulation "Set flag for paramodulate." (paramod-str))
   (quit      "Quit to top level." nil)))

(defun paramod-str ()
  (ask-choice $paramodulate '(y n)
	      "Use paramodulation (y) or not (fast & incomplete) (n) ?"))

(defun bool-match-str ()
  (ask-choice $fast-match '(1 2)
"Use set matching (1) or sequence match (fast & incomplete) (2) ?"))

(defun post-ass-list ()
  (ask-choice $post-ass-list '(s q l)
     "Organize assertions as stack (s) queue (q) or sorted list (l) ?"))

(defun crit-pair-process ()
  (ask-choice $post-ass-list '(s q l)
	      "Process critcal pairs after (q), inside (l) unification or"
	      "after superposition (l) ?"))

(defun break-ass-str ()
  (ask-choice $more-break '(m l n) 
        "Break more assertions (m), or less (l) or none (n) ?" ))

(defun ass-rule-bound ()
  (ask-number $immediate
	      "What is the bound of number of rules made in one section ?"))

;; >>>>>> 1/18/89
(defun restrict-crit-stra ()
  (ask-choice $idem '(1 2 3 4)
"Superposing with any rules (1), without itself (2), with unit rules (3),"
"    or with input rules (4) ?"
 ))

(defun size-depth-str ()
  (ask-choice $rule-size '(s d l u)
        "Is the size of rule the size (s), or the depth (d)"
        "  or the number of literals (l) of lhs?")
  (if (eq $rule-size 'd) (setq $ex1 5 $ex2 10)))

(defun over-rewrite-premises ()
  ; Decide what is the number of over-rewrite premises.
  (ask-number $over-rewrite
	      "What is the maximal depth of conditional rewriting ? "))

(defun norm-strategy ()
  ;  Sets normalization strategy by updating the flag $NORM_STR.
  ;            (Called by RUN-KB-OPTIONS.)
  (terpri)
  (princ "The options are available only for unconditional rewriting") (terpri)
  (princ "    modulo an empty set of equations") (terpri)
  (if (not (or $induc $ckb_flag $ac $commutative)) then
    (ask-choice $norm_str '(i e o m)
"Set normalization strategy to innermost (i), efficient innermost (e),"
" outermost (o) or efficient outermost (or mixed) (m) ? " )))

(defun ext-precedence ()
  ; Sets the precedence relation between two operators specified by
  ; the user by updating $GLOB_PREC.
  (if (is-empty-line $in-port)
      then (princ "Type operators in decreasing precedence") (terpri)
           (princ "  (eg. 'i * e' to set i > * > e) ") (terpri)
           (princ "--> "))
  (let ((flag t)  
         (op1 (read-atom 'noend)) 
         ops2)
    (setq ops2 (progn (if (is-empty-line $in-port) 
                       then (princ (uconcat op1 " > operators ? ")))
                      (read-args $in-port)))
    (if (member op1 $operlist) 
     then (loop for op2 in ops2 do 
             (if (not (member op2 $operlist)) then 
            (princ (uconcat op2 ": unknown operator, precedence not set."))
            (terpri)
            (setq flag nil)
           ))
      else  (princ (uconcat op1 ": unknown operator, precedence not set."))
            (terpri)
            (setq flag nil)
     )
     (if flag then 
         (loop for op2 in ops2 do
             (add-sugg op1 op2)
             (princ (uconcat "Precedence relation, " op1 " > " op2
                             ", is added.")) (terpri)
             (setq op1 op2)))))

(defun ext-weight (&aux pairs op w)
  ; set the weigth of some operators.
  (if (is-empty-line $in-port) then
      (princ "Type each operator followed by its weight (the default weight is 1).") 
      (terpri)
      (princ "  (eg. 'i 2 * 4' to set weigth(i) = 2, weight(*) = 4.") (terpri)
      (princ "--> "))
  (setq pairs (read-args $in-port))
  (loop while pairs do
    (setq op (pop pairs))
    (if (memq op $operlist) then
        (setq w (pop pairs))
        (if (not (numberp w))
            (setq w  (progn (princ (uconcat op ": what weigth ? ")) (ask-a-number 1))))
        (push (cons op w) $f-weights))))

(defun ext-status ()
  ; Sets the status for an operator and updates relevant info.
  (if (is-empty-line $in-port)
      then (princ "Type operator you wish to set status for: "))
  (let ((op (read-atom 'end)))
      (if (member op $operlist) 
        then (if (get op 'status)
		 then (princ "Status exists already, sorry.") (terpri)
	       elseif (loop for op1 in (ops-equiv-to op) thereis
			    (or (ac-op-p op1) (commutativep op1)))
		 then (princ "It's commutative, or its equivalent operators")
		      (princ " are commutative, sorry.") (terpri) 
		 else (user-selectq
			 (lr "Left-to-right" (add-status op 'lr))
			 (rl "Right-to-left" (add-status op 'rl)))) 
 	else (princ (uconcat "Sorry, that operator is not known to me: " op))
	     (terpri))))

(defun add-status (op status)
  ;  Add STATUS to the equivalent class of OP. 
  (loop for oper in (ops-equiv-to op) do
     (setq $st_list (cons oper $st_list))
     (putprop oper status 'status))
  (if (ok-prev-rules op) then t
      else (loop for oper in (ops-equiv-to op) do
	        (setq $st_list (cdr $st_list))
		(remprop oper 'status))
	    nil))

(defun ext-operator (status &aux flag)
  ; Sets the STATUS status for a list of operator and updates relevant info.
  (if (is-empty-line $in-port) then
    (princ (uconcat "Type operators you wish to be " status ": ")))
  (loop for op in (read-args $in-port) do 
     (if (not (is-valid-op op)) 
 	  then (princ (uconcat "'" op "' is not a valid operator.")) (terpri) 
	elseif (or (eq status `constructors) (memq op $operlist)) 
	  then (setq flag (or (caseq status
				     (constructors (ext-constructor op))
				     (divisible   (ext-divisible op))
				     (transitive  (ext-transitive op))
				     (commutative (ext-commutative op))
				     (ac          (ext-ac op)))
			      flag))
          else (princ (uconcat "Sorry, that operator is not known: " op))
	       (terpri)))

  (if (and flag (eq status 'constructor)) then
     (setq $sufficient nil)
     (display-constructors $type-constructors))
  flag)

(defun ext-constructor (op &aux l1)
  (if (not (constructorp op)) then
      (if (not (member op $operlist)) then
	  (setq l1 nil)
	  (ask-number l1 (uconcat "What is the arity of '" op "' ? "))
	  (push op $operlist) 
	  (set-arity op l1))
      (if (get-arity2 op) 
	  then (setq l1 (get-domain-type op)) 
	  else
	  (princ (uconcat "Warning: '" op "' is untyped.")) 
	  (terpri)
	  (if (not (ok-to-continue)) then 
	      (princ "Use [op : type1, type2, ... -> type] to declare arity")
	      (terpri) (princ "under the 'add' command.") (terpri)
	      (reset))
	  (princ (uconcat "What's the type of '" op "' ? "))
	  (if $type-constructors 
	      then (terpri)
	      (setq l1 nil)
	      (ask-choice l1 (cons 'univ (loop for xa in $type-constructors
					       collect (car xa))) 
			  "You have the types: ")
	      else (setq l1 (read-atom 'end)))
	  (set-arity2 op (loop for i from 0 to (get-arity op) collect l1)))
      (set-constructor op)
      (add-associate-list l1 op $type-constructors)
      (if (is-constant-op op)
	  then (push op $free-constructors)
	  elseif (and (not (assoc op $op_rules))
		      (ok-to-continue
		       (uconcat "Is '" op "' a free constructor ? ")))
	  then (push op $free-constructors))
      t))

(defun ext-divisible (op &aux l1 l2 constants) 
  (if (neq (get-arity op) 2) 
      then (terpri) (princ "Only binary operators are accepted.") (terpri)
      elseif (assoc op $divisible) 
      then (terpri) (princ "That operator has the property.") (terpri)
      else
      (terpri) 
      (if (ok-to-continue (uconcat "Does the '" op 
				   "' have the identity function ? ")) then
	  (setq constants (get-constants $operlist))
	  (if (cdr constants)
	      then 
	      (ask-choice l1 constants "Please type it: ")
	      else
	      (princ (uconcat "I assume it is '" (car constants) "'.")) 
	      (terpri)
	      (setq l1 (car constants))))

      (if (and $instant
	       (ok-to-continue
		(uconcat "Does the '" op
			 "' have the exception for cancellation ? "))) then
	(if (cdr constants)
	    then (ask-choice l2 constants "Please type it: ")
	    else 
	    (princ (uconcat "I assume it is '" (car constants) "'.")) 
	    (terpri)
	    (setq l2 (car constants))))

      (push (list op l2 l1) $divisible)))

(defun ext-transitive (op)
  (if (not (memq op $translist)) then
    (princ (uconcat "The operator '" op "' is transitive now.")) (terpri)
    (if (not (ok-to-continue "Is this operator reflexive ? "))
        then (putprop op t 'irreflexive)
        else (putprop op nil 'irreflexive))
    (push op $translist)))

(defun ext-commutative (op)
   (if (not (memq op $commutative)) then
    (if (get op 'status)	
	then (princ "There exists status, sorry.") (terpri) nil
	else (princ (uconcat "'" op "' is commutative now.")) (terpri)
	     (sys-flag-init)
	     (push op $commutative)
             (flatten-rules op 'c-permutation))))

(defun ext-ac (op)
   (if (not (memq op $ac)) then
     (if (get op 'status)        
        then (princ "There exists status, sorry.") (terpri) nil
        else (princ (uconcat "'" op "' is associative & commutative now.")) 
             (terpri)
             (sys-flag-init)
             (setq $norm_str 'o
                   $blocking-on 'y)
             (push op $ac)
             (if $rule-set (flatten-rules op 'make-flat '(user declared))))))

; The following functions are used to add an equivalence relation
; between two operators in the precednce relation. This needs us to

(defun ext-equivalence ()
  ; modifies: $eqop_list $glob_prec
  ; Adds an equivalence relation between two operators in the
  ; precedence relation.
  ; $GLOB_PREC and $EQOP_LIST have to be updated after checking consistency
  ; of the status and equivalence.
  (if (is-empty-line $in-port)
      then (princ "Type the two operators you wish to make equivalent")
           (terpri) (princ "separated by a blank: "))
  (let ((op1 (read-atom 'noend)) op2)
    (setq op2 (progn (if (is-empty-line $in-port) 
                        then (princ "Type second operator: "))
                     (read-atom 'end)))
    (if (not (and (member op1 $operlist) (member op2 $operlist)))
        then (princ "Sorry, operators are not in current system.") (terpri)
        elseif (eqops op1 op2) then (princ "Already equivalent.") (terpri)
        elseif (is-rel-prec op1 op2)
        then (princ "Sorry, inconsistent equivalence.") (terpri)
        else (try-make-equi op1 op2))))

(defun try-make-equi (op1 op2)
  ;  Check the status of OP1 and OP2. Try to make OP1 and OP2 to be 
  ;            equivalent and consistent with their status. 
  (let ((s1 (get op1 'status)) (s2 (get op2 'status)))
    (cond ((and s1 s2) 
           (if (eq s1 s2) then
             (princ (uconcat op1 " and " op2 " made equivalent.")) (terpri)
             (add-equ op1 op2)
            else (princ "Operators have opposite status, sorry.") (terpri)))
          (s1 (if (intersection (ops-equiv-to op2) $commutative)
                 then (princ (uconcat op1 " has status while " op2
                        " is commutative or equivalent to commutative ones."))
                      (terpri)
                 else (warn-stat op1 op2)
                      (add-equ op1 op2)))
          (s2 (if (intersection (ops-equiv-to op1) $commutative)
                 then (princ (uconcat op2 " has status while " op1
                        "is commutative or equivalent to commutative ones.")) 
                      (terpri)
                 else (warn-stat op2 op1)
                      (add-equ op2 op1)))
           (t (princ (uconcat op1 " and " op2 " made equivalent.")) (terpri)
             (add-equ op1 op2)))))

(defun add-equ (op1 op2)
  ; Local function.  Called by EXT-EQUIV.
  ; Does the actual adding of the relation OP1 equivalent to OP2.
  (let ((eqs1 (ops-equiv-to op1)) (eqs2 (ops-equiv-to op2)))
    (if (equal eqs1 (ncons op1))
      then (if (equal eqs2 (ncons op2)) 
             then (push (list op1 op2) $eqop_list)
             else (add-at-end eqs2 op1))
      else (if (equal eqs2 (ncons op2)) 
             then (add-at-end eqs1 op2)
             else (setq $eqop_list (delete eqs1 (delete eqs2 $eqop_list)))
                  (push (append eqs1 eqs2) $eqop_list)))
    (setq eqs1 (assoc op1 $glob_prec)
          eqs2 (assoc op2 $glob_prec)) 
    (if eqs1 then (rplacd eqs1 (union (cdr eqs1) (cdr eqs2)))
                  (update-by-eq op1)
     elseif eqs2 then (update-by-eq op2))
  
    (loop for xa in $glob_prec do
        (if (or (eq (car xa) op1) (eq (car xa) op2)) then ()
            elseif (member op1 xa) then (add-at-end xa op2)
            elseif (member op2 xa) then (add-at-end xa op1)))
  t))

(defun warn-stat (op1 op2)
  ; Local function.  Called by EXT-EQUIV when making OP1 equivalent to OP2 to
  ;                      ensure that they have consistent status.
  (princ (uconcat "Operator, " op1 ", has status: " (get op1 'status)))
  (terpri)
  (loop for op in (ops-equiv-to op2) do
    (princ (uconcat "Operator, " op ", also being given same status.")) 
    (terpri)
    (setq $st_list (cons op $st_list))
    (putprop op (get op1 'status) 'status)))

(defun fastkb-choices ()
  (user-selectq
    (blocking "Set blocking flag for critcal pairs" (block-choice))
    (polynomial "Set polynomial processing option" (poly-choice))
    (prime-acu "Set flag for checking prime ac unifiers." (prime-acu-choice))
    (quit     "Quit fast kb option setting" nil)
    (restrict  "Set restrictions on making superpositions."
	       (restrict-crit-stra))
    (symmetry "Set symmetry flag for critcal pairs" (symmetry-choice))))

(defun block-choice ()
  (ask-choice $blocking-on '(y n)
  "Set blocking flag on or off (good for AC operators)? " ))

(defun symmetry-choice ()
  (ask-choice $check-symmetry '(nil t)
    "Set flag for checking symmetry relation (good for AC operators)? " ))

(defun prime-acu-choice ()
  (ask-choice $prime-acu '(nil t)
	      "Set flag for checking prime/composite AC unifiers or not? " ))

(defun ac-kb-choice ()
  (ask-choice $new-ac '(t nil)
  "Set new ac-completion trick flag on or not ? " ))

(defun cycle-choice ()
  (ask-choice $cycle-rule '(t nil)
	      "Set cycle rule flag on or not ? " ))

(defun instant-choice ()
  (ask-choice $instant '(t nil)
	      "Make instances of non-terminating or big rules ? " ))

(defun poly-choice ()
  (ask-choice $polynomial '(t nil)
  "Set the polynomial flag on means that the following axioms are built in:"
  "             x + y == y + x               z * (x + y) == (z * x) + (z * y)"
  "       (x + y) + z == x + (y + z)         (x + y) * z == (x * z) + (y * z)"
  "             x + 0 == x                         0 * x == 0"
  "       (x * y) * z == x * (y * z)               x * 0 == 0"            
  "Do you want to set it ? " )
  (if $polynomial 
      then (poly-initialize)
      else (terpri) (princ "You should re-initialize RRL.") (terpri))
  (terpri))

(defun brake-choice ()
  ; >>>>> 1/16/89
  (user-selectq 
   (depth "Set depth of conditional rewriting" (over-rewrite-premises))
   (normalize "Set maximal rewritings in a normalization" (normalize-bound))
   (postpone "Set the limit of postponed equations." (post-limit-stra))
   (quit  "Quit brake setting." nil)
   (rules "Set the maximal size of the system." (new-rule-stra))
   (runtime "Set the limit of run time." (time-limit-stra))))

(defun time-limit-stra ()
  (ask-number $runtime-max
	      "What is the limit of run time ? "))

(defun normalize-bound ()
  (ask-number $reduce-bound
	      "What is the maximal rewritings in a normalization? "))

(defun auto-options ()
  ;  Lets the user set the strategies relating to critical pairs and rules.
  (let (stop)
   (loop while (not stop) do
     (user-selectq 
      (eq-pre "Set priority of inequivalence or equivalence relation."
                 (eq-pre-strat))
      (lr-rl "Set priority to left-right or right-left status"
                 (lr-rl-strategy))
      (new-oper "Set new operator introducing stratedgy." (operator-stra))
      (postpone "Set postponing equation strategy." (post-posi-stra))
      (keep-rule "Set keeping rule strategy (used for undo)."
                 (keep-rule-strategy))
      (post-limit "Set the limit of postponed equations." (post-limit-stra))
      (rule-limit "Set the limit of increasing size of the system."
                 (new-rule-stra))
      (quit "Return to top level." (setq stop t)))
   (terpri))))

(defun operator-stra ()
  (ask-choice $newop-first '(1 2)
 "Introduce a new operator as posssible (1), or when really needed (2)?"))

(defun eq-pre-strat ()
  (ask-choice $pre-first '(1 2)
     "Equivalence relation first (1), or inequivalence relation first (2) ?"))

(defun new-rule-stra ()
  (ask-number $newrule-max
	      "What is the limit of new rules under a new precedence ? "))

(defun support-eqn ()
  ; Deletes specified equation from the equation set.
  (prog (l1)
    support-top
    (if (is-empty-line $in-port)        ; no argument pending?
        then (princ "Type support input numbers (or L to list) : "))
      (setq l1 (read-args $in-port))
      (if (eq (car l1) 'l)
          then (display nil)                        ; display equations only.
               (go support-top))
      (loop for n in l1 do
        (cond ((not (numberp n))
               (princ (uconcat n " is not a number.")) (terpri))
              (t (query-insert n $support))))))

(defun post-posi-stra ()
  (ask-choice $post-posi '(1 2 3) 
        "Postpone an equation before precedence suggestion (1), "
        "  or after precedence suggestion and before status suggestion (2)"
        "  or after status suggestion (3) ?"))

(defun lr-rl-strategy ()
  (ask-choice $rl-first '(1 2)
	      "left-to-right-status first (1), or rl-status first (2) ?"))

(defun arity-eq-strategy ()
  (ask-choice $eq-arity '(y n)
       "Operators with the same arity can be equivalent or not ?"))

(defun keep-rule-strategy ()
  (ask-choice $resume-rule '(y n)
	      "When undo, keep all rules as equations or not ?"))

(defun post-limit-stra ()
  (ask-number $post-max
	      "What is the maximum number of postponed equations ?"))
