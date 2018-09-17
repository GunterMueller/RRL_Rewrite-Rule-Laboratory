;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)
(declare (special $add-crit-rule $orderhelp))
(setq $add-crit-rule nil 
      $orderhelp 
; >>>>>>>> 1/7/89
'(
"  Abort     - Quit to the top of RRL."
"  Cyclerule - Make it as a permutative rule. "
"  Display   - Display equivalence, precedence, and status of operators. "
"  Drop      - Throw it away."
"  Equiv     - Make two operators equivalent. "
"  LR        - Hand orient equation left-to-right. "
"  MakeEq    - Make a rule as (lhs = rhs) ---> true ."
"  Operator  - Introduce new operator. "
"  Postpone  - Postpone orienting this equation."
"  Quit      - Interrupt and go to top level. "
"  RL        - Orient equation right-to-left. "
"  Status    - Set lexicographic status of an operator. "
"  NoReduc   - Use it not for reduction but for superposition only."
"  Twoway    - Make it orientable in two directions."
"  Undo      - Undo previous operation. "
"  Help      - Print this message."
""
))

(defun orient-an-eqn (eqn &optional eqn2 &aux xa)
  ; Try consisient checking.
  ; Try to orient EQN into rule.
  ; If possible, then add the new rule obtained into the system.
  ; Return NIL.
  (if $induc 
      then (if (ctx eqn) then (setq eqn (release-premises eqn)))
           (if (falsep (lhs eqn)) then (refuted-result (eqn-source eqn)))
      elseif $prove-eqn then (consistent-check eqn))
  (if eqn then
      (setq xa (*catch 'reset (add-time $ord_time (orient-rule eqn))))
      (cond ((eq xa '*reset*)
	     (push (if eqn2 then eqn2 else eqn) $eqn-set)
	     (if $prove-eqn then (*throw 'prove '*reset*) else (reset)))
	    ((memq xa '(nil *kb-top*)) nil)
	    (xa (add-time $add_time (add-rule xa))))))

(defun pure-orient-an-eqn (eqn &aux xa)
  ; Try consisient checking.
  ; Try to orient EQN into rule.
  ; If possible, then add the new rule obtained into the system.
  ; Return NIL.
  (setq xa (*catch 'reset (add-time $ord_time (orient-rule eqn))))
  (cond ((eq xa '*reset*) 
	 (push eqn $eqn-set) 
	 (reset))
	(xa (add-time $add_time (pure-add-rule xa)))))

(defun orient-rule (eqn &aux l1 rhs)
  ; modifies: $operlist, $eqop_list, $glob_prec, $st_list
  ; tries to orient the equation EQN as a rule.  If possible,
  ; then returns a rule.  If EQN is invalid or un-orientable, return NIL.
  ; If EQN is invalid in the sense that the variable set of either
  ; term is not contained in the other then the function INVALID-RULE
  ; is called which tries to add a new operator and form two rules.
  (if (setq l1 (divisible-check (lhs eqn) (setq rhs (rhs eqn)))) 
      then (if (eq l1 'p) then
	       (push eqn $post-set)
	       (terpri) 
	       (princ (uconcat "Postponed a big critical pair of Rule ["
			       (car (eqn-source eqn)) "] and Rule [" 
			       (cadr (eqn-source eqn)) "]."))
	       (terpri)
	       (if (> $trace_flag 2) then (princ "    ") (write-eqn eqn))
	       nil
	       else
	       (process-equation (remove-one-arg l1 eqn)))
      else
      (if (null rhs) then (setq rhs '(true)))
      (if (ctx eqn)
	  then (caseq (is-valid-condi-rule eqn (is-oneway eqn))
		 (nil nil)
		 (1 (try-to-orient-condi eqn (lhs eqn) rhs (ctx eqn) t))
		 (2 (try-to-orient-condi (exchange-lr eqn)
					 rhs (lhs eqn) (ctx eqn) t))
		 (t (try-to-orient-condi eqn (lhs eqn) rhs 
					 (ctx eqn) (is-oneway eqn))))
	  else (caseq (is-valid-rule eqn (is-oneway eqn))
		 (nil nil)
		 (1 (try-to-orient eqn (lhs eqn) rhs t))
		 (2 (try-to-orient (exchange-lr eqn) rhs (lhs eqn) t))
		 (t (try-to-orient eqn (lhs eqn) rhs (is-oneway eqn)))))))

(defun try-to-orient-condi (eqn t1 t2 c oneway &aux s1 s2)
  ; modifies: $eqop_list, $glob_prec, $st_list
  ; ONEWAY indicates if the terms T1 and T2 can be oriented only
  ; one way (because of varsets) or they can be compared both ways.
  ; If they are not currently orderable, call functions SUGG-PREC
  ; and ASK-USER to get help from the user.  If the terms are
  ; orientable, return the rule to be added.
  (cond ((eq $ordering 'm) (manual-orient eqn t1 t2 c oneway))
        ((and (eq $ordering 's) (neq (setq s1 (size t1)) (setq s2 (size t2))))
	 (if (> s1 s2)
	     (make-new-rule t1 t2 c (eqn-source eqn))
	     (make-new-rule t2 t1 c (eqn-source eqn))))
	((lrpo t1 t2) 
	 (if (order-ctx eqn t1 c) then
	  (make-new-rule t1 t2 c (eqn-source eqn))))
        ((and (not oneway) (lrpo t2 t1))
         (if (order-ctx eqn t2 c) then 
	  (make-new-rule t2 t1 c (eqn-source eqn))))
        (t
	 (if (and (eq $induc 'c) (variablep (lhs eqn)))
	     (instantiate-lhs eqn))

	 (terpri) (princ "Trying to orient the equation: ") (terpri)
	 (princ "  ") (write-eqn eqn)
	 (caseq (ask-user eqn t1 t2 oneway)
		(1 (if (order-ctx eqn t1 c) then
		    (make-new-rule t1 t2 c (eqn-source eqn))))
	     (2 (if (order-ctx eqn t2 c) then
		    (make-new-rule t2 t1 c (eqn-source eqn))))
	     ((m p) nil)
	     (i (*throw 'reset '*reset*))))))

(defun try-to-orient (eqn t1 t2 oneway &aux s1 s2)
  ; FLAG indicates if the terms T1 and T2 can be oriented only
  ; one way (because of varsets) or they can be compared both ways.
  ; If they are not currently orderable, call functions SUGG-PREC
  ; and ASK-USER to get help from the user.  If the terms are
  ; orientable, return the rule to be added.
  (cond ((eq $ordering 'm) (manual-orient eqn t1 t2 nil oneway))
        ((and (eq $ordering 's) (neq (setq s1 (size t1)) (setq s2 (size t2))))
	 (if (> s1 s2)
	     (make-new-rule t1 t2 nil (eqn-source eqn))
	     (make-new-rule t2 t1 nil (eqn-source eqn))))
        ((lrpo t1 t2) (make-new-rule t1 t2 nil (eqn-source eqn)))
        ((and (not oneway) (lrpo t2 t1))
	 (make-new-rule t2 t1 nil (eqn-source eqn)))
	((is-p-commut-pair (lhs eqn) (rhs eqn))
	 (make-p-commut-rule eqn) nil)
	((and $cycle-rule (is-cycle-eqn eqn)) (make-cycle-rule eqn))
        (t (terpri) (princ "Trying to orient equation: ") (terpri)
		    (princ "  ") (write-eqn eqn)
 	   (caseq (ask-user eqn t1 t2 oneway)
	     (1 (make-new-rule t1 t2 nil (eqn-source eqn)))
	     (2 (make-new-rule t2 t1 nil (eqn-source eqn)))
	     (p nil)
	     (i (*throw 'reset '*reset*))
	     (m nil)
	     (t (break "Lost in try-to-orient"))))))

(defun order-ctx (eqn term c)
  ;  Try to prove TERM is greater than CTX. If so, return T.
  (cond ($induc t)
	((lrpo term c) t)
        ((lrpo c term) (ctx-gt-lhs eqn) nil)
        (t (terpri) (princ "Trying to orient Equation: ") (terpri)
	   (princ "  ") (write-eqn eqn)
           (caseq (ask-user eqn term c t)  
	       (1 t)
	       (2 t)
	       (p nil)
	       (i (*throw 'reset '*reset*))))))   

(defun ctx-gt-lhs (eqn)
  ;  Signal that the precondition of EQN is greater then the 
  ;	    left-hand-side of EQN.
  (terpri)
  (princ "Conditional equation : ") (terpri) (princ "    ")
  (write-eqn eqn)
  (princ "    is not contextual noetherian.") (terpri)
  (*throw 'reset '*reset*))

(defun try-to-orient2 (t1 t2 oneway)
  ; FLAG indicates if the terms T1 and T2 can be oriented only
  ; one way (because of varsets) or they can be compared both ways.
  ; If they are not currently orderable, call functions SUGG-PREC
  ; and ASK-USER to get help from the user.  If the terms are
  ; orientable, return the rule to be added.
  (if (lrpo t1 t2) then 1
   elseif (and (not oneway) (lrpo t2 t1)) then 2))

(defun ask-user (eqn t1 t2 oneway)
  ; Called by TRY-TO-ORIENT, ORDER-CTX.
  ; modifies: $eqop_list, $glob_prec, $st_list
  ; Asks the user for help when orienting rules.  It takes a
  ;	    list of possible precedence relations and prompts the user
  ;	    to either choose a list of them, add status, add new
  ;	    operators, or hand orient the rule.
  ;	    Returns 1 if t1 > t2
  ;		    2 if t2 > t1
  ;	 	    i if interrupt
  ;		    p if postponed
  ;		    m if made as eq(t1, t2) ---> true.
  (prog (l3 sugg)
    (start-history-manual eqn)
    (if (and $akb_flag $auto-sugg)
 	then (setq sugg (pop $auto-sugg)) 
	else (setq sugg (sugg-prec (op-list t1) (op-list t2) oneway))
	     (if (and $history1 $akb_flag) then (rplaca $history1 (ncons sugg))))

    asktop
    (print-sugg-info t1 t2 sugg oneway (null (ctx eqn)))

    (if $akb_flag then  (princ "auto") (terpri) 
	   (return (auto-orient eqn t1 t2 sugg oneway)))

    (selectq
      (choose-str (setq l3 (read-atom 'none))
	      '(abort cyclerule display drop equivalence help 
		      left_to_right makeeq noreduc operator postpone quit
		      right_to_left status twoway undo))
      (abort (return 'i))
      (cyclerule
       (if (ctx eqn) 
	   then (princ "Impossible ! Try again.") (terpri) (go asktop)
	   else 
	   (setq $cycle-rule t)
	   (make-cycle-rule eqn) (return 'm)))
      (display (display-op-stats) (go asktop))
      (drop (return 'm))
      (equivalence 
     	 (if (ext-equivalence) then
	    (push-history-manual)
	    (if (setq l3 (try-to-orient2 t1 t2 oneway)) then (return l3))
	    (setq sugg (remove-sugg sugg)))
         (go asktop))
      (help (help-file $orderhelp) (go asktop))
      (left_to_right
        (if $lrpo then (print-warning)
	    (if (not (ok-to-continue)) then (go asktop)))
        (setq $lrpo nil)
        (push-history-manual)
        (return 1))
      (makeeq (return (make-eq t1 t2 eqn)))
      (noreduc (make-crit-rule eqn t1 t2) (return 'm))
      (operator
	 (add-operator eqn (var-list (lhs eqn)) (var-list (rhs eqn)) nil)
	 (return nil))         
      (postpone (push eqn $post-set)
		(setq $history1 nil)
	        (return 'p))
      (quit (return 'i))
      (right_to_left
         (if (not (is-subset (var-list t1) (var-list t2))) then 
	    (princ "Sorry - the relation will never be sound.") (terpri) (go asktop)
           else
	   (if $lrpo then (print-warning)
 		(if (not (ok-to-continue)) then (go asktop)))
  	   (push-history-manual)
           (setq $lrpo nil)
	   (return 2)))
      (status
	 (if (ext-status) then
   	    (push-history-manual)
	    (if (setq l3 (try-to-orient2 t1 t2 oneway)) then (return l3))
	    (setq sugg (remove-sugg sugg)))
         (go asktop))
      (twoway
	(if (not oneway) 
	  then (princ "It is already twoway.") (terpri)
               (go asktop)
	  elseif (or (not (is-subset (var-list t1) (var-list t2)))
		     (equal (ctx eqn) t2)) then 
  	       (princ "Sorry, twoway cannot be set.") (terpri) 
               (go asktop)
	  else (princ "Equation can be oriented in twoway now.") 
	       (push (set-eqn-mark eqn nil) $eqn-set)
	       (return 'p)))
      (undo (undo))
      (otherwise
	(if (not (numberp l3)) then
	  (invalid-input-warning l3) (go asktop))

	(if (setq l3 (try-sugg-prec t1 t2 l3 sugg oneway)) then (return l3))
	(setq sugg (remove-sugg sugg))
        (go asktop)))))

(defun make-crit-rule (eqn t1 t2 &aux so)
  (setq so (cons 'crit (eqn-source eqn))
	so (list (make-new-rule t1 t2 (ctx eqn) so)))
  (loop for xa in so do (add-crit-rule xa)))

(defun comp-rule (r1 r2)
  ; Returns T if r1 should be ordered before r2 in a rule-set.
  (cond ((null-ctx (ctx r1))
         (if (null-ctx (ctx r2))
             then (lessp (lhsize r1) (lhsize r2))
             else t))
        ((null-ctx (ctx r2)) nil)
        (t (lessp (lhsize r1) (lhsize r2)))))

(defun comp-eqn (e1 e2)
  ;  Returns T if e1 should be ordered before e2 in a rule-set.
  (cond ((null-ctx (ctx e1))
         (if (null-ctx (ctx e2))
             then  (lessp (size (lhs e1)) (size (lhs e2)))
             else t))
        ((null-ctx (ctx e2)) nil)
        (t (lessp (size (lhs e1)) (size (lhs e2))))))

(defun make-eq (t1 t2 eqn)
  (setq t1 (if $induc 
	       then  (make-term '= (commu-exchange (list t1 t2)))
	       else  (make-term 'eq (commu-exchange (list t1 t2))))
	t1 (norm-ctx t1))
  (if (truep t1) then nil
      elseif (falsep t1) then (refuted-result (eqn-source eqn))
      else (add-rule (make-new-rule t1 '(true) (ctx eqn) (eqn-source eqn))))
  'm)

;;; functions used to be in manual.l

(defun manual-orient (eqn t1 t2 c flag)
  ;
  (prog (l3 response)
    (start-history-manual eqn)
    asktop1 
    (terpri)
    (if flag then 
       (princ "The equation can only be oriented from left-to-right (LR)") 
       (terpri)
       else 
       (princ "The equation can be oriented from left-to-right (LR) or ")
       (princ "right-to-left (RL)") (terpri))
    (princ "Type Add-op, Give-Stat, LR, RL, Postpone, Undo, Quit, ")
    (princ "or Help.") (terpri) 
    (princ "To orient: ") (write-eqn eqn)
    (princ "RRL>ORDER> ")
    (selectq (setq l3
		(choose-str (setq response (read-atom 'none))
		 	'(add-operator give-stat help interrupt 
			  left-to-right  noreduc right-to-left 
			  postpone quit undo)))
      (add-operator
         (add-operator eqn (var-list (lhs eqn)) (var-list (rhs eqn)) nil)
	 (return nil))
      (give-stat (give-stat) (go asktop1))
      (help
	(terpri)
	(princ "  Add-op   - Add new operator.") (terpri)
        (princ "  Give-stat - Gives statistics.") (terpri)
	(princ "  LR       - Hand orient equation left-to-right.") (terpri)
	(princ "  RL       - Hand orient equation right-to-left.") (terpri)
	(princ "  Postpone - Postpone orienting this equation for now.")
	(terpri)
	(princ "  Quit     - Interrupt and go to top level.") (terpri)
	(princ "  Undo     - Undo previous operation.") (terpri)
	(go asktop1)
      )
      (left-to-right (push-history-manual) (return (make-new-rule t1 t2 c (eqn-source eqn))))
      (noreduc (make-crit-rule eqn t1 t2) (return 'm))
      (postpone (push eqn $post-set) (setq $history1 nil) (return nil))
      ((interrupt quit) (*throw 'reset '*reset*))
      (right-to-left
	 (if flag then (princ "Sorry - rule cannot be reversed.") (terpri)
		       (go asktop1)
	          else (push-history-manual) (return (make-new-rule t2 t1 c (eqn-source eqn)))))
      (undo (undo) (go asktop1))
      (otherwise (invalid-input-warning l3) (go asktop1)))))

(defun initialize-manual-ordering ()
  (setq $manual-history-number 0)
  (print-warning))

(defun instantiate-lhs (eqn) 
  (terpri) 
  (princ "Instantiating the equation with constants: ") (terpri)
  (princ "    ") (write-eqn eqn)
  (princ "    because its LHS of the head is a variable.")
  (terpri)
  (loop with type = (get-domain-type (op-of (rhs eqn)))
	for op in $operlist 
	if (and (not (is-bool-op op)) 
		(is-constant-op op)
		(type-cohere type (get-domain-type op)))
	  do (process-equation (subst-eqn (lhs eqn) (ncons op) eqn))))

