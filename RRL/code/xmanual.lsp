(in-package 'user)

#|
=====================================================================
  File: x_manual.lsp

  Index:
    0. xin-menu (&rest options)
    1. manual_reduce (eqn step num &aux option result)
    2. menu_for_manual_reduce (eqn num &aux option)
    3. menu_for_normal (eqn num &aux option)
    4. x_normal (eqn step  num &aux option result)
    5. x_one_rule (eqn num &aux userin rule_sav eqn_sav rule)
    6. switch_rule_lr (rule &aux lhs rhs result)    
    7. x_choose_one_rule (rules &aux rule-list result userin)
    8. reduce-eqn-by-one-rule (eqn rule &aux term pres)
    9. x_reduce-by-one-rule (term rule)

=====================================================================
|#

(defun manual_reduce (eqn step num &aux option result)
  ;; try to reduce eqn to nil.
  ;; result = nil or old eqn or reduced eqn.
  (setf result eqn)
  (setf option (menu_for_manual_reduce eqn num))

  (cond 
         ((eq option 'normal)  (setf result (x_normal eqn step num)))
	 ((eq option 'split)   (setf result (x_split eqn step num)))
	 ((eq option 'general) (setf result (x_general eqn step num)))
	 ((eq option 'induc)   (setf result (x_induc eqn step num)))
	 ((eq option 'assume)  (setf $xnode (search-tree num $root))
                               (setf (node-source $xnode) 'assumed)
	                       (setf (node-status $xnode) 'lemma)
                               (setf result nil))
   
         ( t                   result)
  )
)



(defun x_split (eqn step num)
  (debug-msg " reduction by splitting " )
  eqn
  step
  num
)

(defun x_general (eqn step num)
  (debug-msg "  recuction by generalization ")
  eqn
  step
  num
)



(defun x_induc (eqn step num &aux result)
  ; 8/7/91
  ; set flag, let prover use x_make_conj to get conjectures
  (clean-indhyp)  ; clean previous induction hypothesis
  (setf $x_choose_term t)   
  (setf $failed-eqns nil) 
  (setf result (cover-proof-process2 eqn num step))
  (setf $x_choose_term nil) ; cancel flag
  ; if cover-proof-process2 returns eqn, eqn is reduced to nil otherwise eqn unchanged.
  (if* (equal result 't) then (setq result eqn))
  (if* (endp result) then eqn
                     else nil)
)


(defun menu_for_manual_reduce (eqn num &aux option)
 (setf option 'none)
 (sloop while t do
  (when (not (eq option 'none)) (return option))
  (clearscreen)
  (terpri)
  (princ " The equation to prove is :")
  (terpri)
  (write-seq-eqn num eqn)
  (terpri)
  (disp_strings '(
"                                                       "
"     +------------------------------------------------+"
"     |                                                |"
"     |        STRATEGIES OF REDUCTION                 |"
"     |                                                |"
"     |                                                |"
"     |         1. NORMALIZATION                       |"
"     |         2. SPLITTING                           |"
"     |         3. GENERALIZATION                      |"
"     |         4. INDUCTION                           |"
"     |         5. ASSUME TRUE                         |"
"     |                                                |"
"     |         9. QUIT                                |"
"     |                                                |"
"     +------------------------------------------------+"))
  (terpri)
  (princ "              Your option number is (1-5, 9) ")
  (setf option (read-atom 'end))
  (cond 
         ((eq option '1) (setf option 'normal))
         ((eq option '2) (setf option 'split))
         ((eq option '3) (setf option 'general))
         ((eq option '4) (setf option 'induc))
         ((eq option '5) (setf option 'assume))
         ((eq option '9) (setf option 'quit))

         ( t   (setf option 'none)
	       (terpri)
	       (princ " Which option?  Try it again, please. "))
  )
 )   
)


; -- 10/23/90 --

(defun menu_for_normal (eqn num &aux option)
  (setf option 'none)
  (sloop while t do
  (when (not (eq option 'none)) (return option))
  (clearscreen)
  (terpri)
  (princ " The equation to prove is :")
  (terpri)
  (write-seq-eqn num eqn)
  (terpri)
  (disp_strings '(
"                                                       "
"     +------------------------------------------------+"
"     |                                                |"
"     |           MANUAL  NOMALIZATION                 |"
"     |                                                |"
"     |                                                |"
"     |         1. PREPARE REWRITING RULES             |"
"     |         2. SIMPLIFY BY ONE NEW RULE            |"
"     |         3. SIMPLIFY BY ONE OLD RULE            |"
"     |         4. SIMPLIFY BY ONE REVERSED OLD RULE   |"
"     |         5. SIMPLIFY BY INDUCTION HYPOTHESIS    |"
"     |         6. AUTOMATIC NOMALIZATION              |"
"     |         7. AUGMEMT CONDITIONS BY ONE RULE      |"
"     |                                                |"
"     |         9. QUIT                                |"
"     |                                                |"
"     +------------------------------------------------+"))
  (terpri)
  (princ "              Your option number is (1-3, 9) ")
  (setf option (read-atom 'end))
  (cond 
         ((eq option '1) (setf option 'prepare))
         ((eq option '2) (setf option 'new_rule))
         ((eq option '3) (setf option 'old_rule))
         ((eq option '4) (setf option 'old_rev))
         ((eq option '5) (setf option 'hypothesis))
         ((eq option '6) (setf option 'automatic))
         ((eq option '7) (setf option 'augment))

         ((eq option '9) (setf option 'quit))

         ( t   (setf option 'none)
	       (terpri)
	       (princ " Which option?  Try it again, please. "))
  )
 )   
)




;-- reorganized at 8/2/91
(defun x_normal (eqn step  num &aux option result)
  ;; try to reduce eqn to nil
  ;; result is the return variable containing the reduced eqn
  (setf option (menu_for_normal eqn num))
  (setf result eqn)
  
  (sloop while t do
   (when  (eq option 'quit) (return result))
   (cond 
         ((eq option 'prepare)   (x_prepare_rules ))
	 ((eq option 'hypothesis)(setf result (x_one_rule option result num)))
	 ((eq option 'new_rule)  (setf result (x_one_rule option result num)))
	 ((eq option 'old_rule)  (setf result (x_one_rule option result num)))
	 ((eq option 'old_rev)   (setf result (x_one_rule option result num)))
	 ((eq option 'augment)   (setf result (x_augment result num)))
	 ((eq option 'automatic) (setf result (x_auto_normal result step num)))
    )
    ; redisplay menu for user's next option
    (setf option (menu_for_normal result num))
  )
)

(defun x_one_rule (option eqn &optional num &aux userin rule result)
   (setf result eqn)
   ; locate the proving eqn in tree
   (setf $peek (search_by_eqn result (list $x_sub_root)))

  (cond
     ((eq option 'hypothesis) 
          (setf userin $induc)
	  (setq rule (make-new-rule (lhs userin) (rhs userin) 
				    (ctx userin) (eqn-source userin))))

     ((eq option 'new_rule)   
      (setf userin (read-this-eqn))
      (setf $x_lemmas (append $x_lemmas (list userin)))
      (if* userin then
       (setq userin (flatten-eqn userin))
       (when (ctx userin)
	     (setq userin (change-ctx userin 
				      (first-process-premises (ctx userin))))))
       (setq rule (make-new-rule (lhs userin) (rhs userin) 
				 (ctx userin) (eqn-source userin)))
     )

     ((or (eq option 'old_rule) (eq option 'old_rev))
      (sloop while t do
	    (princ "Enter a rule number (or name); 0 for displaying rules.")
	    (terpri)
            (setf userin (read-atom 'end))
            (if* (eq userin 0)
		(list-rules $rule-set)
	      (if* (setq rule (pick-out-rule (name2rulenum userin)))
		  (return rule)
		(progn (princ "No rule is found. Try again.") (terpri)))
	      ))
	(if* (eq option 'old_rev) (setq rule (switch_rule_lr rule)))
     )
  )

  (when rule
	(setf $failed-eqns nil)
	(princ " The currently used rule is:")
	(terpri)
	(write-rule rule)
	(terpri)
        (setf $x_rule rule)
	(setf result (or (one-rule-iteration eqn rule) eqn))
	)

   ; if the given eqn is reduced, add it in tree.
   (if* (not (equal (node-info $peek) result)) then
        (add_child $peek num $x_rule $seq-no 'man nil result)
        (setf $seq-no (+ 1 $seq-no))
        ; explain the reason of one-rule-rewriting
        (terpri)
        (princ " By the rule: ")
        (terpri)
        (write-rule $x_rule)
	(princ " The equation : ")
        (terpri)
	(write-eqn (node-info $peek))
	(princ " is reduced to ")
        (terpri)
	(write-eqn result))

  result
)

;-- new 7/31/91 ---------------------------------------
(defun x_hypothesis (eqn &optional &aux userin rule result)
      (setf userin $induc)
      (if* userin then
          ; Add new rule in rule set -- by XH 
	  ; Why? -- by HZ
          ;(setf $eqn-set (append $eqn-set (list userin)))
          ;(order-eqns)
          (setq userin (flatten-eqn userin))
;	  (when (ctx userin)
;		(setq userin (change-ctx userin (first-process-premises (ctx userin)))))
	  (setq rule (make-new-rule (lhs userin) (rhs userin) 
				    (ctx userin) (eqn-source userin)))
	  (setf $x_lemmas (append $x_lemmas (list userin)))
      )
  (when rule
	(setf $failed-eqns nil)
	(princ " The currently used rule is:")
	(terpri)
	(write-rule rule)
	(terpri)
        (setf $x_rule rule)
        ;add new rule in rule set  -- by XH
	(setf result (or (one-rule-iteration eqn rule) eqn))
	)
  result
)
;-------------------------------------------------------------

(defun one-rule-iteration (eqn rule &aux old (new eqn))
  (sloop while t do
    (when (null new) (return old))
    (setf old new)
    (setf new (reduce-eqn-by-one-rule old rule))
    (mark " -- Reduce equation iteratively by one rule -- ")
    (mark " The old equation is : ")
    (write-eqn old)
    (mark " The new equation is : ")
    (if* new (write-eqn new) (princ " the same as the old one. "))
;    (when new
;	  (princ " Stop reducing by the same rule ? (y or n) ")
;	  (when (eq (read-atom 'end) 'y) 
;		(setf old new
;		      new nil)))
    (setf old new
	  new nil)
  )
)

(defun switch_rule_lr (rule &aux lhs rhs result)
  (setf lhs (first  rule))
  (setf rhs (second rule))
  (setf result (rest (rest rule)))
  (setf result (cons rhs (cons lhs result)))
)





(defun x_choose_one_rule (rules &aux rule-list result userin)
  (setf rule-list rules)
  (sloop  while t do
   (when (null rule-list) (return result))
   (write-rule (first rule-list))
   (princ " Is this rule? (y or n)")
   (setf userin (read-atom 'end))
   (if* (equal userin 'y) then
         (setf result (first rule-list))
         (setf rule-list nil)
    else
         (setf rule-list (rest rule-list))
   )
  )
)





; -- 10/29/90 -- 
(defun reduce-eqn-by-one-rule (eqn rule &aux term pres)
  ;; return an equation after one rewriting by rule.
  ;; If no rewriting, return nil.
  (setq $premises-set (ctx eqn))
  (cond
   ((setq term (x_reduce-by-one-rule (lhs eqn) rule))
    (change-lhs eqn term))
   ((and (nonvarp (rhs eqn)) (setq term (x_reduce-by-one-rule (rhs eqn) rule)))
    (change-rhs eqn term))
   (t (setq pres (my-copylist (cdr $premises-set)))
      (sloop for pre in pres 
	    if (and (nonvarp (car pre)) 
		    (setq term (x_reduce-by-one-rule (car pre) rule)))
	    do 
	    (setf (car pre) term)
	    (return (change-ctx eqn (cons '*&* pres)))))
   ))

(defun x_reduce-by-one-rule (term rule)
  ; Tries to rewrite TERM at some position using RULE.
  (cond ; ((variablep term) nil)
        ((and (not (member0 term $x_avoid-terms)) 
	      (same-root term (lhs rule)) 
	      (reduce-by-one-at-root term rule)))
        ((sloop for xa in (args-of term) for i from 1
		if (and (nonvarp xa) (setq xa (x_reduce-by-one-rule xa rule)))
		return (flat-term (rplnthsubt-in-by i term xa))
		finally (return nil)))
	))


  ;; -- 12/06/90 --

(defun x_add-rule3 (rule rule-list)
  ; Add RULE in RULE-LIST.
  (setq $newrule-num (1+ $newrule-num))
  (add-associate-list (op-of (lhs rule)) rule rule-list))

(defun x_clean-rule (rule &aux l1)
  ; clean $rule-set
  (setq $rule-set (delete0 rule $rule-set 1))

  ; clean $op_rules
  (if* (member0 rule (setq l1 (assq (op-of (lhs rule)) $op_rules))) then
	 (delete0 rule l1)))



(defun x_prepare_rules (&aux userin rule)
  (list-rules $rule-set)
  (princ "Which one do you want to delete? ( <number>, n (none))" )
  (setf userin (read-atom 'end))
  (if* (not (equal userin 'n)) then
    (setf rule (pick-out-rule userin))
    (x_clean-rule rule))
)


(defun x_augment (eqn num &aux userin rule)
  (princ " Choose one rule from old rule-set? (y or n)")
  (setf userin (read-atom 'end))
  (if* (equal userin 'n) then       ;; --- user enters new rule ---
      (setf userin (read-this-eqn))
      (if* userin then
          ;add new rule in rule set -- by XH
	  ;(setf $eqn-set (append $eqn-set (list userin)))
          ;(order-eqns)
          (setq userin (flatten-eqn userin))
	  (setq rule (make-new-rule (lhs userin) (rhs userin) 
				    (ctx userin) (eqn-source userin)))
	  (setf $x_lemmas (append $x_lemmas (list userin)))
      )
   else                            ;; --- choose one from rule-set ---
   (sloop while t do
      (princ " Which one? ( enter the rule number; 0 for displaying rules): " )
      (setf userin (ask-a-number 0))
      (if* (eq userin 0)
	  (list-rules $rule-set)
	(return (setf rule (pick-out-rule userin)))))
  )
  (when rule
	(setf $failed-eqns nil)
	(princ " The rule is currently used is:")
	(terpri)
	(write-rule rule)
	(terpri)
        ;; ---  augment equ ---   
	;; input: eqn & rule  
	;; output: t if the eqn is simplified to true.
	;;         eqn if a condition is added sucessfully.
	;;         nil if failed to add a condition.

	)
  (list eqn num)
)

(defun x_auto_normal (result step num)
  (list result step num))
