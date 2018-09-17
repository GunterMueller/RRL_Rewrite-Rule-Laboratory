;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;  PICK  FIRST  RULE  TO  COMPUTE  CRITICAL  PAIRS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun pick-unmarked-rule ()
  ; Goes through the rule set and picks the unmarked rule with
  ; the smallest left-hand-side size.  If there are more than
  ; one such pick, the earliest or latest is choosen depending
  ; on the critical-pair strategy.  If a rule is found, mark it
  ; and return it.  If all rules are marked already, return NIL.
  (if* (eq $pick-rule-str 'm) then (manual-pick)
      elseif (and $induc (neq $induc 'c)) then (induc-pick-unmark)
      elseif $ac then (pick-ac-pair)
      else
      (caseq $pick-rule-str 
        (f (sloop for rule in $rule-set 
		 if (not (crit-marked rule)) return (set-crit-mark rule)))
        (m (manual-pick))
	(t (pick-one-unmarked)))))

(defun pick-unmarked-rule-dummy ()
  ; Goes through the rule set and picks the unmarked rule with
  ; the smallest left-hand-side size.  If there are more than
  ; one such pick, the earliest or latest is choosen depending
  ; on the critical-pair strategy.  If a rule is found, mark it
  ; and return it.  If all rules are marked already, return NIL.
  (if* (eq $pick-rule-str 'm) then (manual-pick)
      elseif (and $induc (neq $induc 'c)) then (induc-pick-unmark)
      elseif $ac then 
      (pop $pair-set)
;#+lispm (sloop for xa = (send $pair-set ':remove)
;	      if xa do
;		      (if* (not (or (memq (ruleno (cadr xa)) $del-rule-nums)
;				   (memq (ruleno (caddr xa)) $del-rule-nums)))
;			  (return xa))
;	      finally (return nil))
      else
      (caseq $pick-rule-str 
        (f (sloop for rule in $rule-set 
		 if (not (crit-marked rule)) return (set-crit-mark rule)))
        (m (manual-pick))
	(t (pick-one-unmarked)))))

(defun induc-pick-unmark ()
  ; Return a definition rule if there is an unmarked one.
  ; Otherwise return a property one that is not big than any other rules.
  (sloop for xa in $rule-set 
	if (and (not (crit-marked xa)) 
		(eq (car (rule-source xa)) 'def))
	  return (set-crit-mark xa)
	finally (return nil)))

(defun is-big-enough-rule (rule)     
  ; return t iff (lhs rule) is bigger than some marked rules other than "rukenos".
  (sloop with lhs = (lhs rule)
	for xb in (cdr (assoc (op-of lhs) $op_rules))
	thereis (is-sub-nonvar-term (lhs xb) lhs)))

(defun manual-pick (&aux rules)
  ; pick a rule for computing critical pairs.
  (setq rules (sloop for r1 in $rule-set 
			if (not (crit-marked r1)) collect r1))
  (if* rules then
    (if* (null (cdr rules)) then (set-crit-mark (car rules)) else
     (terpri)
     (princ (uconcat "There are " (length rules)
  	        " candidates for the first rule. Which one ? ")) (terpri)
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
			if (= (ruleno xa) n1) 
			    return (caseq $crit-with-str 
                                      ((h1 h2) xa)
	                              (t (set-crit-mark xa)))
			finally (return 0))))
	(if* (= n1 0) 
	   then (if* (null l3) then
		    (princ "You must choose one rule !") (terpri)
		    (setq l3 rules))
		(go loop-here)
	   elseif (= n1 999) then (return (reset))
	   else (return n1))))))

(defun pick-one-unmarked ()
   (sloop with ssize = 999999 with r2 = nil
	  for r1 in $rule-set 
	  if (not (crit-marked r1))
	    ;(or $add-crit-rule (is-reduction r1)))
	    do (if* (lessp (lhsize r1) ssize)
		   then (setq ssize (lhsize r1) r2 r1)
		   elseif (and (eq $pick-rule-str 'l) (= ssize (lhsize r1)))
		   then (setq r2 r1))
	 finally (if* r2 then (return (set-crit-mark r2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;  PICK  SECOND  RULES  TO  COMPUTE  CRITICAL  PAIRS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun intro-rule (rule)
  ; Return a list of rules that will be computed crtical pairs with "rule".
  ; Called when maintaining a list of marked rules to insert
  ; a newly picked rule for critical pairs.
  ; The flag $MARK_RULE_STR determines the discipline of marked rules (stack,
  ; queue, or sorted).  Sorted pays off in many examples.
  (if* $narrow then $rule-set 	; Return theory rules.
      else
      (caseq $crit-with-str 
	((h1 h2) (choose-by-hand rule
				 (sloop for xa in $rule-set 
				       if (nondo-crit rule xa) collect xa)))
	(o $rule-set)
	(m (caseq $mark_rule_str 
	     (l (if* (null $aux-rset) then (ncons rule)
		    else (insert rule $aux-rset 'comp-rule t)))
	     (q (append1 $aux-rset rule))
	     (s (cons rule $aux-rset))))
	(a (if* (or (nequal $idem 3) (unitp rule))
	       then (sloop for xa in $rule-set 
			  if ; (and (or $add-crit-rule (is-reduction xa))
			    (nondo-crit rule xa) collect xa)
	       else (sloop for xa in $rule-set 
			  if (and (unitp xa) 
				  ;(or $add-crit-rule (is-reduction xa))
				  (nondo-crit rule xa)) collect xa))))))

(defun choose-by-hand (rule rules &aux n1)
  ; pick a rule from "rules" so that we compute critical pairs between
  ; it and "rule". One case is to display rules, the other is not.
  (if* (null rules) then
      (set-crit-mark rule)
      (terpri) (princ "No rules can be chosen.") (terpri) 
      nil
      elseif (null (cdr rules)) then rules
      else
      (terpri)
      (princ (uconcat "There are " (length rules) " candidates as the second rule. "))
      (if* (eq $crit-with-str 'h1) then
	  (prog ((l2 rules))
	     loop-here	       
		(terpri)
	(sloop for xa in l2 for n2 from 1 to 10 do (write-rule xa))
	(setq n1 (man-pick-2nd-rule rule rules))
	(if* (= n1 999) then (return (reset))
             elseif (= n1 0) then
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
     (if* (= n1 999) then (reset)
	elseif (= n1 0) then
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
		     if (= (ruleno xa) n1) 
		       return (last-check-2nd-rule xa rule)
		     finally (return 0))))
  n1)

(defun last-check-2nd-rule (rule2 rule)
  ; check whether "rule2" has been computed critical pairs with "rule".
  ; If yes, yielding a warning message and return 0. 
  ; Otherwise, return a list containing "rule2".
  (if* (not (nondo-crit rule rule2)) then
      (terpri)
      (princ (uconcat "Critical pairs between [" (ruleno rule2)
                      "] and [" (ruleno rule) "] has been done."))
      (terpri)
      0
      else
      (list rule2)))

(defun nondo-crit (rule1 rule2)
  ; Determine whether we have done critical pairs between rule1 and rule2.  
  (if* (lessp (ruleno rule2) (ruleno rule1)) 
	     then (not (memq (ruleno rule1) (pairswith rule2)))
	     else (not (memq (ruleno rule2) (pairswith rule1)))))

(defun mark-superposed (rule1 rule2)
  ; Mark "rule1" and "rule2" such that the superposition
  ; has taken place between "rule1" and "rule2".
  ; We put the mark into the rule with the lesser number.
  (if* (lessp (ruleno rule2) (ruleno rule1)) 
     then (query-insert (ruleno rule1) (pairswith rule2))
     else (query-insert (ruleno rule2) (pairswith rule1))))


