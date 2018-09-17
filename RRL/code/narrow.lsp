;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

; New globals vars.
; $narrow: True if doing narrowing or linear completion.

; $goal-set: Used to store generated rule.

; $ans-rule: Used to store rule of the form $anspred(..) --> true
; which represent answer to the problem.

; $guest-eqn: Keep the equation user entered so answer can be
; substituted for vars and printed.

; $op-goal-rules: Contains goal rules in a form like
; $op_rules. Only used if doing reduction with goal rules.

; Goal-reduce: If true reduce by goal rules. Currently does
; not seem to be useful.


;  The function linear controls the linear completion procedure. 
(defun linear (&aux l1)
  ; If $goal-set is not empty then see if user wants to
  ; continue previous attempt.
  (set-predicate $anspred)
  (if* $goal-set then
      (if* (not (ok-to-continue
		 "Continue previous linear completion (y,n) "))
	  then (setq $goal-set nil)))
       
  (if* (not $goal-set) then
      ; Get equation from user.
      (setq $op_goal_rules nil
	    $ans-rule nil
	    $pair-set nil
	    l1 'k
	    l1 (read-input (eq 'k (ask-choice 
				   l1 '(k f)
				   "From the keyboard or a file ? "))))
      (if* l1 then    
	  (setq $guest-eqn (car (last l1))
		$eqn-set (nconc $eqn-set (delete0 $guest-eqn l1)))
	  (makerules)
	  ; Convert last equation to the form pred(...) ---> $anspred(...)
	  (setq $eqn-set (ncons (mr $guest-eqn))))
      else
      (makerules))

  (setq $narrow t)
  (start-kb)
  
  ; If there are answers, print them by substituting for vars
  ; in equation user entered.
  (if* $ans-rule then
      (terpri) (princ "And the answer is ...") (terpri) (terpri)
      ; Loop for each answer.
      (sloop with free-vars = (free-vars (lhs $guest-eqn))
	    for rule in $ans-rule do
	; Substitute for free vars in user equation.
	(write-eqn (subpair free-vars (cdar rule) $guest-eqn))))
  (setq $ans-rule nil
	$confluent nil
	$narrow nil))

(defun mr (e)
  ; Mr changes predicate equation into equation of the form
  ; pred(...) == $anspred(...). Note this destorys any right-hand
  ; side the equation had.
  (cond ((null e) nil)
	(t (make-eqn (skolemize (lhs e) t)
		     (cons $anspred (free-vars (lhs e)))
		     nil (list 'goal (second (eqn-source e)))))))

(defun makerules ()
  ;  Make equations into rules without doing kb.
  ;  Different from order because will handle logical operators
  ;  and it normalizes and tries to simplify rules.
  (setq $newrule-num 1 $small-depth 3)
  (sloop while $eqn-set do (process-equation (pop $eqn-set))))


; Choose rule from $goal-set. Supports same option as RRL +
; If $pick-rule-str = v, pick rule that has fewest vars. This
; seems to work best for linear completion.
(defun pick-goal ()
    (if* $ac then (if* $pair-set then (pop $pair-set))
     elseif (eq $pick-rule-str 'f) then
       (sloop for rule in $goal-set
          if (not (crit-marked rule)) return (set-crit-mark rule))
     elseif (eq $pick-rule-str 'm) then
        (manual-goal)
     else (pick-small-goal)))

(defun manual-goal (&aux l1)
  (if* (setq l1 (sloop for r1 in $goal-set 
		  if (not (crit-marked r1)) collect r1)) then
    (if* (null (cdr l1)) then (set-crit-mark (car l1)) else
     (terpri)
     (princ (uconcat "There are " (length l1)
  	        " unmarked rules. Which one do you choose ? ")) (terpri)
     (prog ((l2 l1) n1)
	loop-here	       
	(terpri)
	(sloop for xa in l2 for n2 from 1 to 10 do (write-rule xa))
	(terpri)
	(setq n1 nil)
	(ask-number n1 "Please type a rule number, 0 for none.")
	(if* (not (= n1 0)) then
  	   (setq n1 (sloop for xa in l2 for n2 from 1 to 10 
			if (= (ruleno xa) n1) return (set-crit-mark xa)
			finally (return 0))))
	(if* (= n1 0) 
	   then (if* (null (setq l2 (nthcdr 10 l2))) then
		    (princ "You must choose one rule !") (terpri)
		    (setq l2 l1))
		(go loop-here)
	   else (return n1))))))

(defun pick-small-goal (&aux l1)
   (sloop with ssize = 999999 with r2 = nil
	  for rule in $goal-set 
	  if (not (crit-marked rule)) do
	     (if* (lessp (goal-rule-size rule) ssize)
		 then (setq ssize (goal-rule-size rule) r2 rule)
	       elseif (and (eq $pick-rule-str 'l) 
                           (= ssize (goal-rule-size rule)))
		 then (setq r2 rule))
          finally (if* r2 then (setq l1 (set-crit-mark r2))))
;   (if* (and l1 (= $idem 3) (not (unitp l1))) 
;      then (pick-small-goal)
;       else l1))
    l1)


; Return the size of a rule based of $pick-rule-str. If this = v
;  then rule size is number of vars, otherwise size is number of
; symbols

(defun goal-rule-size (rule &aux size)
   (cond ((equal $pick-rule-str 'v) 
             (setq size (length (free-vars (lhs rule))))
             (if* (equal size 0) then 99999 else size))
         (t (lhsize rule))))


(defun not-in-set (r1 s)
   (prog (r2)
      loop
         (if* (null s) then (return t))
         (setq r2 (car s) s (cdr s))

; If r1 is exactly the same as r2 (rule from s), we are done.

         (if* (and (equal (car r1) (car r2)) (equal (cadr r1) (cadr r2)))
          then (return nil))
; 
; Otherwise check if only different because are variable names different.
; Check unifier. If each var get assigned a var and no var occurs
; more than once in unifier than rules are the same.

         (if* (and (sub-test (unifier (lhs r1) (lhs r2)))
                  (sub-test (unifier (rhs r1) (rhs r2))))
             then (return nil))
         (go loop)))

; Test unifier to see if it represents rules are the same.

(defun sub-test (s)
   (if* (null s) then nil

; l1,l2 used to check no var occurs more than once.

    else (prog (l1 l2 temp)	
            (setq l1 nil l2 nil)
            loop
               (cond ((null s) (return t)))
               (setq temp (car s) s (cdr s))

; Check that assignment to var is var. Only vars are represented by
; atoms.

               (cond ((not (atom (cdr temp)))
                      (return nil))
                     ((member0 (car temp) l1) (return nil))
                     ((member0 (cdr temp) l2) (return nil))
                     (t (setq l1 (cons (car temp) l1))
                        (setq l2 (cons (cdr temp) l2))))
               (go loop))))


; My function to check is $anspred is in the list of args.

(defun ans-member (args)
   (if* (not $narrow) then nil
    else
       (sloop for a in args
	     if (and (not (atom a)) (eq (car a) $anspred))
	     collect a)))


; Modified function from kb.l. Do not print rule set after finish
; linear completion.
;run-kb

; Modified function from kb.l Before doing next set of critical
; pairs chek if answer has been found.
;knuth-bendix2


; Modified function from kb.l. Insert rules generated in linear completion
; into $goal-set. Presently generated rule are not inserted in $op-rules so
; they are not used for normalization. Must make sure that same rule
; is not added more than once. Do not add rules of the form
; $anspred ---> false, they are meaningless.
; Do not do critical pairs with rules of the form
; $anspred ---> true.
;addrule




; Modified function from critical.l. If $narrow true 
; return theory rules which are in rule set.
;intro-rule

; Modified function from input.l. If $narrow do not change
; assertion by universally quantifing all free vars.
;get-equation  

; Modified function form initial.l. Give initial value
; to new globals.
;initialize

; Modified function from toplevel.l. Add option linear and makerule.
;rrl

; Functions from norm.l
; Also these function have been changed to do normalization
; with $op_rules and $op_goal_rules. Note $op_goal_rules with
; empty unless $goal-reduce is true.
;norm-inn norm-with-bin mixed-reduce reducible2 rewrite-at-root guide-reducible reduce-bool-args


; Functions from option.l
; This function has been modified to allow v to be pick stategy.
; Option v say to do critical pair next with the goal rule with
; the smallest number of variables.
;pick-strategy


;Functions from critical
;Addition of flag $one-way
;func-superposition ac-superposition

;Functions from critical
;Does idem-superposition in case of narrowing
;critpairs

; From output.l
; Display has been change to also show the goal rules
;display


; From propbtr.l
; Simp-and has been changed so that $anspred & anything = $anspred
;simp-and


; functions from propsko. Refuted has been changed to
; add true-false to goal-set.
;refuted

; Modified function from propsko.l
; Compare term has been changes so that $anspred is less than
; everything but true.
;compare-term

; Modified function from propsko.l
; Make-rule-from-ass has been modify so that $anspred is
; on the right-hand side of a rule, unless true is the only
; other term.
;make-rule-from-ass

; Modified function from propsko.l
; Check-mismatch modified so $anspred does never violates
; the variable rules.
;check-mismatch

