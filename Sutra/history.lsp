;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "RRL")



;;;; changed a merge to merge-list (siva 9/24)

(defun start-history (&optional eqn force)
  ;  Saves relevant variables in $HISTORY1 (if not already done so)
  ;  which will later be put in $HISTORY.
  (if (and (null $history1)
	   (or force (not $no-history))) then
     (setq $history1 (nconc
		         (list  nil ; Place for $auto-sugg
				$newop-terms
			        (if eqn then (cons eqn $eqn-set)
					else (my-copylist $eqn-set))
				(my-copylist $post-set)
				(my-copylist $post-ass-set)

				(my-copylist $rule-set)
				(my-copylist $invalid-rules)
				(my-copylist $goal-set)
				(my-copylist $aux-rset) 
				(my-copylist $op_rules) 
				(my-copylist $cycle-op-rules)
				(my-copylist $build-rules)
				(my-copylist $character-rules)
				(my-copylist $p-commut-rules)

				(my-copylist $pair-set)

				(my-copylist $eqop_list)
				(my-copylist $glob_prec) 
				(copylist $st_list)
				(copylist $del-rule-nums)
				(copylist $del-rules)

				(copylist $operlist)
				(my-copylist $cover-sets)
				(my-copylist $non-comm-cover-sets)
				(my-copylist $defin-depend)
				(copylist $divisible) 
				(copylist $translist) 
				(copylist $commutative) 
				(copylist $associative) 
				(copylist $ac)
				(copylist $constructors) 
				(copylist $free-constructors) 
				(my-copylist $type-constructors) 
				$num-type
				$confluent 
				$sufficient
				$prove-eqn
				$nrules
			        $ncritpr 
				$unblocked
				$lrpo
				$ans-rule
				$narrow
				$in-fopc
				$add_time 
				$norm_time 
				$unif_time
				$ord_time 
			 	$proc_time)
		        (loop for op in $st_list collect (get-status op)))))
  $history1)

(defun start-history-manual (&optional eqn)
  (if (= $manual-history-number $manual-history-frequency)
      (start-history eqn)))

(defun push-history (&optional notrace)
  ;  Saves relevant variables onto $HISTORY.  Returns a list of the
  ;  variables saved and the status properties.
  (if $history1
      then (push $history1 $history)
	   (setq $max-history (max $max-history (length $history)))
	   (if (not notrace) then
	       (terpri)
	       (princ (uconcat "----- Step " (length $history) " -----"))
	       (terpri))
	   (setq $history1 nil $newrule-num 1)))

(defun push-history-manual ()
  (if (= $manual-history-number $manual-history-frequency)
      then (push-history) (setq $manual-history-number 0)
      else (setq $manual-history-number (1+ $manual-history-number))))

(defun start-push-history (&optional eqn notrace force)
  ;  Save the current state in $history.
  (start-history eqn force)
  (push-history notrace))

(defun undo (&optional flag)
  ; If if is possible to undo, then restores the variables and operator
  ; status and throws the undo tag with the value *UNDO*; otherwise,
  ; prints an error message and returns NIL.
  (cond ((null $history)  (princ "----- Nothing can be undone -----"))
        ((null (cdr $history))
         (if $akb_flag then (*throw 'akb '*noway*))
	 (undo1 (null flag))
         (princ "----- The original system is restored -----"))
        (t (undo1)
	 (princ (uconcat "----- Return to Step "(length $history)" -----"))))
  (terpri)
  (if $history then (*throw 'kb-top '*undo*)))

(defun undo1 (&optional flag)
   (let ((popped (cond (flag (car $history))
		       (t (pop $history))))
	 (ops $operlist) rules)
     (if (equal $resume-rule 'y) then (setq rules (r2e $rule-set)))
     (if popped then
      (loop for op in $st_list do (remprop op 'status))
      (setq	   $auto-sugg 	(pop popped)
		   $newop-terms (pop popped)
		   $eqn-set 	(pop popped)
		   $post-set	(pop popped)
		   $post-ass-set (pop popped)

		   $rule-set 	(pop popped)
		   $invalid-rules (pop popped)
		   $goal-set    (pop popped)
		   $aux-rset 	(pop popped)
		   $op_rules    (pop popped)
		   $cycle-op-rules (pop popped)
		   $build-rules  (pop popped)
		   $character-rules (pop popped)
		   $p-commut-rules  (pop popped)

		   $pair-set 	(pop popped)

		   $eqop_list   (pop popped)
		   $glob_prec	(pop popped)
		   $st_list 	(pop popped)
		   $del-rule-nums (pop popped)
		   $del-rules	(pop popped)

		   $operlist	(pop popped)
		   $cover-sets  (pop popped)
		   $non-comm-cover-sets (pop popped)
		   $defin-depend (pop popped)
		   $divisible	(pop popped)
		   $translist	(pop popped)
		   $commutative (pop popped)
		   $associative (pop popped)
		   $ac 		(pop popped)
		   $constructors (pop popped)
		   $free-constructors (pop popped)
		   $type-constructors (pop popped)
		   $num-type    (pop popped)
		   $confluent   (pop popped)
		   $sufficient  (pop popped)
		   $prove-eqn   (pop popped)
		   $nrules 	(pop popped)
		   $ncritpr  	(pop popped)
		   $unblocked	(pop popped)
		   $lrpo    	(pop popped)
		   $ans-rule	(pop popped)
		   $narrow	(pop popped)
		   $in-fopc	(pop popped)
		   $add_time	(pop popped)
		   $norm_time	(pop popped)
		   $unif_time 	(pop popped)
		   $ord_time 	(pop popped)
		   $proc_time 	(pop popped))
     (loop for op in (reverse $st_list) do (set-status op (pop popped)))

     (setq ops (loop for op in ops 
		     if (not (or (memq op $operlist) (memq op $bool-ops))) 
		       collect op))

;; OPS are operators introduced during the kb-completion.
     (loop for op in ops do (rem-arity op))
     (if (equal $resume-rule 'y) then
	 (setq rules (loop for eqn in rules
			   if (not (or (have-common ops (all-ops (lhs eqn)))
				       (have-common ops (all-ops (rhs eqn)))))
			     collect eqn)
	       $eqn-set (merge-list rules $eqn-set 'comp-eqn)))
     (setq $history1 nil)))
)

(defun clean-history ()
  ; Clean the history stack without effecting the current system.
  (terpri) 
  (if (null (cdr $history)) 
      then (princ "The history is not big enough to clean.")
      else 
      (if (cddr $history) then (setq $history (last $history)))
      (setq $prove-eqn nil)
      (princ "The history stack of RRL is cleaned."))
  (terpri))

(defun my-copylist (list &optional (depth 2))
  ; >>>>> 4/5/89
  ; Make new list from elements of "list".
  (if (= depth 1)
      ;(mapcan 'list list)		
      (append list nil)
      (loop for xa in list collect (my-copylist xa (sub1 depth)))))
