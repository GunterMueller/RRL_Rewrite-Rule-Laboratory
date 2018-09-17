;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

(defun start-history (&optional eqn force)
  ;  Saves relevant variables in $HISTORY1 (if* not already done so)
  ;  which will later be put in $HISTORY.
  (if* (and (null $history1)
	   (or force (not $no-history))) then
     (setq $history1 (nconc
		         (list  nil ; Place for $auto-sugg
				$newop-terms
			        (if* eqn then (cons eqn $eqn-set)
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
		        (sloop for op in $st_list collect (get-status op)))))
  $history1)

(defun start-history-manual (&optional eqn)
  (if* (= $manual-history-number $manual-history-frequency)
      (start-history eqn)))

(defun push-history (&optional notrace)
  ;  Saves relevant variables onto $HISTORY.  Returns a list of the
  ;  variables saved and the status properties.
  (if* $history1
      then (push $history1 $history)
	   (setq $max-history (max $max-history (length $history)))
	   (if* (not notrace) then
	       (terpri)
	       (princ (uconcat "----- Step " (length $history) " -----"))
	       (terpri))
	   (setq $history1 nil $newrule-num 1)))

(defun push-history-manual ()
  (if* (= $manual-history-number $manual-history-frequency)
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
         (if* $akb_flag then (*throw 'akb '*noway*))
	 (undo1 (null flag))
         (princ "----- The original system is restored -----"))
        (t (undo1)
	 (princ (uconcat "----- Return to Step "(length $history)" -----"))))
  (terpri)
  (if* $history then (*throw 'kb-top '*undo*)))

(defun undo1 (&optional flag)
   (let ((popped (cond (flag (car $history))
		       (t (pop $history))))
	 (ops $operlist) rules)
     (if* (equal $resume-rule 'y) then (setq rules (r2e $rule-set)))
     (if* popped then
      (sloop for op in $st_list do (remprop op 'status))
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
     (sloop for op in (reverse $st_list) do (set-status op (pop popped)))

     (setq ops (sloop for op in ops 
		     if (not (or (memq op $operlist) (memq op $bool-ops))) 
		       collect op))

;; OPS are operators introduced during the kb-completion.
     (sloop for op in ops do (rem-arity op))
     (if* (equal $resume-rule 'y) then
	 (setq rules (sloop for eqn in rules
			   if (not (or (have-common ops (all-ops (lhs eqn)))
				       (have-common ops (all-ops (rhs eqn)))))
			     collect eqn)
	       $eqn-set (merge-list rules $eqn-set 'comp-eqn)))
     (setq $history1 nil)))
)

(defun clean-history ()
  ; Clean the history stack without effecting the current system.
  (terpri) 
  (if* (null (cdr $history)) 
      then (princ "The history is not big enough to clean.")
      else 
      (if* (cddr $history) then (setq $history (last $history)))
      (setq $prove-eqn nil)
      (princ "The history stack of RRL is cleaned."))
  (terpri))

(defun my-copylist (list &optional (depth 2))
  ; >>>>> 4/5/89
  ; Make new list from elements of "list".
  (if* (= depth 1)
      ;(mapcan 'list list)		
      (append list nil)
      (sloop for xa in list collect (my-copylist xa (sub1 depth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; saveload.lsp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+franz (declare (special l__2 l__3 l__ctr))

(defun save-rrl (&aux file)
  ; Save the current state of RRL into a file.
  (if* (setq file (open-write-file "rrl" t)) then
      (setq $eqn-set (mapcar 'rename-eqn-rule $eqn-set)
	    $post-set (mapcar 'rename-eqn-rule $post-set)
	    $rule-set (mapcar 'rename-eqn-rule $rule-set)
	    $invalid-rules (mapcar 'rename-eqn-rule $invalid-rules)
	    $aux-rset (mapcar 'rename-eqn-rule $aux-rset)
	    $del-rules (mapcar 'rename-eqn-rule $del-rules)
	    $op_rules (mapcar 'rename-op-rules $op_rules)
	    $post-ass-set (sloop for xa in $post-ass-set collect
				(cons (car xa) (cons (cadr xa) (rename-term (cddr xa)))))
	    $pair-set (mapcar 'rename-pair-rule $pair-set)
	    $prove-eqn (if* $prove-eqn then (rename-eqn-rule $prove-eqn))
	    $ans-rule (if* $ans-rule then (rename-eqn-rule $ans-rule))
	    $goal-set $goal-set
	    $op_goal_rules (mapcar 'rename-op-rules $op_goal_rules)
	    $history nil
	    $history1 nil)
      (start-push-history nil t)

      #-lispm (print $history file)
      #+lispm (print-wash-file $history file)

      (print (get-all-properties) file)
      (print (get-rest-globals) file)
      (close file)
      (terpri)
      (princ "RRL has been saved. Use 'load' to load it next time.")
      (terpri)))

(defun load-rrl (&aux file)
  ; Load the environment saved by "save" command.
  (if* (or (null (or $eqn-set $rule-set $history))
	  (ok-to-continue "Destroy the current state ? ")) then
      (if* (setq file (open-read-file "rrl")) then
	  (setq $history (read file))
	  (undo1 t)
	  (restore-properties (read file))
	  (restore-rest-globals (read file))
	  (close file)
	  (princ "Load is done.") 
	  (terpri))))

(defun get-all-properties ()
  ; return a list of proerites for each operator of $operlist.
  (sloop for op in $operlist 
	  collect (if* (numberp op) then nil
		      else
		      (list (get op 'infix)
			    (get op 'arity)
			    (get op 'arity2)
			    (get op 'predicate)))))

(defun restore-properties (props)
  ; restore the properties of operators in $operlist.
  (sloop for op in $operlist 
	for prop in props do
    (if* (not (numberp op)) then
	(putprop op (pop prop) 'infix)
	(putprop op (pop prop) 'arity)
	(putprop op (pop prop) 'arity2)
	(putprop op (car prop) 'predicate))))

(defun get-rest-globals ()
  ; return a list of global variables.
  (list $support
	$cons-of-ts 		
	$ckb_flag 		
	$akb_flag 		
	$func-name		
	$paramodulate		
	$fopc-lrpo		
	$set_pred		
	$def-domains    
	$nusereqn
        $induc
	$trace-proof		
	$goal-reduce
	$anspred	
	$pick-rule-str
	$crit-with-str
	$del_rule_str	
	$mark_rule_str	
	$rule-size	
	$immediate	
	$more-break	
	$idem		
	$norm_str	
	$blocking-on    
	$prove-method 	
        $ordering       
	$build-rules 
	$cycle-rule		
	$instant
	$instant-seeds
	$step-deep
	$over-rewrite
	$f-weights
	$gene-num
	$symmetry-dels          
	$polynomial
	$post-bound
	))

(defun restore-rest-globals (globals)
  ; return a list of global variables.
  (setq	$support 		(pop globals)
	$cons-of-ts 		(pop globals)
	$ckb_flag 		(pop globals)
	$akb_flag 		(pop globals)
	$func-name		(pop globals)
	$paramodulate		(pop globals)
	$fopc-lrpo		(pop globals)
	$set_pred		(pop globals)
	$def-domains            (pop globals)
	$nusereqn               (pop globals)
        $induc                  (pop globals)
	$trace-proof		(pop globals)
	$goal-reduce            (pop globals)
	$anspred	        (pop globals)
	$pick-rule-str          (pop globals)
	$crit-with-str          (pop globals)
	$del_rule_str	        (pop globals)
	$mark_rule_str	        (pop globals)
	$rule-size	        (pop globals)
	$immediate	        (pop globals)
	$more-break	        (pop globals)
	$idem		        (pop globals)
	$norm_str	        (pop globals)
	$blocking-on            (pop globals)
	$prove-method 	        (pop globals)
        $ordering               (pop globals)
	$build-rules            (pop globals)
	$cycle-rule		(pop globals)
	$instant		(pop globals)
	$instant-seeds		(pop globals)
	$step-deep		(pop globals)
	$over-rewrite	        (pop globals)
	$f-weights              (pop globals)
	$gene-num               (pop globals)
	$symmetry-dels          (pop globals)
	$polynomial             (pop globals)
	$post-bound             (pop globals)
	))

(defun rename-term (term)
  (setq l__2 nil l__3 nil l__ctr 0) 
  (initsym 'x)
  (get-var-substitution term)
  (applysubst l__2 term))

(defun rename-eqn-rule (eqn)
  (setq l__2 nil l__3 nil l__ctr 0) 
  (initsym 'x)
  (get-var-substitution (lhs eqn))
  (get-var-substitution (rhs eqn))
  (get-var-substitution (ctx eqn))
  (setq l__2 (sloop for xa in l__2 if (nequal (car xa) (cdr xa)) collect xa))
  (applysubst-rule l__2 eqn))

(defun rename-pair-rule (pair)
  (list (car pair) (rename-eqn-rule (cadr pair)) 
	(rename-eqn-rule (caddr pair)) (cadddr pair)))

(defun rename-op-rules (op_rules)
  (cons (car op_rules) (mapcar 'rename-eqn-rule (cdr op_rules))))

(defun get-var-substitution (term &aux l1)
  (if* (and term (variablep term)) then
      (if* (assoc0 term l__2) then nil
	  elseif (member0 (get_pname term) l__3)
	  then
	  (sloop while (member0 (get_pname (setq l1 (newsym 'x))) l__3) do nil)
	  (push (get_pname l1) l__3)
	  (push (cons term l1) l__2)
	  else
	  (push (cons term term) l__2)
	  (push (get_pname term) l__3))
      else
      (mapcar 'get-var-substitution (args-of term))))

(defun applysubst-rule (sigma eqn)
  ; apply substitution "sigma" to "eqn", where "eqn" is either an equation
  ; or a rule.
  (append (list (applysubst sigma (lhs eqn)) 
		(applysubst sigma (rhs eqn))
		(applysubst sigma (ctx eqn)))
	  (cdddr eqn)))



