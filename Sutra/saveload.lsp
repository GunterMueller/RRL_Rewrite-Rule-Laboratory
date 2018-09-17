;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "RRL")

#+franz (declare (special l__2 l__3 l__ctr))

(defun save-rrl (&aux file)
  ; Save the current state of RRL into a file.
  (if (setq file (open-write-file "rrl" t)) then
      (setq $eqn-set (mapcar 'rename-eqn-rule $eqn-set)
	    $post-set (mapcar 'rename-eqn-rule $post-set)
	    $rule-set (mapcar 'rename-eqn-rule $rule-set)
	    $invalid-rules (mapcar 'rename-eqn-rule $invalid-rules)
	    $aux-rset (mapcar 'rename-eqn-rule $aux-rset)
	    $del-rules (mapcar 'rename-eqn-rule $del-rules)
	    $op_rules (mapcar 'rename-op-rules $op_rules)
	    $post-ass-set (loop for xa in $post-ass-set collect
				(cons (car xa) (cons (cadr xa) (rename-term (cddr xa)))))
	    $pair-set (mapcar 'rename-pair-rule $pair-set)
	    $prove-eqn (if $prove-eqn then (rename-eqn-rule $prove-eqn))
	    $ans-rule (if $ans-rule then (rename-eqn-rule $ans-rule))
	    $goal-set $goal-set
	    $op_goal_rules (mapcar 'rename-op-rules $op_goal_rules)
	    $history nil
	    $history1 nil)
      (start-push-history nil t)

      #-lispm (print $history file)
      #+lispm (print-wash-file $history file)

      (print (get-properts) file)
      (print (get-rest-globals) file)
      (close file)
      (terpri)
      (princ "RRL has been saved. Use 'load' to load it next time.")
      (terpri)))

(defun load-rrl (&aux file)
  ; Load the environment saved by "save" command.
  (if (or (null (or $eqn-set $rule-set $history))
	  (ok-to-continue "Destroy the current state ? ")) then
      (if (setq file (open-read-file "rrl")) then
	  (setq $history (read file))
	  (undo1 t)
	  (restore-properties (read file))
	  (restore-rest-globals (read file))
	  (close file)
	  (princ "Load is done.") 
	  (terpri))))

(defun get-properts ()
  ; return a list of proerites for each operator of $operlist.
  (loop for op in $operlist 
	  collect (if (numberp op) then nil
		      else
		      (list (get op 'infix)
			    (get op 'arity)
			    (get op 'arity2)
			    (get op 'predicate)))))

(defun restore-properties (props)
  ; restore the properties of operators in $operlist.
  (loop for op in $operlist 
	for prop in props do
    (if (not (numberp op)) then
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
  (setq l__2 (loop for xa in l__2 if (nequal (car xa) (cdr xa)) collect xa))
  (applysubst-rule l__2 eqn))

(defun rename-pair-rule (pair)
  (list (car pair) (rename-eqn-rule (cadr pair)) 
	(rename-eqn-rule (caddr pair)) (cadddr pair)))

(defun rename-op-rules (op_rules)
  (cons (car op_rules) (mapcar 'rename-eqn-rule (cdr op_rules))))

(defun get-var-substitution (term &aux l1)
  (if (and term (variablep term)) then
      (if (assoc term l__2) then nil
	  elseif (member (get_pname term) l__3)
	  then
	  (loop while (member (get_pname (setq l1 (newsym 'x))) l__3) do nil)
	  (push (get_pname l1) l__3)
	  (push (cons term l1) l__2)
	  else
	  (push #+franz (cons term term) 
                #-franz (cons term (intern (get_pname term) *rrl-package*))
		          ;; To make sure names are interned in RRL package
                     l__2)
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



