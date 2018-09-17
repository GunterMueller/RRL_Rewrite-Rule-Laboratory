;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "RRL")


(defmacro default-flag (flag default-value)
  `(cond ((assq ,flag $defaults) (cdr (assq ,flag $defaults)))
	 (t ,default-value)))

(defun pre-init ()
  ; Read in a list of default flag values from "init-rrl-flag".
  (setq user-top-level 		'rrl
;        sharp-backslash-end     148 ;; #\end
;	$example-dir            #+franz "~//rrl//demo//"
;	                        #+lispm "sutra:examples;"
	$cons-of-ts 		nil
	$ckb_flag 		nil
	$akb_flag 		nil
	$operlist		nil
	$test 			nil
	$in-port                nil
	$log-port		nil
        $separators		'(|(| |)| |,| |;| |]| if == --->) 
	$func-name		'a
	$fast-match     	1
	$paramodulate		'n
	$trace_flag		2
	$over-rewrite           3
	$symmetry-check         t
	$many-args              4
	$false-rhs              nil
	$fopc-lrpo		nil
	$post-bound             100
	$guest-eqn              nil
	$set_pred		nil
	$try                    nil
	$new-ac                 nil)
  (if (boundp '$st_list)
      then (loop for op in $st_list do (remprop op 'status))
      else (setq $st_list nil))
  (if (my-probef 'init-rrl.flag) then 
    (let ((in-port (car (errset (infile 'init-rrl.flag) nil))))
      (setq $defaults
	      (loop while (nequal (tyipeek-spa-cr in-port) -1)   ; "-1" = EOF 
		    collect (cons (read-atom 'none in-port)
				  (read-atom 'none in-port))))
      (close in-port))
    else (setq $defaults nil)))

(defun sys-flag-init ()
  (setq 
	$confluent      nil		; confluence flag.
	$sufficient     nil		; sufficient completeness flag.
	$cons-of-ts     nil             ; constructors of testset.
	$testset	nil
	$def-domains    nil))

(defun initialize ()
  ; Initialize the global variables.
  (clear-operators)			; clears $operlist
  (loop for op in $st_list do (remprop op 'status))
      (setq 
	;; Global Counters or Indexes
	$symbnum	1		; new variable number
	$nrules		0		; number of rules generated 
	$nusereqn	0		; number of user's equations.
	$ncritpr	0		; number of critical pairs
	$unblocked      0		; number of unblocked equations.
	$symmetry-dels  0		; number of deleted unifers by symmetry.
     )
     (setq
	;; Rule, Equation and Proposition Sets
	$eqn-set	nil		; equation set
	$pair-set       nil             ; for ac-completion only
	$post-set	nil		; postponed equations
	$post-ass-set	nil		; postponed propositions
	$rule-set	nil		; rule set
	$invalid-rules	nil		; rule set
	$aux-rset	nil		; auxiliary rule set
;	$op_rules	nil		; a_list of form: ((op . (rules))...)
;; $op_rules has eq(x,x) -> true and x = x -> true initially to
;; fix problems with  not(eq(e,e)) etc.
;;
	$op_rules	(list
 	  (cons 'eq (list (make-new-rule '(eq x x) '(true) nil '(EQ))))
 	  (cons '=  (list (make-new-rule '(= x x) '(true) nil '(=EQ))))
	  (cons 'not (list (make-new-rule '(not (true)) '(false) nil '(NOT))
			   (make-new-rule '(not (false)) '(true) nil '(NOT))
			   (make-new-rule '(not (not x)) 'x nil '(NOT))))
                          )
	$nrules         0     ; to reset after the copying above
	$del-rule-nums	nil		; deleted rule numbers
	$del-rules	nil		; deleted rules
	$del-eqns	nil		; eqns made from deleted rules
	$history	nil		; storage for undo operation
	$history1	nil		; auxilliary storage for undo operation
	$ckb_flag   	nil	 	; conditional rewriting flag.
    )
   (setq 
	;; Operators with properties.
	$eqop_list	nil		; equivalent operator list
	$glob_prec	nil		; precedence relations
	$st_list	nil		; operators with status assigned
	$f-weights      nil             ; operators with its weight
        $commutative	nil		; commutative operators
        $associative	nil		; associative operators
	$ac             nil             ; ac-operators
	$divisible      nil		; divisible operators
	$translist      nil		; transitive operators
	$constructors   nil             ; operators declared as constructors
	$type-constructors   nil        ; constructors paritioned by type
	$free-constructors   nil        ; 
     )

    (setq
	;; Time Statistics
	$add_time	0		; time spent while adding rules
	$norm_time	0		; time spent in normalization
	$reduce_time	0		; time spent in reduction
	$ord_time	0		; time spent in ordering
	$unif_time	0		; time spent in unification
	$proc_time	0		; total time by processor
        $block_time     0               ; used by blocked critical
	$brt_time	0 		; time spent in brt.
     )
    (setq 
	;; Proof methods
        $induc          nil             ; explicit induction flag.
 	$induc-vars     nil             ; variables for induction proof.
        $prove-eqn      nil             ; containing proving equation.
        $witness-eqn    nil             ; containing proving equation.
	$trace-proof		nil	; trace the result of refutational proof.
	$cover-sets     nil             ; recursive definition cover sets.
	$non-comm-cover-sets    nil     ; recursive definition cover sets.
	$defin-depend   nil             ; definition dependency.
	$gene-num       0               ; definition dependency.
     )
    (setq
	;; Narrowing Stuff
	$narrow         nil             ; set narrowing equal false
	$ans-rule       nil             ; answer's derived using narrowing
	$goal-set	nil		; goal set used in narrowing
	$goal-reduce	nil		; decides whether to use goal rules for reduction
	$op_goal_rules	nil		; like $op_rules (used in narrowing)
	$anspred	'solution	; name of answer predicate used in narrowing
     )
    (setq
	;; Strategies
	$pick-rule-str	(default-flag 'pick-rule 'l) 
	$crit-with-str	(default-flag 'critical-with 'm)
	$del_rule_str	(default-flag 'delete-rule 2)
	$mark_rule_str	(default-flag 'mark-rule 'l)
	$rule-size	(default-flag 'rule-size 's)
        $ex1            (default-flag 'ext-rule-size1 1)
        $ex2            (default-flag 'ext-rule-size2 2)
	$immediate	(default-flag 'post-bound '6)
	$post-ass-list	(default-flag 'post-ass-list 'q)
	$more-break	(default-flag 'more-break 'l)
	$idem		(default-flag 'fopc-crit '1)
	$norm_str	(default-flag 'normalization 'o)
	$check-symmetry (default-flag 'symmetry t)
	$prime-acu      (default-flag 'prime-acu t)
	$blocking-on    (default-flag 'blocking 'n)
	$no-history     (default-flag 'history nil)
	$prove-method 	(default-flag 'prove-method  's)
        $ordering       (default-flag 'ordering 'l)
	$lrpo           (default-flag 'lrpo t)	; lexico-recursive-path-order.

	$in-fopc	nil		; true if a first order formula has
	                                ; been read in (DC 9/3/86)
	$build-rules nil
	$reduce-bound           1000
	$reduce-system 		3
	$support                nil
     )
    (setq
        ; Auto-ordering Stuff.
	$newop-terms    nil		; used in autoorder.
	$auto-sugg      nil     	; variable used in "auto-orient".
	$max-history    0		; maximum history having been atteined
	$newop-first	(default-flag 'new-operator 1)
	$rl-first	(default-flag 'status 2) ; give the rl-status first.
	$pre-first 	(default-flag 'precedence 1) ; give equivalence first.
	$eq-arity	(default-flag 'equal-arity 'y)
			; the same arity operators can be eq.
	$resume-rule    (default-flag 'resume-rule 'n) 
			; resume rules when undo.
	$post-posi	(default-flag 'postpone-position 2)
			; postpone suggestion flag.
	$post-max	(default-flag 'max-postpone 9999)
			; maximum of postponed equation.
	$runtime-max	(default-flag 'max-runtime 0)
			; maximum of postponed equation.
	$newrule-max	(default-flag 'max-new-rule 1000)
			; maximum of new generated rules
	$manual-history-frequency 0	; determines the frequency of saving
	                                ; historys under manual orienting
					; 0 means always save history
        $manual-history-number	0)	; current history number relative 
                                        ; to $manual-history-frequency

    (setq
	$polynomial             nil
	$cycle-rule		nil
	$cycle-op-rules         nil
	$character-rules        nil
	$p-commut-rules         nil
	$instant		nil
	$instant-seeds          nil
	$premises-set		nil
	$var-premises		nil
	$used-rule-nums         nil
	$poly-homo-rules        nil
      )

    (if $polynomial (poly-initialize))
    (init-bool-ops)
    (sys-flag-init))

(defun reset-rrl ()
  ; Reset the global variables.
  (let ((eqns (nconc (mapcar 'r2e $rule-set) $eqn-set $post-set)))
     (initialize)
     (setq $eqn-set eqns)
     (terpri) (princ "RRL is reset.") (terpri)))

(defun r2e (xa) (make-eqn (lhs xa) (rhs xa) (ctx xa) (rule-source xa)))

(defun init () (setq $in-port nil) (initialize) (reset))
