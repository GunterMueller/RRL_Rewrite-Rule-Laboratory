;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")

(defmacro default-flag (flag default-value)
  `(cond ((assq ,flag $defaults) (cdr (assq ,flag $defaults)))
	 (t ,default-value)))

(defun pre-init ()
  ; Read in a list of default flag values from "init-rrl-flag".
  (setq user-top-level 		'rrl
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
	$set_pred		nil
	$try                    nil
	$new-ac                 nil)
  (if* (boundp '$st_list)
      then (sloop for op in $st_list do (remprop op 'status))
      else (setq $st_list nil))
  (if* (my-probef 'init-rrl.flag) then 
    (let ((in-port (infile 'init-rrl.flag)))
      (setq $defaults
	      (sloop while (nequal (tyipeek-spa-cr in-port) -1)   ; "-1" = EOF 
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
  (sloop for op in $st_list do (remprop op 'status))
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
	$condi-dominate-rules 	nil	; rule set
	$invalid-rules	nil		; rule set
	$rule-names     nil             ; names for rewrite rules.
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
	$complete-ops   nil             ; completely defined ops
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
	$guest-eqn      nil             ; contain an equation for ...
        $witness-eqn    nil             ; containing proving equation.
	$trace-proof	nil        	; trace a refutational proof.
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
	$no-history     (default-flag 'history t)
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

    (setq $cover-auto-level 2
	  $strong-induc nil
	  $abstract-proof t
	  $multi-term-induc t)

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

(defun init () (setq $in-port nil) (initialize) (rrl))


;;;;;;;;;;;;;;;; from toplevel.lsp ;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro start-timer (&optional x)
  (if x `(setq ,x (get-internal-run-time)) `(get-internal-run-time)))
(defmacro run-time (x)  `(- (get-internal-run-time) ,x))
(defmacro time-in-sec (x) `(/ (float ,x) (float internal-time-units-per-second)))

#|(defmacro add-time (variable body)
  ; instead of having to use run-time and set-timer in the code
  ; this macro adds to variable the time required to execute body
  `(let (v1)
       (start-timer v1)
       (prog1
	   ,body
	 (setq ,variable (+ ,variable (run-time v1))))
       ))
|#

(defun start-up ()
  ;  Top-most-level function.  Starts up the RRL system.
  (terpri)
  (sloop for xa in '(
"****************************************************************************"
"****                                                                    ****"
"****        WELCOME  TO  REWRITE  RULE  LABORATORY  (RRL 4.1)           ****"
"****                                                                    ****"
;"****  (c) Copyright 1991 The University of Iowa.  All rights reserved.  ****"
"****************************************************************************"
) do (princ xa) (terpri))
  (princ "Start at: ") (date)

  ; The following are equates and some variables that have to be set before
  ; calling INITIALIZE.

  (pre-init)
  (initialize)
  (if* (my-probef 'init-rrl.cmd) then 
     (setq $in-port (infile "init-rrl.cmd"))
     (terpri) (princ "Excecuting 'init-rrl.cmd' ...") (terpri))

  (start-timer $begin-time)
  (setq $time-when-last-call $begin-time)
  (rrl)
  )

(defun rrl ()
  ;; common lisp doesn't yet know that top-level is (rrl).
  ;; so we do this explicitly here & call (exit) for leaving with q.
  ;;   -- siva 2/9/90
  (sloop while (*catch 'reset (rrl-aux)) do (setq $in-port nil))
  )

(defun rrl-aux ()
  ; This is the top level function that interacts with the user and
  ; dispatches the various commands.
  ; how about changing to user-selectq ?? It's not easy.
  (prog (*readtable* stime)
    top-rrl
   (start-timer stime)

#-franz (setq *readtable* *rrl-readtable*)
    (show-message  '( 
""
"Type Add, Akb, Auto, Break, Clean, Delete, Disable, Enable, Grammar, History,"
"     Init, Kb, List, Load, Log, Makerule, Manager, Namerule, Norm, Option, "
"     Operator, Prove, Quit, Read, Refute, Save, Stats, Suffice, Time, Undo, "
"     Unlog, Write or Help."))
    (princ "RRL-> ")
    (selectq					
      (choose-str (read-atom 'none)
		  '(add akb auto break clean delete disable enable help grammar history init
		    kb list load log makerule manager namerule narrow norm option 
		    operator prove quit read refute save solve stats
		    suffice test time undo unlog write xin))
      (add (setq $eqn-set (nconc $eqn-set (read-input t))))
      (akb (if* (equal $post-max 9999) (setq $post-max 4))
	   (if* (equal $newrule-max 1000) (setq $newrule-max 50))
	   (auto-kb))
      (auto (setq $in-port (open-read-file "cmd")))
      (break 
#-kcl  (break "to LISP. Type (rrl) or :c to resume; (init) to initialize.")
#+kcl  (break "to LISP. Type (rrl) or :r to resume; (init) to initialize.")
      )
      (clean (clean-history))
      (delete (delete-sys))
      (disable (disable-rules))
      (enable (enable-rules))
      (grammar (help-file $grammar))
      (help    (help-file $helpfile))
      (history (setq $history1 nil) (start-push-history nil nil t))
      (init (initialize) (terpri) (princ "RRL is initialized.") (terpri))
      (kb (if* $narrow then
	      (setq $narrow (ok-to-continue "Continue previous linear completion ? ")))
	  (setq $akb_flag nil)
	  (start-kb))
      (list (display))
      (load (load-rrl))
      (log (setq $log-port (open-write-file "cmd" nil)))
      (makerule (setq $eqn-set (append $eqn-set $post-set) 
		      $post-set nil)
		(order-eqns))
      (manager (x_prover))
      (xin (x_prover))
;;      (narrow (linear))
;;      (norm (normalize))
      (namerule (name-last-rule))
      (option (run-kb-options))
      (operator (operator-options))
;;      (protocol (top-level-protocol))
      (prove (prove))
      (quit (quit-rrl))
      (read (setq $eqn-set (nconc $eqn-set (read-input nil))))
      (refute (refute-eqn))
      (save (save-rrl))
;;     (solve (top-level-solve))
      (stats (give-stat))
      (suffice (start-test))
      (test (test-rrl))
      (time (report-current-time))
      (undo (setq $akb_flag nil) (*catch 'kb-top (undo t))); (display)
      (unlog (close-log))
      (write (writef-sys))
      (otherwise ;(drain-it $in-port)
	 (princ "Sorry, I cannot do that.") (terpri)
	 (if* $test then (quit-rrl))))

    (format t "Time for this command = ~,3f sec      Total time = ~,3f sec~%" 
	    (time-in-sec (run-time stime)) 
	    (time-in-sec (run-time $begin-time)))

    (go top-rrl)))

(defun report-current-time ()
  (princ "The current time is: ") (date) 
  (format t "The cumulated time since the last call is: ~,3f sec~%" 
	    (time-in-sec (run-time $time-when-last-call)))
  (start-timer $time-when-last-call))

;delete shouldn't be here in toplevel.
(defun delete-sys ()
  ;  Lets the user delete an equation or a rule from the current set.
  ;  It has its own sub-toplevel for related options.
  (user-selectq
    (abort    "- Abort and return to top level." nil)
    (equation "- Delete equation." (delete-eqn))
    (list    " - List numbered equations and rules." (display)) 
    (rule    " - Delete rule." (delete-rule))))

(defun delete-rule ()
  ; Deletes specified rule from the rule set.
  (if* (is-empty-line $in-port)
	then (princ "Type a list of deleting rules' numbers or names : "))
  (let ((rule-nums (read-args $in-port)) flag d-ops)

    ;; HZ: the user may give rule-name.
    (setq rule-nums (sloop for xa in rule-nums collect (name2rulenum xa)))

    (sloop for rule in $rule-set do
	  (cond ((member0 (ruleno rule) rule-nums)
		 (clean-rule rule)
		 (setq flag t
		       d-ops (union d-ops (union (op-list (lhs rule))
						 (op-list (rhs rule)))))
		 (princ "Deleted rule: ")
		 (write-rule rule) (terpri))))
    (if* flag then (sys-flag-init))
    (clean-ops d-ops)
    flag))

(defun delete-eqn ()
  ;  Deletes specified equation from the equation set.
  (prog (flag l1 l2 l3 d-ops)
    delete-top
    (if* (is-empty-line $in-port)	; no argument pending?
	then (princ "Type delete equation numbers (or L to list) : "))
      (setq l1 (read-args $in-port))
      (if* (eq (car l1) 'l)
	  then (display nil)			; display equations only.
	       (go delete-top))
      (sloop with l4 = (length $eqn-set)
	    for n in l1 do
        (cond ((not (numberp n))
	       (princ (uconcat n " is not a number.")) (terpri))
	      ((> n l4) (push n l3))
	      (t (push n l2))))
      (setq l1 nil)
      (if* l2 then
	  (sloop for x in $eqn-set	; find equation and extract
		for i from 1 do
	    (if* (member0 i l2)
		then (princ (uconcat "Deleted equation #" i ": "))
	        (terpri) (princ "  ") (write-eqn x)
		(setq $eqn-set (remove0 x $eqn-set 1)
		      flag t
		      d-ops (union d-ops (union (op-list (lhs x))
					        (op-list (rhs x))))))))
      (if* l3 then
	  (sloop for x in $post-set	; find equation and extract
		for i from (1+ (length $eqn-set)) do
	    (if* (member0 i l3)
		then (princ (uconcat "Deleted equation #" i ": "))
	        (terpri) (princ "  ") (write-eqn x)
		(setq $post-set (remove0 x $post-set)
		      flag t
		      d-ops (union d-ops (union (op-list (lhs x))
					        (op-list (rhs x))))))))

      (if* (not flag)
	  then (princ "No equation can be deleted.") (terpri)
	  else (clean-ops d-ops))
      (return flag)))

; This function is too expensive.
;(defun delete-ops (ops)
;   (sloop for op in ops if (not (exist-op op)) do
;	(setq $operlist (remove0 $operlist op)
;	      $constructors (remove0 $constructors op))))

(defun order-eqns (&optional dis &aux l2 rule)
  ;  Adds RULES to the rule set without computing critical pairs.
  (setq $newrule-num 1 $small-depth 3)
  (if* (or $ac $commutative) then
     (setq $eqn-set (sloop for eq in $eqn-set collect (flatten-eqn eq)))
     (setq $post-set (sloop for eq in $post-set collect (flatten-eqn eq))))
  (sloop while $eqn-set do
     (setq l2 (pop $eqn-set)
           rule (*catch 'kb-top
		  (*catch 'refuted 
		    (*catch 'reset (process-equation l2)))))
     (cond ((null rule) nil)	
	   ((member0 rule '(*newop* *undo* *kb-top*)) nil)
	   ((member0 rule '(*incons* *reset*))
	    (setq $eqn-set (cons l2 $eqn-set))
	    (return))
	   (t (if* (> $trace_flag 1) then 
		   (terpri) (princ " Adding Rule: ") (write-rule rule))
	      (add-associate-list (op-of (lhs rule)) rule $op_rules)
	      (setq $rule-set (nconc $rule-set (ncons rule))))))
 (sys-flag-init)
 (if* dis then (display)
     (if* $lrpo then (princ "The system is terminating.")
	 else (princ "The system is hopefully terminating.")) (terpri)))
  
(defun close-log ()
  (if* $log-port then
    (princ (uconcat "Log file '" (truename $log-port) "' is closed."))
    (close $log-port) (setq $log-port nil)
   else (princ "No log file.")) (terpri))

(defun quit-rrl ()
  ;(if $in-port (close $in-port))
  (close-log)
  (terpri)
  (princ (uconcat "Goodbye " 
#+kcl (getenv 'USER) 
#-kcl "my friend"
      ".")) (terpri)
   (princ "Finish at: ") (date) (terpri)
   (terpri)
#+kcl (bye)
#-kcl (quit)
)

(defun test-rrl (&aux l1)
   (push $in-port $save-in-port)
   (setq $test t
	 $trace_flag 1
	 $in-port (open-read-file "cmd"))
   (if* $in-port then
	(setq l1 (uconcat (truename $in-port) 'cp)
	      $log-port (outfile l1))
        (princ (uconcat "    '" l1 "' is open to write.")) (terpri)))

#|
(defun top-level-solve()
  (let ((eqn (read-this-eqn 'solve)))
    (if* eqn
	(progn
	  (format t "~% ~% Solving ")
	  (write-eqn eqn)
	  (solve (lhs eqn) (rhs eqn))))))
|#

(defun date () ; print the current date.
  (let (sec min hou day mon yea)
    (multiple-value-setq (sec min hou day mon yea) (get-decoded-time))
    (princ hou) (princ ":") (princ min) (princ ":") (princ sec) (princ " ")
    (princ (case mon
		  (1 "Jan")
		  (2 "Feb")
		  (3 "Mar")
		  (4 "Apr")
		  (5 "May")
		  (6 "Jun")
		  (7 "Jul")
		  (8 "Aug")
		  (9 "Sep")
		  (10 "Oct")
		  (11 "Nov")
		  (12 "Dec")
		  (t "ERROR")))
    (princ " ") (princ day) 
    (princ " ") (princ yea)
    (terpri)))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; code for implementing rule names
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun name-last-rule (&aux name)
  (terpri) (princ "Please give a name to the NEWEST rewrite rule: ")
  (sloop while (null name) do
	(when (and (setq name (read-atom 'end))
		   (not (assoc name $rule-names)))
	      (push (cons name $nrules) $rule-names)
	      (princ "The name for Rule [") (princ $nrules) (princ "] is ")
	      (princ name) (princ ".") (terpri)
	      (return $rule-names))
	(setq name nil)
	(princ "Try a new name!")
	))

(defun name2rulenum (name)
  ;; retrun either the corresponding rule number or the name itself.
  (or (cdr (assoc name $rule-names)) (if (numberp name) name -1)))

;; disable-rules makes rules inactive, i.e., not for rewriting.
;; enable-rules turns inactive rules into active.
(defun disable-rules () (disable-rules-aux))
(defun enable-rules () (disable-rules-aux t))

(defun disable-rules-aux (&optional enable &aux rule-nums)
  (if* (is-empty-line $in-port)
      then (princ "Type a list of rules' numbers or names : "))
  (setq rule-nums (sloop for xa in (read-args $in-port) collect (name2rulenum xa)))
  (sloop for rule in $rule-set do
	(when (member0 (ruleno rule) rule-nums)
	      (cond (enable 
		     (enable-rule rule)
		     (princ "Active rule: "))
		    (t 
		     (disable-rule rule)
		     (princ "Inactive rule: ")))
	      (write-rule rule) (terpri))))

(defun disable-rule (rule)
  (if (ref-extra-pre-variables rule)
      (setq $condi-dominate-rules (delete0 rule $condi-dominate-rules 1))
    (delete0 rule (assq (op-of (lhs rule)) $op_rules))))

(defun enable-rule (rule) 
  (if (ref-extra-pre-variables rule) 
      (push-end rule $condi-dominate-rules)
    (add-associate-list (op-of (lhs rule)) rule $op_rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; end of rule names ;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;; from statistics.lsp ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun give-stat (&optional port)
   (terpri port)
   (display-kb-stat nil port)
   (terpri port)
   (if* $constructors 
     then (princ (uconcat "Constructors : " (display-ops $constructors)) port) 
     else (princ "No constructors." port))			
   (terpri port)    (terpri port) 
   (princ "Termination Ordering : " port)
   (if* (eq $ordering 'm) 
     then (princ "Manual" port) (terpri port) 
     elseif (eq $ordering 's)
     then (princ "Size + Lexicographic Ordering." port)
     else (if* $lrpo
	   then (princ "Lexicographic Recursive Path Ordering (LRPO)" port) 
	   else (princ
		 "Manual and Lexicographic Recursive Path Ordering (LRPO)" port)) 
		(terpri port)
	  (display-op-stats port))
   (princ "Normalization Strategy : " port)
   (princ (selectq $norm_str
	    (e "Efficient Innermost")
	    (i "Innermost")
	    (m "Mixed")
	    (o "Outermost")) port) 
   (terpri port)
   (princ "Critical Pair Strategy : " port)
   (princ (caseq $pick-rule-str
	    (m "Manual chosen rule with ")
	    (e "Earliest generated smallest rule with ")
	    (l "Latest generated smallest rule with ")
	    (o "Old strategy for ac with ")
	    (f "First unmarked rule with ")) port)
   (princ (caseq $crit-with-str
	    (m "all marked rules.")
	    (o "all older rules.")
	    (a "all other rules.")
            ((h1 h2) "manually chosen rule.")) port) 
   (terpri port))

#-franz
(defun nrm-time (n) (/  (float n) internal-time-units-per-second))

(defun display-kb-stat (&optional total port)
   (let ((x1  #-franz (float $proc_time)
	      #+franz $proc_time)
	 (port2 (if port port t)))
      (princ (uconcat "Number of rules generated            =  " $nrules) port)
      (terpri port)
      (princ (uconcat "Number of rules retained             =  " 
                      (length $rule-set)) port)
      (terpri port)
      (princ (uconcat "Number of critical pairs             =  " $ncritpr) port) 
      (terpri port)
      (if* (eq $blocking-on 'y) then
       (princ (uconcat "Number of unblocked critical pairs   =  " $unblocked) port)
       (terpri port))

#+franz     (cprintf  "CPU Time used                        = %.2f sec" x1 port) 
#-franz (format port2 "Time used                            = ~6,2f sec" (nrm-time x1))
      (terpri port)
#+franz  
   (if* (greaterp x1 0.009) then
       (cprintf " Time spent in normalization         = %.2f sec" $norm_time port)
       (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $norm_time x1)) port) (terpri port)
       (cprintf " Time spent in unification           = %.2f sec" $unif_time port)
       (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $unif_time x1)) port) (terpri port)
       (cprintf " Time spent in ordering              = %.2f sec" $ord_time port)
       (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $ord_time x1)) port) (terpri port)
       (cprintf " Time spent in simplifying the rules = %.2f sec" $add_time port)
       (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $add_time x1)) port) (terpri port)
       (if* (greaterp $brt_time 0.009) then
        (cprintf " Time spent in boolean translation   = %.2f sec" $brt_time port)
        (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $brt_time x1)) port) (terpri port))
       (if* (eq $blocking-on 'y) then
	(cprintf " Time spent in blocking              = %.2f sec" $block_time port)
        (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $block_time x1)) port) (terpri port))
    )
#-franz
   (if* (greaterp x1 0.009) then
       (format port2 " Time spent in normalization         = ~6,2f sec " (nrm-time $norm_time))
       (format port2 " (~f percent of time)"
			(truncate (* 100 $norm_time) x1)) (terpri port)
       (format port2 " Time spent in unification           = ~6,2f sec "
	                      (nrm-time $unif_time))
       (format port2 "  (~f percent of time)"
			(truncate (* 100 $unif_time) x1)) (terpri port)
       (format port2 " Time spent in ordering              = ~6,2f sec "
	                    (nrm-time $ord_time))
       (format port2 "  (~f percent of time)"
			(truncate (* 100 $ord_time) x1)) (terpri port)
       (format port2 " Time spent in simplifying the rules = ~6,2f sec "
	       (nrm-time $add_time))
       (format port2 "  (~f percent of time)"
			(truncate (* 100 $add_time) x1)) (terpri port)
       (if* (greaterp $brt_time 0.009) then
        (format port2 " Time spent in boolean translation   = ~6,2f sec "
		(nrm-time $brt_time))
        (format port2 "  (~f percent of time)"
			(truncate (* 100 $brt_time) x1)) (terpri port))
       (if* (eq $blocking-on 'y) then
	(format port2 " Time spent in blocking              = ~6,2f sec "
		(nrm-time $block_time))
        (format port2 "  (~f percent of time)"
		       (truncate (* 100 $block_time) x1)) (terpri port))
    )
    (if* total then
#+franz (cprintf  "Total time (including 'undo' action) = %.2f sec" total)
#-franz (format port2 "Total time (including 'undo' action) = ~f sec" (nrm-time total))
     (terpri port) (terpri port))))

(defun display-op-stats (&optional port)
  ; Displays to the user the current equivalence, precedence and
  ; status relation among operators in the system.  Returns NIL.
  (terpri port)
  (if* $eqop_list
      then (princ "Equivalence relation among operators now is:" port) (terpri port)
	   (sloop for xa in $eqop_list do 
	      (princ (uconcat "Equivalent set: " (display-ops xa)) port) (terpri port))
      else (princ "There are no equivalent operators." port) (terpri port))
  (terpri port)
  (if* $glob_prec
      then (princ "Precedence relation now is: " port) (terpri port) 
	   (sloop for xa in $glob_prec do
		 (princ (uconcat "   " (car xa) " > ") port)
		 (sloop for xb in (cdr xa) do (princ (uconcat xb " ") port))
		 (terpri port))
      else (princ "There is no ordering yet in the precedence relation." port)
	   (terpri port))
  (terpri port)
  (if* $st_list
      then (princ "Operators with status are:" port) (terpri port)
	   (sloop for op in $st_list do
		 (princ (uconcat "   " op) port)
		 (if* (eq (get op 'status) 'lr)
		     then (princ " with left-to-right status." port)
		     else (princ " with right-to-left status." port))
		 (terpri port))
      else (princ "There are no operators with status." port) (terpri port))
  (if* $ac then (terpri port)
    (princ (uconcat "Associative & commutative operator set = "
		    (display-ops $ac)) port) (terpri port))
  (if* $commutative then (terpri port)
    (princ (uconcat "Commutative operator set = " (display-ops $commutative)) port)
    (terpri port))
  (if* $translist then (terpri port)
    (princ (uconcat "Transitive operator set = " (display-ops $translist)) port)
    (terpri port))
  (display-type-arity $operlist port))

(defun display-ops (ops)
  (if* ops then
   (prog (res)
     (setq res (uconcat "{ " (pop ops)))
     (sloop for op in ops do (setq res (uconcat res ", " op)))
     (return (uconcat res " }")))
   else "{ }"))     
