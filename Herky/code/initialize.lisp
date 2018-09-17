(in-package "USER")

#+kcl (defun gc (&optional (level 3)) (gbc level))

(defun init-herky ()
  (sloop for xa in *herky-banner* do (princ xa) (terpri))
  (init))

(defmacro start-herky () `(startup))

(defun startup ()
  ;  Top-most-level function.  Starts up the RRL system.
  (sloop for xa in *herky-banner* do (princ xa) (terpri))
  ; The following are equates and some variables that have to be set before
  ; calling INITIALIZE.
  (princ "Start at: ") (date) 

  (init-char-type-table)
  (init-var-table)
  (init-op-table)
  (pre-init)
  (when (probef "herky-init.cmd") 
    (initialize)
    (setq $in-port (infile "herky-init.cmd"))
    (terpri) (princ "Excecuting `herky-init.cmd' ...") (terpri))
  (start-timer $total-time)
#+kcl (princ "Type (init) to start!")
#-kcl (init)
  )

(defun init (&optional gc)
  (setq $test-in-process nil)
  (setq $in-port piport)
  (initialize) 
  (if gc (gc 3))
  (herky))

(defmacro herky ()
  `(sloop while (catch 'reset (herky2)) do 
	  (setq $in-port piport)))

(defun herky2 ()
  ; This is the top level function that interacts with the user and
  ; dispatches the various commands.
  ; how about changing to user-menu ?? It's not easy.
  (prog (stime cmd)
    top-herky
    (start-timer stime)
    (terpri) 
    (dolist (xa '( 
"Type Add, Auto, Break, Cmd, Close, Delete, Gc, Grammar, Init, Kb, List,"
"     Makerule, Option, Operator, Prove, Quit, Read, Runbg, Stats, Test,"
"     Write or Help."))
      (princ xa) (terpri))
    (princ "HERKY-> ")

    (setq cmd (read-atom 'none))

    (when (eq $in-port piport) 
	  (if $test-in-process (return nil))
	  (if (not (member0 cmd *avoid-cmds*)) (open-new-log-port)))
    
    (setq cmd (choose-str cmd
		      '(add auto break cmd close delete help gc grammar
			    init kb list load makerule manager option 
			    operator prove quit read refute runbg
			    save stats test write)))

    (case cmd
      (add (setq $eqn-set (nconc $eqn-set (read-input t))))
      (auto (close-log-file)
	    (unless (setq $in-port (open-read-file "cmd"))
		    (setq $in-port piport)))
      (break (return (break-herky)))
      (cmd (setq $log-port (open-write-file "cmd" nil)))
      (close (close-log-file))
      (delete (delete-sys))
      (gc (gc 3))
      (grammar (help-file *help-grammar*))
      (help (help-file *help-herky*))
      (init (close-log-file) (initialize) 
	    (terpri) (princ "HERKY is initialized.") (terpri))
      (kb (setq $akb-flag nil) 
	  (if $hiper-loaded
	      (hiper-start)
	    (start-kb)))
      (list (display))
;      (load (load-herky))
      (makerule (setq $eqn-set (append $eqn-set $post-set) 
		      $post-set nil)
		(order-eqns))
;      (manager (x_prover))
;      (xin (x_prover))
      (option (run-kb-options))
      (operator (operator-options))
      (prove (prove))
      (quit (quit-herky) (return nil))
      (read (setq $eqn-set (nconc $eqn-set (read-input nil))))
;      (refute (refute-eqn))
      (runbg (run-herky))
;      (save (save-herky))
      (stats (display-stat))
      (test (test-herky))
      (write (writef-sys))
      (otherwise (princ "Sorry, that's an invalid command.") (terpri)))
    (format t "Time for this command = ~,3f sec      Total time = ~,3f sec~%" 
	    (time-in-sec (run-time stime)) 
	    (time-in-sec (run-time $total-time)))
    (go top-herky)))

(defun delete-sys ()
  ;  Lets the user delete an equation or a rule from the current set.
  ;  It has its own sub-toplevel for related options.
  (user-menu
    (equation "    Delete equation." (delete-eqn))
    (list "        List numbered equations and rules." (display)) 
    (rule "        Delete rule." (delete-rule))))

(defun delete-rule ()
  ; Deletes specified rule from the rule set.
  (if (io-eoln $in-port)
      (princ "Type a list of deleting rules' numbers : "))
  (let ((rule-nums (read-nums)) flag d-ops)
	(sloop for rule in $rule-set do
             (cond ((member (ruleno rule) rule-nums)
                    (clean-rule rule)
                    (setq flag t
			  d-ops (union d-ops (union (op-list (lhs rule))
					        (op-list (rhs rule)))))
                    (princ "Deleted rule: ")
		    (write-rule rule) (terpri))))
       (if flag (sys-flag-init))
       (clean-ops d-ops)
       flag))

(defun delete-eqn ()
  ;  Deletes specified equation from the equation set.
  (prog (flag l1 l2 l3 d-ops)
    delete-top
    (when (io-eoln $in-port)	; no argument pending?
	(princ "Type delete equation numbers (or L to list) : "))
      (setq l1 (read-nums))
      (if* (eq (car l1) 'l)
	  then (display nil)			; display equations only.
	       (go delete-top))
      (sloop with l4 = (length $eqn-set)
	    for n in l1 do
        (cond ((not (numberp n))
	       (princ n) 
	       (princ " is not a number.")
	       (terpri))
	      ((> n l4) (push n l3))
	      (t (push n l2))))
      (setq l1 nil)
      (if* l2 then
	  (sloop for x in $eqn-set	; find equation and extract
		for i from 1 do
	    (if* (member i l2)
		then
		(format t "Deleted equation #~d: " i)
	        (terpri) (princ "  ") (write-eqn x)
		(setq $eqn-set (removen x $eqn-set 1)
		      flag t
		      d-ops (union d-ops (union (op-list (lhs x))
					        (op-list (rhs x))))))))
      (if* l3 then
	  (sloop for x in $post-set	; find equation and extract
		for i from (add1 (length $eqn-set)) do
	    (if* (member i l3)
		then 
		(format t "Deleted equation #~d: " i)
	        (terpri) (princ "  ") (write-eqn x)
		(setq $post-set (removen x $post-set 1)
		      flag t
		      d-ops (union d-ops (union (op-list (lhs x))
					        (op-list (rhs x))))))))

      (if* (not flag)
	  then (princ "No equation can be deleted.") (terpri)
	  else (clean-ops d-ops))
      (return flag)))

(defun order-eqns (&optional dis &aux l2 rule)
  ;  Adds RULES to the rule set without computing critical pairs.
  (decide-which-kb)
  (if* (or $ac $commutative) then
     (setq $eqn-set (sloop for eq in $eqn-set collect (flatten-eqn eq)))
     (setq $post-set (sloop for eq in $post-set collect (flatten-eqn eq))))

  (sloop while $eqn-set do
     (setq l2 (pop $eqn-set)
           rule (catch 'kb-top
		  (catch 'refuted 
		    (catch 'reset (process-equation l2)))))
     (cond ((null rule) nil)	
	   ((member rule '(*newop* *kb-top*)) nil)
	   ((member rule '(*incons* *reset*))
	    (setq $eqn-set (cons l2 $eqn-set))
	    (reset))
	   ((member rule '(*refuted*))
	    (trace-rule $used-rule-nums)
	    (reset))
	   ((not (eq $kb '*distree*))
	    (trace-message 2 "Add Rule: " (write-rule rule))
	    (add-associate-list (op-of (lhs rule)) rule $op-rules)
	    (push-end rule $rule-set))))

  (terpri)
  (sys-flag-init)
  (when dis
	(display)
	(if $lrpo 
	    (princ "The system is terminating.")
	  (princ "The system is hopefully terminating.")) 
	(terpri)))
  
(defun close-log-file ()
  (when (and $log-port $log-flag)
	(terpri)
	(princ "Previous inputs are in file: ")
	(princ (truename $log-port)) (princ "."))
  
  (when $log-port
	(close $log-port) 
	(setq $log-port nil)
	(terpri)
	))

(defun close-out-file ()
  (when (not (eq $out-port poport))
	(terpri)
	(princ "Previous outputs are in file: ")
	(princ (truename $out-port)) (princ ".")
	(terpri)
	(close $out-port) 
	(setq $out-port poport)
	))

(defun quit-herky ()
   (unless (eq $in-port piport) (close $in-port))
   (close-log-file)
   (close-out-file)
   ;(princ (uconcat "Goodbye " (getenv 'USER) ".")) (terpri)
   (princ "Goodbye, my friend.") (terpri) 
   (terpri)
   (princ "Finish at: ") (date) (terpri)
   (quit))

(defun break-herky ()
  (princ "Break to LISP Listener.") (terpri)
  (princ "Using (init) to initialize HERKY. ") (terpri)
  (princ "Using (herky) to keep the current state of HERKY. ") (terpri)
  nil)

(defun test-herky ()
  (setq $trace-flag 1
	$automatic nil
	$order-condition nil
	$test-in-process t)
  (dolist (filename $test-examples)
	  (setq $in-port (infile (uconcat $example-directory 
					  filename ".cmd")))
	  (when $in-port
		(io-char-init)
		(initialize)
		(gc 3)
		(terpri)
		(princ "Execute the commands in file ")
		(princ (uconcat $example-directory filename ".cmd"))
		(terpri)
		(catch 'reset (herky2))
		(princ "Finish the commands in file ")
		(princ (uconcat $example-directory filename ".cmd"))
		(terpri)
		))
  (setq $in-port piport
	$test-in-process nil
	$trace-flag 3)
  )

(defun complete (name)
  ;; Hiper's orignal starting function.
 (when (not $hiper-loaded) 
       (lhiper) (chiper)
       (setq $hiper-loaded t))
 (histart name))

(defun load-hiper ()
  (when (not $hiper-loaded) 
	(lhiper) (chiper)
	(setq $hiper-loaded t))
  )

(defun run-herky ()
  (close-log-file)
  (terpri) 
  (princ "Please give a filename for the output and a filename for the commands .") (terpri)
  (unless (setq $out-port (open-write-file "out"))
	  (setq $out-port poport))
  (unless (setq $in-port (open-read-file "cmd"))
	  (setq $in-port piport))
  )

;;;;;; This file constains functions of initialization, reset, 
;;;;;; and statistics of herky.

(defmacro default-flag (flag default-value)
  `(cond ((assoc ,flag $defaults) (cdr (assoc ,flag $defaults)))
	 (t ,default-value)))

(defun pre-init ()
  ; Read in a list of default flag values from "init-herky-flag".
  (setq $defaults nil)
  (when (probef "init-herky.flag") 
      (setq $in-port (infile 'init-herky.flag))
      (while (not (io-eof $in-port))
	(push (cons (s2s (read-atom 'none))
		    (read-atom 'none))
	      $defaults))
      (close $in-port)
      (setq $in-port piport))

  (setq $distree (make-dtnode :id '*root* :num-of-rules 0 :num-of-child 0))
  )

(defun sys-flag-init ()
  (setq 
   $pure           nil          ; suppose it is not pure.
   $confluent      nil		; confluence flag.
   $old-nrules     $nrules      ; number of new rules.

   ;$sufficient     nil		; sufficient completeness flag.
   ;$cons-of-ts     nil          ; constructors of testset.
   ;$testset	nil
   ;$def-domains    nil
   )

  ;; Used in distree-kb. To be used in pure-kb.
  (init-var-bindings)
  (re-init-distree)
  )

(defun initialize ()
  ; Initialize the global variables.
  (clear-ops)		    

  (setq $out-port poport)
 
  (setq
    ;; Rule, Equation and Proposition Sets
    $kb            nil

    $eqn-set	   nil		; equation set
    $pair-set      nil          ; for ac-completion only
    $rules-to-pair nil          ; for ac-completion only
    $post-set	   nil		; postponed equations
    $post-ass-set  nil		; postponed propositions

    $rule-set	   nil		; rule set
    $subsume-rules nil		; rule set
    $aux-rules	   nil		; auxiliary rule set
    $op-rules	   nil		; a-list of form: ((op . (rules))...)

    $del-new-rules nil          ; newly deleted rules
    $del-rules     nil		; deleted rules
    $del-eqns	   nil		; eqns made from deleted rules
    $num-del-rules   0          ; number of deleted rules

    $new-variable    0          ; new variable.
    $new-sym-num     0
    )

  (setq 
    $theory-eqns   nil                 ; eqns built into systems
    $theory-rules  nil                 ; eqns built into systems
    $inverse-ops   nil                 ; inverse triples of operators
    $unit-ops      nil                 ; unit pairs of operators
    )

  (setq 
    ;; Operators with properties.
    $eqop-list  	nil		; equivalent operator list
    $precedence          nil		; precedence relations
    $l-st-list	        nil		; operators with lr-status assigned
    $r-st-list	        nil		; operators with rl-status assigned
    $f-weights          nil             ; operators with its weight
    $commutative	nil		; commutative operators
    $associative	nil		; associative operators
    $distributive       nil             ; distributive pairs of operators
    $ac                 nil             ; ac-operators
    $infix-ops          (list *=* *and* *xor* *or* *->* *equ*) ;; infix operators
    $divisible          nil		; divisible operators
    $constructors       nil             ; operators declared as constructors
    $type-constructors  nil             ; constructors paritioned by type
    $free-constructors  nil             ; 
    $skolem-ops         nil             ; 
    )

  (setq 
    ;; Global Counters or Indexes
    $block-cps          0		; number of unblocked equations.
    $prime-cps        nil		; number of down-composite equations.
    $left-cps         nil		; number of left-composite equations.
    $symbnum    	1		; new variable number
    $nrules		0		; number of rules generated 
    $nusereqn   	0		; number of user's equations.
    $ncritpr    	0		; number of critical pairs
    $symmetry-dels      0		; number of delete unifers by symmetry.
    )

  (setq
    ;; Time Statistics
    $add-time	        0		; time spent while adding rules
    $norm-time	        0		; time spent in normalization
    $ord-time	        0		; time spent in ordering
    $proc-time	        0		; total time by processor
    $brt-time   	0 		; time spent in brt.
    )

  (setq 
    ;; Proof methods
    $prove-eqn          nil             ; equation to be proved.
    $prove-eqns         nil             ; equation to be proved.
    $trace-proof        nil             ; trace the result of refutational proof.
    )

  (setq
    ;; Strategies
    $pick-rule-str	(default-flag 'pick-rule 'l) 
    $crit-with-str	(default-flag 'critical-with 'm)
    $del-rule-str	(default-flag 'delete-rule 2)
    $unmark-rule-str	(default-flag 'mark-rule 'l)
    $mark-rule-str	(default-flag 'mark-rule 'l)
    $rule-size	    (default-flag 'rule-size 'o)
    $ex1            (default-flag 'ext-rule-size1 1)
    $ex2            (default-flag 'ext-rule-size2 2)
    $immediate	    (default-flag 'post-max '6)
    $post-ass-list  (default-flag 'post-ass-list 'q)
    $more-break	    (default-flag 'more-break 'l)
    $norm-str	    (default-flag 'normalization 'o)
    $symmetry-check (default-flag 'symmetry t)
    $prime-acu      (default-flag 'prime-acu t)
    $prove-method   (default-flag 'prove-method  'h)
    $ordering       (default-flag 'ordering 'l)
    $lrpo           (default-flag 'lrpo t)	; lexico-recursive-path-order.

    $fopc                   nil		; true if a first order formula has
	                                ; been read in.
    $reduce-max            1000
    $discarded              nil
    $discard-eqn-max-degree  10  ;;  5
    $discard-eqn-max-depth    0
    $discard-eqn-max-size   100  ;; 30 
    $discard-eqn-2max-size  200  ;; 60
    $keep-deleted-rules     nil

    $support                nil
    $idem-superpose           t
    $one-superpose          nil
    $input-superpose        nil
    $unit-superpose         nil

    $reduce-system 	      3
    $array-in-use           nil
    )
    
  (setq
    ;; Auto-ordering Stuff.
    $newop-terms    nil		; used in autoorder.
    $auto-sugg      nil     	; variable used in "auto-orient".
    $newop-first (default-flag 'new-operator 1)
    $rl-first	(default-flag 'status 2) ; give the rl-status first.
    $pre-first 	(default-flag 'precedence 1) ; give equivalence first.
    $eq-arity	(default-flag 'equal-arity t)
    ;; the same arity operators can be eq.
    $post-posi	(default-flag 'postpone-position 2)
    ;; postpone suggestion flag.
    $post-max	(default-flag 'max-postpone 9999)
    ;; maximum of postponed equation.
    $runtime-max	(default-flag 'max-runtime 0)
    ;; maximum of postponed equation.
    $newrule-max	(default-flag 'max-new-rule 1000)
    ;; maximum of new generated rules
    )

  (setq
    $polynomial             nil
    $nilpotent-rules        nil
    $p-commut-rules         nil
    $poly-rules             nil
    $instant		nil
    $instant-seeds          nil
    $premises-set		nil
    $var-premises		nil
    $used-rule-nums         nil
    $poly-multi-1p-rules        nil
    )

#|
  (setq
    $condi          nil             ; boyer-moore rewriting flag.
    $build-rules    nil
    $induc-vars     nil             ; variables for induction proof.
    $cover-sets     nil             ; recursive definition cover sets.
    $non-comm-cover-sets    nil     ; recursive definition cover sets.
    $defin-depend   nil             ; definition dependency.
    $gene-num       0               ; definition dependency.
    $history	nil		; storage for undo operation
    $history1	nil		; auxilliary storage for undo operation
    )
|#    
    
  (de-init-poly)
  (sys-flag-init)
  (if $automatic (set-automatic-flags))
  )

(defun set-automatic-flags ()
  (setq	$reduce-system 2
	$discard-eqn-max-size 17 ;; p7:17, p5:13, p4:20, p2:17, p1:17
	$discard-eqn-2max-size 21 ;;
	$discard-poly-max-size 40 ; P7:30
;	$discard-eqn-max-depth  8 ;; 10 works well.
	$discard-eqn-max-degree 5
	$order-condition t
	))
