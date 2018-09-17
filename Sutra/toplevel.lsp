;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "RRL")
#-franz (export '(start-up))
#-franz (export '(rrl))


(defun start-up ()
  ;  Top-most-level function.  Starts up the RRL system.
  (terpri)
  (loop for xa in '(
"****************************************************************************"
"****                                                                    ****"
"****          Welcome To  SUTRA   (Version 1.0)                         ****"
;; REWRITE RULE LABORATORY (RRL 2.1)              ****"
"****                                                                    ****"
;"****     (c) Copyright 1985,1986 G.Sivakumar.  All rights reserved.     ****"
;"****     (c) Copyright 1985,1986 Hantao Zhang.  All rights reserved.    ****"
;"***(c) Copyright 1985,1986 General Electric Company. All rights reserved.***"
"****************************************************************************"
) do (princ xa) (terpri))
  ; The following are equates and some variables that have to be set before
  ; calling INITIALIZE.
;#+franz  (sstatus uctolc t)	; convert uppercase to lowercase.
; >>>>>> 1/28/89 no need to change everything in lowcase. HZ 12/88
#+franz (setsyntax '|,| 'vsingle-character-symbol)
  (pre-init)
  (initialize)
  (if (my-probef 'init-rrl.cmd) then 
     (setq $in-port (car (errset (infile "init-rrl.cmd") nil)))
     (terpri) (princ "Excecuting 'init-rrl.cmd' ...") (terpri))
#+franz  (setq $total-time (set-timer))
#+franz  (loop while (*catch 'reset (rrl)) do (setq $in-port nil))

;; common lisp doesn't yet know that top-level is (rrl).
;; so we do this explicitly here & call (exit) for leaving with q.
;;   -- siva 2/9/90
#-franz  (loop  do (setq $in-port nil) (*catch 'reset (rrl)))

)

(defun rrl ()
  ; This is the top level function that interacts with the user and
  ; dispatches the various commands.
  ; how about changing to user-selectq ?? It's not easy.
  (prog (*readtable* #+franz stime)
    top-rrl
#+franz    (setq stime (set-timer))
#-franz (setq *readtable* *rrl-readtable*)
    (show-message  '( 
""
"Type Add, Akb, Auto, Break, Clean, Delete, Grammar, History, Init, Kb, List,"
"     Load, Log, Makerule, Modal, Narrow, Norm, Option, Operator, Prove, Quit, "
"     Read, Refute, Save, Solve, Stats, Suffice, Undo, Unlog, Write or Help."))
    (princ "RRL-> ")
    (selectq					
      (choose-str (read-atom 'none)
		  '(add akb auto break clean delete help grammar history init
		    kb list load log makerule modal narrow norm option 
		    operator test prove quit read refute save solve stats
		    suffice undo unlog write))
      (add (setq $eqn-set (nconc $eqn-set (read-input t))))
      (akb (if (equal $post-max 9999) (setq $post-max 4))
	   (if (equal $newrule-max 1000) (setq $newrule-max 50))
	   (auto-kb))
      (auto (setq $in-port (open-read-file "cmd")))
      (clean (clean-history))
      (history (setq $history1 nil) (start-push-history nil nil t))
      (delete (delete-sys))
      (break (let (#-franz (*readtable* *starting-cl-readtable*))
	       (break "to LISP. Type (rrl) to resume.")))
      (help    (help-file $helpfile))
      (grammar (help-file $grammar))
      (init (initialize) (terpri) (princ "RRL is initialized.") (terpri))
      (kb (if $narrow then
	      (setq $narrow (ok-to-continue "Continue previous linear completion ? ")))
	  (setq $akb_flag nil)
	  (start-kb))
      (list (display))
      (load (load-rrl))
      (log (setq $log-port (open-write-file "cmd" nil)))
      (makerule (setq $eqn-set (append $eqn-set $post-set) 
		      $post-set nil)
		(order-eqns))
      (modal (modal-proof))
      (narrow (linear))
      (norm (normalize))
      (option (run-kb-options))
      (operator (operator-options))
;;      (protocol (top-level-protocol))
      (prove (prove))
      (quit (quit-rrl))
      (read (setq $eqn-set (nconc $eqn-set (read-input nil))))
      (refute (refute-eqn))
      (save (save-rrl))
      (solve (top-level-solve))
      (stats (give-stat))
      (suffice (start-test))
      (test (test-rrl))
      (undo (setq $akb_flag nil) (*catch 'kb-top (undo t))); (display)
      (unlog (close-log))
      (write (writef-sys))
      (otherwise ;(drain-it $in-port)
	 (princ "Sorry, I cannot do that.") (terpri)
	 (if $test then (quit-rrl))))
#+franz (cprintf  "Time (this command) = %.3f sec" (get-time stime)) 
; #-franz (format t "Time = ~f sec" (get-time stime)) 
#+franz (cprintf "      Total = %.3f sec" (get-time $total-time))
; #-franz (format t "      Total = ~f sec" (get-time $total-time)) 
    (terpri)
    (go top-rrl)))

(defun resume-rrl() (rrl))

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
  (if (is-empty-line $in-port)
	then (princ "Type a list of deleting rules' numbers : "))
  (let ((rule-nums (read-args $in-port)) flag d-ops)
	(loop for rule in $rule-set do
             (cond ((member (ruleno rule) rule-nums)
                    (clean-rule rule)
                    (setq flag t
			  d-ops (union d-ops (union (op-list (lhs rule))
					        (op-list (rhs rule)))))
                    (princ "Deleted rule: ")
		    (write-rule rule) (terpri))))
       (if flag then (sys-flag-init))
       (clean-ops d-ops)
       flag))

(defun delete-eqn ()
  ;  Deletes specified equation from the equation set.
  (prog (flag l1 l2 l3 d-ops)
    delete-top
    (if (is-empty-line $in-port)	; no argument pending?
	then (princ "Type delete equation numbers (or L to list) : "))
      (setq l1 (read-args $in-port))
      (if (eq (car l1) 'l)
	  then (display nil)			; display equations only.
	       (go delete-top))
      (loop with l4 = (length $eqn-set)
	    for n in l1 do
        (cond ((not (numberp n))
	       (princ (uconcat n " is not a number.")) (terpri))
	      ((> n l4) (push n l3))
	      (t (push n l2))))
      (setq l1 nil)
      (if l2 then
	  (loop for x in $eqn-set	; find equation and extract
		for i from 1 do
	    (if (member i l2)
		then (princ (uconcat "Deleted equation #" i ": "))
	        (terpri) (princ "  ") (write-eqn x)
		(setq $eqn-set (remove x $eqn-set 1)
		      flag t
		      d-ops (union d-ops (union (op-list (lhs x))
					        (op-list (rhs x))))))))
      (if l3 then
	  (loop for x in $post-set	; find equation and extract
		for i from (1+ (length $eqn-set)) do
	    (if (member i l3)
		then (princ (uconcat "Deleted equation #" i ": "))
	        (terpri) (princ "  ") (write-eqn x)
		(setq $post-set (remove x $post-set)
		      flag t
		      d-ops (union d-ops (union (op-list (lhs x))
					        (op-list (rhs x))))))))

      (if (not flag)
	  then (princ "No equation can be deleted.") (terpri)
	  else (clean-ops d-ops))
      (return flag)))

; This function is too expensive.
;(defun delete-ops (ops)
;   (loop for op in ops if (not (exist-op op)) do
;	(setq $operlist (remove $operlist op)
;	      $constructors (remove $constructors op))))

(defun order-eqns (&optional dis &aux l2 rule)
  ;  Adds RULES to the rule set without computing critical pairs.
  (setq $newrule-num 1 $small-depth 3)
  (if (or $ac $commutative) then
     (setq $eqn-set (loop for eq in $eqn-set collect (flatten-eqn eq)))
     (setq $post-set (loop for eq in $post-set collect (flatten-eqn eq))))
  (loop while $eqn-set do
     (setq l2 (pop $eqn-set)
           rule (*catch 'kb-top
		  (*catch 'refuted 
		    (*catch 'reset (process-equation l2)))))
     (cond ((null rule) nil)	
	   ((member rule '(*newop* *undo* *kb-top*)) nil)
	   ((member rule '(*incons* *reset*))
	    (setq $eqn-set (cons l2 $eqn-set))
	    (reset))
	   (t (if (> $trace_flag 1) then 
		   (terpri) (princ " Adding Rule: ") (write-rule rule))
	      (add-associate-list (op-of (lhs rule)) rule $op_rules)
	      (setq $rule-set (nconc $rule-set (ncons rule))))))
 (sys-flag-init)
 (if dis then (display)
     (if $lrpo then (princ "The system is terminating.")
	 else (princ "The system is hopefully terminating.")) (terpri)))
  
(defun close-log ()
  (if $log-port then
    (princ (uconcat "Log file '" (truename $log-port) "' is closed."))
    (close $log-port) (setq $log-port nil)
   else (princ "No log file.")) (terpri))

(defun quit-rrl ()
   (if $in-port then (close $in-port))
   (if $log-port then
	(princ (uconcat "Log file '" (truename $log-port) "' is closed."))
	(close $log-port))
   (terpri)
   (princ (uconcat "Goodbye " (getenv 'USER) ".")) (terpri)
   (terpri)
#+franz (exit)
#-franz (bye)
)

(defun test-rrl (&aux l1)
   (push $in-port $save-in-port)
   (setq $test t
	 $trace_flag 1
	 $in-port (open-read-file "cmd"))
   (if $in-port then
	(setq l1 (uconcat (truename $in-port) 'cp)
	      $log-port (car (errset (outfile l1 'b) nil)))
        (princ (uconcat "    '" l1 "' is open to write.")) (terpri)))

(defun top-level-solve()
  (let ((eqn (read-this-eqn 'solve)))
    (if eqn
	(progn
	  (format t "~% ~% Solving ")
	  (write-eqn eqn)
	  (solve (lhs eqn) (rhs eqn))))))


  
