;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "RRL")



(defun give-stat (&optional port)
   (terpri port)
   (display-kb-stat nil port)
   (terpri port)
   (if $constructors 
     then (princ (uconcat "Constructors : " (display-ops $constructors)) port) 
     else (princ "No constructors." port))			
   (terpri port)    (terpri port) 
   (princ "Termination Ordering : " port)
   (if (eq $ordering 'm) 
     then (princ "Manual" port) (terpri port) 
     elseif (eq $ordering 's)
     then (princ "Size + Lexicographic Ordering." port)
     else (if $lrpo
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
	 (port2 (if port then port else t)))
#+franz     (cprintf  "CPU Time used                        = %.2f sec" x1 port) 
#-franz (format port2 "Time used                            = ~6,2f sec" (nrm-time x1))
      (terpri port)
      (princ (uconcat "Number of rules generated            = " $nrules) port)
      (terpri port)
      (princ (uconcat "Number of rules retained             = " 
                      (length $rule-set)) port)
      (terpri port)
      (princ (uconcat "Number of critical pairs             = " $ncritpr) port) 
      (terpri port)
      (if (eq $blocking-on 'y) then
       (princ (uconcat "Number of unblocked critical pairs   = " $unblocked) port)
       (terpri port))
#+franz  
   (if (greaterp x1 0.009) then
       (cprintf "Time spent in normalization          = %.2f sec" $norm_time port)
       (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $norm_time x1)) port) (terpri port)
       (cprintf "Time spent in unification            = %.2f sec" $unif_time port)
       (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $unif_time x1)) port) (terpri port)
       (cprintf "Time spent in ordering               = %.2f sec" $ord_time port)
       (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $ord_time x1)) port) (terpri port)
       (cprintf "Time spent in simplifying the rules  = %.2f sec" $add_time port)
       (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $add_time x1)) port) (terpri port)
       ;(princ "  (keeping rule set reduced)" port) (terpri port)
       (if (greaterp $brt_time 0.009) then
        (cprintf "Time spent in boolean translation    = %.2f sec" $brt_time port)
        (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $brt_time x1)) port) (terpri port))
       (if (eq $blocking-on 'y) then
	(cprintf "Time spent in blocking               = %.2f sec" $block_time port)
        (cprintf "     (%.2f percent of time)"
			(times 100 (quotient $block_time x1)) port) (terpri port))
    )
#-franz
   (if (greaterp x1 0.009) then
       (format port2 "Time spent in normalization          = ~6,2f sec " (nrm-time $norm_time))
       (format port2 " (~f percent of time)"
			(truncate (* 100 $norm_time) x1)) (terpri port)
       (format port2 "Time spent in unification            = ~6,2f sec "
	                      (nrm-time $unif_time))
       (format port2 "  (~f percent of time)"
			(truncate (* 100 $unif_time) x1)) (terpri port)
       (format port2 "Time spent in ordering               = ~6,2f sec "
	                    (nrm-time $ord_time))
       (format port2 "  (~f percent of time)"
			(truncate (* 100 $ord_time) x1)) (terpri port)
       (format port2 "Time spent in simplifying the rules  = ~6,2f sec "
	       (nrm-time $add_time))
       (format port2 "  (~f percent of time)"
			(truncate (* 100 $add_time) x1)) (terpri port)
       ;(princ "  (keeping rule set reduced)" port) (terpri port)
       (if (greaterp $brt_time 0.009) then
        (format port2 "Time spent in boolean translation    = ~6,2f sec "
		(nrm-time $brt_time))
        (format port2 "  (~f percent of time)"
			(truncate (* 100 $brt_time) x1)) (terpri port))
       (if (eq $blocking-on 'y) then
	(format port2 "Time spent in blocking               = ~6,2f sec "
		(nrm-time $block_time))
        (format port2 "  (~f percent of time)"
		       (truncate (* 100 $block_time) x1)) (terpri port))
    )
    (if total then
#+franz (cprintf  "Total time (including 'undo' action) = %.2f sec" total)
#-franz (format port2 "Total time (including 'undo' action) = ~f sec" total)
     (terpri port) (terpri port))))

(defun display-op-stats (&optional port)
  ; Displays to the user the current equivalence, precedence and
  ; status relation among operators in the system.  Returns NIL.
  (terpri port)
  (if $eqop_list
      then (princ "Equivalence relation among operators now is:" port) (terpri port)
	   (loop for xa in $eqop_list do 
	      (princ (uconcat "Equivalent set: " (display-ops xa)) port) (terpri port))
      else (princ "There are no equivalent operators." port) (terpri port))
  (terpri port)
  (if $glob_prec
      then (princ "Precedence relation now is: " port) (terpri port) 
	   (loop for xa in $glob_prec do
		 (princ (uconcat "   " (car xa) " > ") port)
		 (loop for xb in (cdr xa) do (princ (uconcat xb " ") port))
		 (terpri port))
      else (princ "There is no ordering yet in the precedence relation." port)
	   (terpri port))
  (terpri port)
  (if $st_list
      then (princ "Operators with status are:" port) (terpri port)
	   (loop for op in $st_list do
		 (princ (uconcat "   " op) port)
		 (if (eq (get op 'status) 'lr)
		     then (princ " with left-to-right status." port)
		     else (princ " with right-to-left status." port))
		 (terpri port))
      else (princ "There are no operators with status." port) (terpri port))
  (if $ac then (terpri port)
    (princ (uconcat "Associative & commutative operator set = "
		    (display-ops $ac)) port) (terpri port))
  (if $commutative then (terpri port)
    (princ (uconcat "Commutative operator set = " (display-ops $commutative)) port)
    (terpri port))
  (if $translist then (terpri port)
    (princ (uconcat "Transitive operator set = " (display-ops $translist)) port)
    (terpri port))
  (display-type-arity $operlist port))

(defun display-ops (ops)
  (if ops then
   (prog (res)
     (setq res (uconcat "{ " (pop ops)))
     (loop for op in ops do (setq res (uconcat res ", " op)))
     (return (uconcat res " }")))
   else "{ }"))     
