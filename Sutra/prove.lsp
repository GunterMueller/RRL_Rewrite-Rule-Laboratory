;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "RRL")

(defun prove ()
  ; Determines if the specified equation is true (equal after normalizing). 
  ; Returns NIL.
  (prog (eqn new)
    (when (null $rule-set) 
      (princ "Note: the rewriting system is empty.") (terpri) 
      (if (neq $prove-method 'f) (return nil)))
    (if (or $prove-eqn $witness-eqn) then
	(princ "Note: you have been proving the equation") (terpri)
        (princ "    ") 
	(write-eqn (if $prove-eqn $prove-eqn $guest-eqn)) 
	(terpri)
        (if (ok-to-continue) 
	    then 
	    (if (null $induc) (start-kb))
	    (induc-prove) (return nil)
	    else
	    (setq $prove-eqn nil $witness-eqn nil)))
    (if (null (setq eqn (read-this-eqn))) then (return nil))
    (add-time $proc_time
              (setq new (first-process-eqn eqn)
                    new (if $induc
			    (newinduc-eq-prove new) 
			  (uncondi-prove new))))
    (when new
      (cond ((eq $prove-method 'f)
	     (setq $guest-eqn eqn
		   $witness-eqn eqn
		   $del_rule_str 1)
	     (start-kb))
	    ($newops 
	     (terpri) (princ "New operators are added, it")
	     (princ " can't be an inductive theorem.") (terpri))
	    ((and $ckb_flag (null $induc))
	     (terpri)
	     (princ "Sorry, the inductionless induction method is not supported ")
	     (terpri) (princ "     for conditional equation systems."))
	    ($induc
	     (start-push-history nil)
	     (setq $prove-eqn eqn)
	     (induc-prove))
	    (t (princ "Do you want to see if it is an inductive theorem ? ")
	       (if (ok-to-continue "Proof by induction ? ") then
		   (start-push-history nil)
		   (setq $prove-eqn eqn)
		   (push new $eqn-set)
		   (induc-prove)))))))

(defun uncondi-prove (eqn)
  (if (null (setq eqn (checkeq-normal eqn))) then
      (princ "Yes, it is equational theorem.") (terpri) nil
     else (if $confluent
	      then (princ "No, it is not an equational theorem.") 
	      else (princ "No, it is not known to be an equational theorem."))
     (terpri) 
     (princ "Normal form of the left hand side is:") (terpri)
     (princ "   ") (write-term (lhs eqn))
     (terpri) (terpri)				
     (princ "Normal form of the right hand side is:") (terpri)
     (princ "   ") (write-term (rhs eqn)) (terpri)
     (if $induc then (setq $induc eqn))
     eqn))

(defun induc-prove ()
   ; Prepare eveything for inductive proof, then run KB.
   (if $induc 
       then (add-time $proc_time (cover-induc-prove $induc)) 
       else
   (prog (result (temp (choose-constructors)))
      (setq
            $confluent nil
	    $constructors temp
            $def-domains (get-defining-domains)
	    temp #+franz (set-timer) #-franz 0)
      (add-time $proc_time (get-testset $constructors))
      (terpri) (princ "Proving equation") (terpri)
      (princ "  ") (write-eqn $prove-eqn) 
      (setq result (*catch 'prove (run-kb)))
      (terpri)
      (cond
	((eq result '*incons*) (fail-end-induc))
	((eq result '*reset*) (reset))
        ($prove-eqn (succ-end-induc)))
      (terpri)
      #+franz (cprintf  "Processor time used         = %.2f sec" (get-time temp)) 
;; #-franz (format t "Processor time used         = ~f sec" (get-time temp)) 
      (terpri))))

(defun choose-constructors ()
  ; Ask the user to use which method or to prove equation with
  ; or without constructors.
  (cond ($sufficient $constructors)
	($ckb_flag
	  (if (not (start-test)) then 
	     (princ "Note: Current conditional system is not sufficiently ")
 	     (princ "complete.") (terpri))
	  $constructors)
	(t (princ (uconcat "      Current Constructor Set  =  "
		               (display-ops $constructors))) (terpri)
 	   (if (not (ok-to-continue 
		     "To prove the equation with the constructors ? "))
	     then $operlist
	     elseif (start-test) 
	     then $constructors
	     else (princ "Warning: The system is not sufficiently complete.") (terpri)
	          (if (ok-to-continue "Use all operators as constructors ? ")
		      then $operlist
		      else $constructors)))))

(defun succ-end-induc (&aux l1)
   (terpri)
   (princ "Following equation") (terpri)
   (princ "    ") (write-eqn $prove-eqn)
   (princ "    is an inductive theorem in the current system.") (terpri)
   (cond ($induc 
	  (setq $prove-eqn nil
		$succ-eqns nil)
	  (add-time $proc_time (order-one-norm-others $induc)))
	 ; >>>> 1/30/89
	 (t (terpri)
	    (if (not (ok-to-continue
		      "Do you want to keep the theorem in the system ? "))
		then (if $no-history
			 then (setq $prove-eqn nil)
			 else (loop while $prove-eqn do (undo1)))
		(princ "The previous system is restored.") (terpri)
		else
		(setq $prove-eqn nil
		      $confluent t)))))

(defun fail-end-induc (&optional eqns)
   (if eqns then 
       (terpri) (princ "Fail to prove the following equations:") (terpri)
       (loop for xa in eqns 
	     if (neq (car (eqn-source xa)) 'gene)
	       do (princ "    ") (write-eqn xa))
       (terpri))
   (princ "Your equation") (terpri)
   (princ "    ") (write-eqn $prove-eqn)
   (if $induc then
       (princ "    is not known to be an inductive theorem in the system.")
       (terpri)
       (if $try then
	   (terpri)
	   (princ "**********************************************************") (terpri)
	   (princ "**********   SORRY, SORRY, SORRY, SORRY, SO WHAT? ********") (terpri)
	   (princ "**********************************************************") (terpri)
	   (break)
	   else
	   (setq $in-port
		 #-lucid nil
		 #+lucid t ; Workaround bug in Lucid 2.15.
	   )
       )
       elseif $ac 
       then (princ "    is not known to be an inductive theorem in the system.") (terpri)
       else (princ "    is not an inductive theorem in the system.") (terpri))
   (if (null $induc) then
       (loop while (or $prove-eqn (null (cdr $history))) do (undo1))
       (terpri) (princ "The previous system is restored.") (terpri)))

(defun separated (tt ss cc pp)
  ; "tt" is in form of f(t1, t2, ... tn) and "ss" is in form of
  ; f(s1, s2, ..., sn). This function throws the equations
  ; "t1 == s1", "t2 == s2", ... "tn == sn" to the higher levels.
  (loop for xa in (args-of tt) as xb in (args-of ss) do
	(push (make-eqn xa xb cc pp) $eqn-set))
  (*throw 'kb-top '*sepa*))
