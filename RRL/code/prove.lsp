;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

(defun prove ()
  ; Determines if the specified equation is true (equal after normalizing). 
  ; Returns NIL.
  (prog (eqn new)
    (when (null $rule-set) 
      (princ "Note: the rewriting system is empty.") (terpri) 
      (if* (neq $prove-method 'f) (return nil)))

    ;; Is there an equation in the system?
    (if* (or $prove-eqn $guest-eqn) then
	(princ "Note: you have been proving the equation") (terpri)
        (princ "    ") 
	(write-eqn (or $prove-eqn $guest-eqn)) 
	(terpri)
        (if* (ok-to-continue) 
	    then 
	    (if* (null $induc) (start-kb) (induc-prove $guest-eqn))
	    (return nil)
	    else
	    (init-prove-globals)))

    ;; If there is no equation in the system, read in a new equation.
    (if* (null (setq eqn (read-this-eqn))) then (return nil))
    (setq eqn (first-process-eqn eqn))

    ;; Try normalization first.
    (setq $trace-proof t)
    (if* (and (null $induc) (ctx eqn)) (setq $induc 'c))
    (add-time $proc_time (setq new (cover-normal-proof eqn)))

    ;; Check if induciton works.
    (when new
      (cond ((eq $prove-method 'f)
	     (setq $guest-eqn eqn
		   $witness-eqn new
		   $del_rule_str 1)
	     (start-kb))
	    ((sloop for op in $newops 
		   if (and (not (is-bool-op op))
				(> (get-arity op) 0))
		   return op)
	     (terpri)
	     (princ "New operators are added, it can't be an inductive theorem.")
	     (terpri))
	    ((and $ckb_flag (null $induc))
	     (terpri)
	     (princ "Sorry, the inductionless induction is not supported ")
	     (terpri) (princ "     for conditional equation systems."))
	    ($induc
	     (start-push-history nil)
	     (setq $prove-eqn eqn
		   $guest-eqn new)
	     (induc-prove new))
	    (t (princ "Do you want to see if it is an inductive theorem ? ")
	       (if* (ok-to-continue "Proof by induction ? ") then
		   (start-push-history nil)
		   (setq $prove-eqn eqn)
		   (push new $eqn-set)
		   (induc-prove new)))))))

(defun uncondi-prove (eqn)
  (if* (null (setq eqn (checkeq-normal eqn))) then
      (princ "Yes, it is equational theorem.") (terpri) nil
     else 
     (when (> $trace_flag 1)
	   (if $confluent
	       (princ "No, it is not an equational theorem.") 
	     (princ "No, it is not known to be an equational theorem."))
	   (terpri) 
	   (princ "Normal form of the left hand side is:") (terpri)
	   (princ "   ") (write-term (lhs eqn))
	   (terpri) (terpri)				
	   (princ "Normal form of the right hand side is:") (terpri)
	   (princ "   ") (write-term (rhs eqn)) (terpri)
	   )
     (if $induc (setq $induc eqn))
     eqn))

(defun induc-prove (eqn)
   ; Prepare eveything for inductive proof, then run KB.
   (if* $induc 
       then (add-time $proc_time (cover-induc-prove eqn))
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
	  (if* (not (start-test)) then 
	     (princ "Note: Current conditional system is not sufficiently ")
 	     (princ "complete.") (terpri))
	  $constructors)
	(t (princ (uconcat "      Current Constructor Set  =  "
		               (display-ops $constructors))) (terpri)
 	   (if* (not (ok-to-continue 
		     "To prove the equation with the constructors ? "))
	     then $operlist
	     elseif (start-test) 
	     then $constructors
	     else (princ "Warning: The system is not sufficiently complete.") (terpri)
	          (if* (ok-to-continue "Use all operators as constructors ? ")
		      then $operlist
		      else $constructors)))))

#|
;; in xrrl.lsp.
(defun succ-end-induc ()
   (terpri)
   (princ "Following equation") (terpri)
   (princ "    ") (write-eqn $prove-eqn)
   (princ "    is an inductive theorem in the current system.") (terpri)
   (cond ($induc 
	  (when (not (eq (op-of (lhs $induc)) 'cond))
		(*catch 'refuted (*catch 'prove (*catch 'kb-top (*catch 'reset
			 (add-time $proc_time 
				   (order-one-norm-others
				    $induc ;;$prove-eqn
				    )))))))
	  (setq $prove-eqn nil
		$guest-eqn nil
		$succ-eqns nil)
	  )
	 ; >>>> 1/30/89
	 (t (terpri)
	    (if* (not (ok-to-continue
		      "Do you want to keep the theorem in the system ? "))
		then (if* $no-history
			 then (setq $prove-eqn nil)
			 else (sloop while $prove-eqn do (undo1)))
		(princ "The previous system is restored.") (terpri)
		else
		(setq $prove-eqn nil
		      $confluent t)))))
|#

(defun fail-end-induc (&optional eqns &aux done)
   (if* eqns then 
       (sloop for xa in eqns 
	     if (neq (car (eqn-source xa)) 'gene)
	       do 
	       (when (not done)
		     (terpri) (princ "Fail to prove the following equations:") (terpri)
		     (setq done t))
	       (princ "    ") (write-eqn xa))
       (terpri))
   
   (princ "Your equation") (terpri)
   (princ "    ") (write-eqn $prove-eqn)

   (if* $induc then
     (princ "    is not known to be an inductive theorem in the system.")
     (terpri)
     (if* $try then
       (terpri)
       (princ "******************************************************") (terpri)
       (princ "******   SORRY, SORRY, SORRY, SORRY, SO WHAT? ********") (terpri)
       (princ "******************************************************") (terpri)
       (break)
       else
       (setq $in-port
	     #-lucid nil
	     #+lucid t ; Workaround bug in Lucid 2.15.
	     )
       )
     elseif $ac 
     then
     (princ "    is not known to be an inductive theorem in the system.")
     (terpri)
     else (princ "    is not an inductive theorem in the system.") (terpri))

   (if* (null $induc) then
     (sloop while (or $prove-eqn (null (cdr $history))) do (undo1))
     (terpri) (princ "The previous system is restored.") (terpri)))

(defun separated (tt ss cc pp)
  ; "tt" is in form of f(t1, t2, ... tn) and "ss" is in form of
  ; f(s1, s2, ..., sn). This function throws the equations
  ; "t1 == s1", "t2 == s2", ... "tn == sn" to the higher levels.
  (sloop for xa in (args-of tt) as xb in (args-of ss) do
	(push (make-eqn xa xb cc pp) $eqn-set))
  (*throw 'kb-top '*sepa*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; refute.lsp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun refuted-result (source &aux rule)
  ; We call this function when we discover that an equation is
  ; unsatisfiable.
  (setq rule (make-new-rule '(true) '(false) nil source))
  (terpri) (princ "Derived: ") (write-rule rule)
  (if* $narrow 
    then (nconc $goal-set (nconc rule))
    else (nconc $rule-set (ncons rule)))
  ;; use $used-rule-nums to store this special rule.
  (setq $used-rule-nums rule) 
  (*throw 'refuted '*incons*))

(defun refute-eqn (&aux l1 eqn)
  (if* (is-empty-line $in-port) then
      (princ "Input a list of equations of which the last one is the ")
      (princ "conclusion.") (terpri))
  (setq l1 (read-input (eq 'k (ask-choice 
			       l1 '(k f)
			       "From the keyboard or a file ? "))))
  
  (when l1 
    (setq eqn (car (last l1))
	  $eqn-set (append $eqn-set (delete0 eqn l1))
	  $guest-eqn eqn
	  eqn (negate-eqn eqn t)
	  $del_rule_str 1
	  $trace-proof t)

    (if* $instant then
	(setq l1 (skolemize (lhs eqn))
	      $instant-seeds (get-instance-seeds l1)
	      eqn (change-lhs eqn l1))
	else (setq $instant-seeds nil))

    (push eqn $eqn-set)))

(defun negate-eqn (eqn &optional trace &aux l1)
  ; negate the equation "eqn" into an assertion. 
  ; adding all default univerally quantified variables.
  (setq l1 (if* (is-assertion eqn)
	       then (lhs eqn) 
	       else (eqn2ass eqn)))
  (sloop for xa in (free-vars l1) do (setq l1 (list 'all xa l1)))
  (setq l1 (append (list (list 'not l1) nil) (cddr eqn)))
  (setf (is-input-ass l1) t)
  (if* trace then
      (terpri)
      (princ "Negating ") 
      (write-eqn eqn)
      (princ "    into ")
      (write-eqn l1))
  l1)

(defun get-instance-seeds (term &aux l1 l2 l3 ops)
  ; Get a list of groups of non-variable terms such that
  ; each group have the same size and all terms are constructed from
  ; the functions of "term".
  (sloop for op in (op-list term) do
	(if* (is-constant op) 
	    (push (list op) l1) 
	  (if* (not (or (predicatep op) (is-bool-op op))) (push op ops))))
  (setq l2 (sloop for op in ops nconc
		 (caseq (get-arity op)
			(1 (sloop for xa in l1 collect (list op xa)))
			(2 (sloop for xa in (cross-product l1 l1)
				 collect (make-term op xa)))
			(t nil))))
  (setq l3 (sloop for op in ops nconc
		 (caseq (get-arity op)
			(1 (sloop for xa in l2 collect (list op xa)))
			(2 (nconc
			    (sloop for xa in (cross-product l1 l2)
				  collect (make-term op xa))
			    (sloop for xa in (cross-product l2 l1)
				  collect (make-term op xa))))
			(t nil))))
  (sloop for xa in (list l1 l2 l3) collect (cons (length xa) xa)))

(defun get-instance-terms (n) (ref-instance-seeds n $instant-seeds))

(defun ref-instance-seeds (n seeds)
  ; return a list of (num s1 s2 ... snum).
  (if* (null seeds) then nil
      elseif (< n (caar seeds)) then (element-combination n (cdar seeds))
      elseif (= n (caar seeds)) then (ncons (cdar seeds))
      else (sloop with first = (cdar seeds)
		 for rest in (ref-instance-seeds (- n (caar seeds)) (cdr seeds))
		 collect (append first rest))))

(defun element-combination (n list)
  (if* list then
      (if* (= n 1) then (mapcar 'ncons list)
	  else (nconc (element-combination n (cdr list))
		      (sloop with first = (car list)
			    for xa in (element-combination (sub1 n) (cdr list))
			    collect (cons first xa))))))

(defun get-instance-terms2 (n &aux terms)
  ; n is a number. Return some n-tuples of terms.
  (setq terms (ref-instance-seeds2 n))
  (if* (< n (car terms))
      (sloop with firstn = (first-n-elements (cdr terms) (sub1 n))
	    for xa in (rest-elements (cdr terms) (sub1 n))
	    collect (cons xa firstn))
      (ncons (cdr terms))))

(defun ref-instance-seeds2 (n)
  (sloop for xa in $instant-seeds 
	if (<= n (car xa)) return xa
	finally
	  (return (let* ((l1 (car (last $instant-seeds)))
			 (l2 (ref-instance-seeds2 (- n (car l1)))))
		    (cons (+ (car l1) (car l2)) 
			  (append (cdr l1) (cdr l2)))))))

(defun collect-cdr-with-same-car (list)
  ; Collect the elements with the same car into groups. Assume list is not empty.
  (sloop with res = (ncons (cdr (pop list)))
	with value = (caar list)
	for xa in list
	if (equal value (car xa))
	  do (nconc res (ncons (cdr xa)))
	     (setq list (cdr list))
	else return (cons res (collect-cdr-with-same-car list))
	finally (return (ncons res))))

(defun all-nonvars (term)
  (if* (variablep term) then nil
      elseif (is-skolem-op (op-of term)) then (ncons term)
      elseif (null (args-of term)) 
      then (if* (not (memq (op-of term) '(0 true false))) (ncons term))
      elseif (not (memq (op-of term) $bool-ops))
      then (cons term (mapcan 'all-nonvars (args-of term)))
      else (mapcan 'all-nonvars (args-of term))))

;; ======================================================================

(defun refute-rule-instances (vars terms rule)
  ; return the instances of rule by substituting "vars" by "terms" in rule.
  ; the number of the instances is the same as that of "vars" or "terms".
  (sloop for n from 1 to (length terms) 
	collect (prog1 (applysubst-rule 
			 (sloop for va in vars
			       for te in terms collect (cons va te))
			 rule)
		       (setq vars (append1 (cdr vars) (car vars))))))

;(defun orient-goal (eqn t1 t2)
;  ; Return a goal rule made from "eqn". 
;  ; Return nil if failed to make so.
;  (if* (lrpo t1 t2) then (make-goal-rule t1 t2 (eqn-source eqn) (ruleno eqn))
;      elseif (lrpo t2 t1) 
;      then (make-goal-rule t2 t1 (eqn-source eqn) (ruleno eqn))
;      else
;      (terpri) (princ "Trying to orient goal: ") (terpri)
;      (princ "  ") (write-goal-eqn eqn)
;      (caseq (ask-user eqn t1 t2 nil)
;	(1 (make-goal-rule t1 t2 (eqn-source eqn)))
;	(2 (make-goal-rule t2 t1 (eqn-source eqn)))
;	(p nil)
;	(i (*throw 'reset '*reset*))
;	(m nil)
;	(t (break "Lost in orient-goal")))))

(defun is-skolem-op (op)
  ; Return t iff "op" is a skolem function.
  (memq op (allsym 's))
)

(defun skolem-terms (term)
  ; return a list of subterms of "term" which are rooted by a skolem function.
  (if* (variablep term) then nil
      elseif (is-skolem-op (op-of term)) then (ncons term)
      else (mapcan 'skolem-terms (args-of term))))

(defun init-prove-globals ()
  (setq $failed-eqns nil
	$succ-eqns nil
	$case-split-terms nil
	$induc-eqns nil
	$first-induc-op nil
	$prove-eqn nil 
	$witness-eqn nil
	$guest-eqn nil))

(defun init-cover-prove ()
  (setq $failed-eqns nil
	$succ-eqns nil
	$case-split-terms nil
	$induc-eqns nil
	$first-induc-op nil))

