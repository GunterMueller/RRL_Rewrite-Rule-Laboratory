(in-package "USER")

(defun prove ()
  ; Determines if the specified equation is true (equal after normalizing). 
  ; Returns NIL.
  (prog (eqn new (old-trace-proof $trace-proof))
    (when (null $rule-set) 
      (princ "Note: the rewriting system is empty.") (terpri) 
      (if (neq $prove-method 'f) (return nil)))
    (if* $prove-eqn then
	(princ "Note: you have been proving the equation") (terpri)
        (princ "    ") 
	(write-eqn $prove-eqn)
	(terpri)
        (if* (ok-to-continue) 
	    then 
	    (if* (null $condi) (start-kb))
;	    (induc-prove)
	    (return nil)
	    else
	    (setq $prove-eqn nil)))
    (if* (null (setq eqn (read-this-eqn))) then (return nil))
    (setq new (make-eqn (lhs eqn) (rhs eqn) (ctx eqn) (eqn-source eqn)))

    (when (and $newops (eq $kb '*distree*))
	  (terpri) (princ "You might have input unnecessary new operators.")
	  (terpri) 
	  (if (ok-to-continue)
	      (re-init-distree)
	  (return nil)))

    (setq $trace-proof t)
    (add-time $proc-time
              (setq new ; (if $condi (newinduc-eq-prove new))
		    (uncondi-prove new)))
    (setq $trace-proof old-trace-proof)

    (when new
      (cond ((eq $prove-method 'f)
	     (if (> $del-rule-str 1) (setq $del-rule-str 1))
	     (push new $prove-eqns)
	     (start-kb))
;	    ($condi
;	     (setq $prove-eqn new)
;	     (induc-prove))
	    ($newops 
	     (terpri) (princ "New operators are added, it")
	     (princ " can't be an inductive theorem.") (terpri))
	    (t
;	     (princ "Do you want to see if it is an inductive theorem ? ")
;	     (if* (ok-to-continue "Proof by induction ? ") then
;		   (setq $prove-eqn eqn)
;		   (push new $eqn-set)
;		   (induc-prove))
	     nil
	     )))))

(defun uncondi-prove (eqn1 &aux eqn)
  (if* (null (setq eqn (check-norm-eqn eqn1))) then
      (princ "Yes, it is an equational theorem.") (terpri) 
      (update-used-rules eqn1)
      (setf (rhs eqn1) (norm-term (rhs eqn1)))
      (setf (lhs eqn1) (rhs eqn1))
      (setq eqn1 (make-dummy-rule eqn1))
      (trace-rule eqn1 poport t)
      nil
     else 
     (if $confluent
	 (princ "No, it is not an equational theorem.") 
       (princ "No, it is not known to be an equational theorem."))
     (terpri) 
     (update-used-rules eqn)
     (princ "The normalized equation is the last one in the following sequence:") (terpri)
     (setq eqn1 (make-dummy-rule eqn))
     (trace-rule eqn1 poport t)
     (if $condi (setq $prove-eqn eqn))
     eqn))

(defun check-witness (rule &aux eqns new old-used-nums)
  ; trace to reduce $prove-eqn using rule;
  ; if $prove-eqn is normalized to nil, then report the success.
  (dolist (eqn $prove-eqns)
	  (setf $used-rule-nums nil
		old-used-nums (eqn-used-rules eqn)
		(eqn-used-rules eqn) nil)

	  (when (setq new (reduce-by-one-rule (lhs eqn) rule))
		(setf (lhs eqn) new)
		(setq new (check-norm-eqn eqn))

		(when (null new)
		      (setf (eqn-used-rules eqn) (append old-used-nums (nreverse $used-rule-nums-old)))
		      (setf (lhs eqn) (rhs eqn))
		      (found-witness eqn))
		(trace-reduced-witness eqn)
		(setf (eqn-used-rules new) (append old-used-nums (eqn-used-rules new)))
		)

          (if (null new) (setf new eqn 
			       (eqn-used-rules new) old-used-nums))

	  (push new eqns))

  (setq $prove-eqns eqns))

(defun trace-reduced-witness (eqn &aux rule-nums)
  (trace-message 2 "Goal " 
		 (format $out-port "[~s, ~s] is reduced by"
			 (car (eqn-source eqn)) (cadr (eqn-source eqn)))
		 (setq rule-nums (reverse (eqn-used-rules eqn)))
		 (format $out-port " [~s]," (car rule-nums))
		 (when (cdr rule-nums) 
		       (princ " followed by" $out-port)
		       (dolist (xa (cdr rule-nums)) (format $out-port " [~s]," xa)))
		 (setf (eqn-used-rules eqn) rule-nums)
		 (princ " to" $out-port) (terpri $out-port)
		 (princ "    " $out-port) (write-eqn eqn)))

(defun flatten-witness (ruleno &aux eqns)
  (dolist (eqn $prove-eqns)
	  (setq eqn (flatten-eqn eqn))
	  (when (equal (lhs eqn) (rhs eqn))
		(setq $used-rule-nums (ncons ruleno))
		(update-used-rules eqn)
		(found-witness eqn))
	  (push eqn eqns))
  (setq $prove-eqns eqns))

(defun found-witness (eqn)
  (setq eqn (make-new-rule eqn 5 nil 1000))
  (setq $used-rule-nums eqn)
  (throw 'refuted '*witness*))

(defun fail-end-induc (&optional eqns)
   (if* eqns then 
       (terpri) (princ "Fail to prove the following equations:") (terpri)
       (sloop for xa in eqns 
	     if (neq (car (eqn-source xa)) 'gene)
	       do (princ "    ") (write-eqn xa))
       (terpri))
   (princ "Your equation") (terpri)
   (princ "    ") (write-eqn $prove-eqn)
   (if* $condi then
       (princ "    is not known to be an inductive theorem in the system.")
       (terpri)
       (if* $try then
	   (terpri)
	   (princ "**********************************************************") (terpri)
	   (princ "**********   SORRY, SORRY, SORRY, SORRY, SO WHAT? ********") (terpri)
	   (princ "**********************************************************") (terpri)
	   (break)
	   else
	   (setq $in-port nil))
       elseif $ac 
       then (princ "    is not known to be an inductive theorem in the system.") (terpri)
       else (princ "    is not an inductive theorem in the system.") (terpri))
   )

(defun refuted-result (source &aux rule)
  ; We call this function when we discover that an equation is
  ; unsatisfiable.
  (setq rule (make-eqn *trueterm* *falseterm* nil source))
  (setq rule (make-new-rule rule 5 nil 100000))
  (update-used-rules rule)
  (terpri) (princ "Derived: ") (write-rule rule)
  (push-end rule $rule-set)
  ;; use $used-rule-nums to store this special rule.
  (setq $used-rule-nums rule) 
  (throw 'refuted '*refuted*))

(defun refute-eqn (&aux l1 eqn)
  (if* (io-eoln $in-port) then
      (princ "Input a list of equations of which the last one is the ")
      (princ "conclusion.") (terpri))
  (setq l1 (ask-choice l1 '(k f q)
		       "From the keyboard or a file, or quit ? "))
  
  (when (and (neq l1 'q) (setq l1 (read-input (eq 'k l1))))
    (setq eqn (car (last l1))
	  $eqn-set (nconc $eqn-set (delete eqn l1))
	  eqn (negate-eqn eqn t)
	  $del-rule-str 1
	  $trace-proof t
	  $keep-deleted-rules t)

    (if (and $instant (not $check-homogenous))
	(setq l1 (skolemize (lhs eqn))
	      $instant-seeds (get-instance-seeds l1)
	      eqn (change-lhs eqn l1))
	(setq $instant-seeds nil))

    (push eqn $eqn-set)))

(defun negate-eqn (eqn &optional trace &aux l1 l2)
  ; negate the equation "eqn" into an assertion. 
  ; adding all default univerally quantified variables.
  (setq l1 (if (is-assertion eqn) (lhs eqn) (eqn2ass eqn))
	l2 l1)
  (sloop for xa in (free-vars l1) do (setq l1 (list *all* xa l1)))
  (if (equal l1 l2) 
      (setq l2 *falseterm*)
      (setq $fopc t 
	    l1 (list *not* l1)
	    l2 nil))

  (if* trace then (terpri) (princ "Negating ") (write-eqn eqn))
  (change-lhs-rhs eqn l1 l2)
  (set-input-ass eqn)
  (when trace (princ "    into ") (write-eqn eqn))
  eqn)

(defun get-instance-seeds (term &aux l1 l2 l3)
  ; Get a list of groups of non-variable terms such that
  ; each group have the same size and all terms are constructed from
  ; the functions of "term".
  (setq l1 (sloop for op in (op-list term) 
		  if (and (not (eq op *0*)) (is-constant-op op))
		  collect (ncons op)))

  (setq l2 (sloop for xa in (cross-product l1 l1)
		  collect (make-term $*$ xa)))

  (setq l3 (nconc
	     (sloop for xa in (cross-product l1 l2)
		    collect (make-term $*$ xa))
	     (sloop for xa in (cross-product l2 l1)
		    collect (make-term $*$ xa))))

  (list (cons (length l1) l1)
	(cons (length l2) l2)
	(cons (length l3) l3)))

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
      (if* (eq n 1) then (mapcar 'list list)
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
	if (eq value (car xa))
	  do (nconc res (ncons (cdr xa)))
	     (setq list (cdr list))
	else return (cons res (collect-cdr-with-same-car list))
	finally (return (ncons res))))

(defun all-nonvars (term)
  (if* (variablep term) then nil
      elseif (is-skolem-op (op-of term)) then (ncons term)
      elseif (null (args-of term)) 
      then (if (not (or (eq (op-of term) 0)
			(memq (op-of term) *true*false*)))
	       (ncons term))
      elseif (not (is-bool-op (op-of term)))
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
		       (setq vars (append1 (cdr vars) (car vars) t)))))

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
;	(i (throw 'reset '*reset*))
;	(m nil)
;	(t (break "Lost in orient-goal")))))

(defun skolem-terms (term)
  ; return a list of subterms of "term" which are rooted by a skolem function.
  (if* (variablep term) then nil
      elseif (is-skolem-op (op-of term)) then (ncons term)
      else (mapcan 'skolem-terms (args-of term))))


