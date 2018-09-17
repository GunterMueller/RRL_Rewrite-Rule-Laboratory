;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

(in-package "USER")

(defun is-inconsi-pair (t1 t2)
   (or (and (variablep t1) (or (variablep t2) (null (args-of t2))))
       (and (variablep t2) (null (args-of t1)))))

(defun consistent-check (eqn)
  ; Check if "eqn" is a consistent equation using Huet and Hullot's 
  ; criteria. If not, prints an error message and throws "*incons*" to 
  ; the catch in "induc-prove".
  (let ((t1 (lhs eqn)) (t2 (rhs eqn)))
    (cond ((variablep t1) 
	   (cond ((variablep t2) (inconsistent-eqn eqn))
		 ((member t1 (var1-list t2)) t)
		 (t (inconsistent-eqn eqn))))
	  ((variablep t2)
	   (if* (not (member t2 (var1-list t1))) (inconsistent-eqn eqn)))
	  ((truep t1) (if* (falsep t2) then (inconsistent-eqn eqn)))
	  ((falsep t1) (if* (truep t2) then (inconsistent-eqn eqn)))
	  ((and (member (op-of t1) $free-constructors))
	   (if* (eq (op-of t1) (op-of t2)) 
	       then (separated t1 t2 (ctx eqn) (eqn-source eqn))
	       else (inconsistent-eqn eqn)))
	  (t t))))

(defun consistent-rule (rule)
  ; Check if "rule" is a consistent equation. If not, prints an error 
  ; message and throws "*incons*" to the catch in "induc-prove".
  (if* (and (not (and (eq (car (rule-source rule)) 'deleted)
		     (memq 'ac-op (rule-source rule))))
	   (is-primitive (lhs rule))
	   (caseq $prove-method 
	     (q (not (quasi-reducible (lhs rule))))
	     (s (rule-destroyable (lhs rule)))))
    then
    (terpri) 
    (if* $ac then (princ "A possiblely "))
    (princ "Inconsistent Relation derived:") (terpri)
    (princ "   ") (write-rule rule)
    (if* (eq $trace_flag 'q) then
	(princ "    because the left side is not ground-reducible.") (terpri))
    (setq $used-rule-nums rule)
    (*throw 'prove '*incons*)))

(defun consistent-pair (t1 t2 &optional var)
  ; Return t if "eqn" is a consistent equation.
  (if (variablep t2) (psetq t1 t2 t2 t1))
  (cond ((equal t1 t2) t)
	((variablep t1) 
	 (if* var 
	      then (or (variablep t2)
		       (not (is-free-constructor (op-of t2)))
		       (not (is-primitive t2))
		       (not (is-subterm t1 t2)))
	      elseif (variablep t2) then nil
	      elseif (memq (op-of t2) $free-constructors) 
	      then nil
	      else (is-subterm t1 t2)))
	((truep t2) (not (falsep t1)))
	((is-free-constructor (op-of t1))
	 (if* (eq (op-of t1) (op-of t2)) then
	      (setq t1 (sloop for xa in (args-of t1) 
			      for xb in (args-of t2) 
			      if (not (consistent-pair xa xb var))
			      return nil 
			      else if (nequal xa xb) 
			      collect (list xa xb)))
	       (if (cdr t1) (cons 'and t1) (car t1))
	       else
	       (not (is-free-constructor (op-of t2)))))
	  (t t)))

(defun consistent-check-testset (eqn)
  ; Check if "eqn" is a consistent equation. If not, prints an error message
  ; and throws "*incons*" to the catch in "induc-prove".
  (let ((t1 (lhs eqn)) (t2 (rhs eqn)))
    (cond ((variablep t1) 
	   (cond ((variablep t2) (inconsistent-eqn eqn))
		 ((member t1 (var1-list t2))
		  (if* (destroyable t2 $testset) 
		      then (inconsistent-eqn eqn)))
		 (t (inconsistent-eqn eqn))))
	  ((variablep t2)
	   (if* (member t2 (var1-list t1))
	       then (if* (destroyable t1 $testset)
			then (inconsistent-eqn eqn))
	       else (inconsistent-eqn eqn)))
	  ((and (member (op-of t1) $free-constructors)
		(eq (op-of t1) (op-of t2)))
	   (separated t1 t2 (ctx eqn) (eqn-source eqn)))
	  (t (setq t1 (destroyable t1 $testset))
	     (if* (and t1 (not (applies t2 t1))) then
		 (if* (destroyable t2 $testset)
		     then (inconsistent-eqn eqn)))))))

(defun consistent-check-quasi (eqn)
  ; Check if "eqn" is a consistent equation. If not, prints an error 
  ; message and throws "*incons*" to the catch in "induc-prove".
  (let ((t1 (lhs eqn)) (t2 (rhs eqn)))
    (cond ((variablep t1) 
	   (cond ((variablep t2) (inconsistent-eqn eqn))
		 ((member t1 (var1-list t2))
		  (if* (and (is-limited t2 $constructors)
			   (not (quasi-reducible t2)))
		      then (inconsistent-eqn eqn)))
		 (t (inconsistent-eqn eqn))))
	  ((variablep t2)
	   (if* (member t2 (var1-list t1))
	       then (if* (and (is-limited t1 $constructors)
			     (not (quasi-reducible t1)))
			then (inconsistent-eqn eqn))
	       else (inconsistent-eqn eqn)))
	  ((truep t1) (if* (falsep t2) then (inconsistent-eqn eqn)))
	  ((falsep t1) (if* (truep t2) then (inconsistent-eqn eqn)))
	  ((and (member (op-of t1) $free-constructors)
		(eq (op-of t1) (op-of t2)))
	   (separated t1 t2 (ctx eqn) (eqn-source eqn)))
	  ((and (is-limited t1 $constructors)
		(is-limited t2 $constructors))
	   (if* (lrpo t1 t2)
	       then (if* (not (quasi-reducible t1)) (inconsistent-eqn eqn))
	       elseif (not (quasi-equivalent t1 t2))
	       then (inconsistent-eqn eqn))))))

(defun inconsistent-eqn (eqn &aux rule)
  ; Auxillary function to "consistent-check".
  (setq rule (make-new-rule (lhs eqn) (rhs eqn) (ctx eqn) (eqn-source eqn)))
  (terpri)
  (if* $ac then (princ "A Possiblely "))
  (princ "Inconsistent Relation Derived:") (terpri)
  (princ "    ") (write-rule rule)
  (nconc $rule-set (ncons rule))
  (setq $used-rule-nums rule)
  (*throw 'refuted '*incons*))

(defun trace-inconsistency (rule &optional port)
  (let (rule-nums unused)
    ; rule is inconsistent. Trace the sources of this rule.
    (setq rule-nums (get-all-rule-nums (rule-nums-from-source (rule-source rule)))
	  rule-nums (delete0 (ruleno rule) rule-nums 1)
	  rule-nums (append1 rule-nums (ruleno rule)))

    (if* (null port) then (terpri))
    (sloop for num in rule-nums 
	  if (setq num (pick-out-rule num)) 
	    do (write-detail-rule num port))
    
    (sloop for rules in (list $del-rules $rule-set) do
	  (sloop for ru in rules
		if (eq (first (rule-source ru)) 'user)
		do (if* (not (memq (ruleno ru) rule-nums)) (push ru unused))))

    (if* unused then 
	(terpri port) 
	(if* (cdr unused)
	    (princ (uconcat "There are " (length unused) " rules") port)
	    (princ "Only one rule is" port))
	(princ " made from the input, but not used in the proof:" port) 
	(terpri port)
	(sloop for ru in (reverse unused) do (write-rule ru port)))

    (terpri port)
    (princ (uconcat "The proof length (including the input) is " 
		    (length rule-nums) ".") port)
    (terpri port)

    (if* port then (terpri port) (display-kb-stat nil port))))
	   
(defun get-all-rule-nums (nums &aux result)
  ; Return all rule numbers which has some relation with the rules in "nums".
  (sloop while nums for num = (pop nums) 
	if (and (numberp num) (not (memq num result)))
	do (push num result)
	   (setq nums (nconc nums
			     (rule-nums-from-source
			       (rule-source (pick-out-rule num))))))
  (sort result '<))

(defun rule-nums-from-source (source)
  ; "source" contains the info about the source of a rule and the rules
  ; which has reduced that rule. 
  ; Return a list of rule nums which is in "source".
  (if* source then
      (nconc (caseq (first source)
	       (user nil)
	       ((deleted divided idem) (ncons (second source)))
	       (t (list (first source) (second source))))
	     (sloop for xa in (cddr source) if (numberp xa) collect xa))))

(defun pick-out-rule (num)
  ; Return a rule of which the number is "num".
  (or (sloop for rule in $rule-set if (= (ruleno rule) num) return rule)
      (sloop for rule in $del-rules if (= (ruleno rule) num) return rule)
      (if* (= num (ruleno $used-rule-nums)) then $used-rule-nums)))
