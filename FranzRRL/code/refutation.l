;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.
#-lispm (include datamacs.l)

(setq $goal-size 40				
      $instance-subst-size 5)

(defun refuted-result (source &aux rule)
  ; We call this function when we discover that an equation is
  ; unsatisfiable.
  (setq rule (make-new-rule '(true) '(false) nil source))
  (terpri) (princ "Derived: ") (write-rule rule)
  (if $narrow 
    then (nconc $goal-set (nconc rule))
    else (nconc $rule-set (ncons rule)))
  ;; use $used-rule-nums to store this special rule.
  (setq $used-rule-nums rule) 
  (*throw 'refuted '*refuted*))

(defun refute-eqn (&aux l1 eqn)
  (if (is-empty-line $in-port) then
      (princ "Input a list of equations of which the last one is the ")
      (princ "conclusion.") (terpri))
  (setq l1 (read-input (eq 'k (ask-choice 
			       l1 '(k f)
			       "From the keyboard or a file ? "))))
  
  (when l1 
    (setq eqn (car (last l1))
	  $eqn-set (append $eqn-set (delq eqn l1))
	  $guest-eqn eqn
	  eqn (negate-eqn eqn t)
	  $del_rule_str 1
	  $trace-proof t)

    (if $instant then
	(setq l1 (skolemize (lhs eqn))
	      $instant-seeds (get-instance-seeds l1)
	      eqn (change-lhs eqn l1))
	else (setq $instant-seeds nil))

    (push eqn $eqn-set)))

(defun negate-eqn (eqn &optional trace &aux l1)
  ; negate the equation "eqn" into an assertion. 
  ; adding all default univerally quantified variables.
  (setq l1 (if (is-assertion eqn)
	       then (lhs eqn) 
	       else (eqn2ass eqn)))
  (loop for xa in (free-vars l1) do (setq l1 (list 'all xa l1)))
  (setq l1 (append (list (list 'not l1) nil) (cddr eqn)))
  (setf (is-input-ass l1) t)
  (if trace then
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
  (loop for op in (op-list term) do
	(if (is-constant op) 
	    (push (list op) l1) 
	  (if (not (or (predicatep op) (is-bool-op op))) (push op ops))))
  (setq l2 (loop for op in ops nconc
		 (caseq (get-arity op)
			(1 (loop for xa in l1 collect (list op xa)))
			(2 (loop for xa in (cross-product l1 l1)
				 collect (make-term op xa)))
			(t nil))))
  (setq l3 (loop for op in ops nconc
		 (caseq (get-arity op)
			(1 (loop for xa in l2 collect (list op xa)))
			(2 (nconc
			    (loop for xa in (cross-product l1 l2)
				  collect (make-term op xa))
			    (loop for xa in (cross-product l2 l1)
				  collect (make-term op xa))))
			(t nil))))
  (loop for xa in (list l1 l2 l3) collect (cons (length xa) xa)))

(defun get-instance-terms (n) (ref-instance-seeds n $instant-seeds))

(defun ref-instance-seeds (n seeds)
  ; return a list of (num s1 s2 ... snum).
  (if (null seeds) then nil
      elseif (< n (caar seeds)) then (element-combination n (cdar seeds))
      elseif (= n (caar seeds)) then (ncons (cdar seeds))
      else (loop with first = (cdar seeds)
		 for rest in (ref-instance-seeds (- n (caar seeds)) (cdr seeds))
		 collect (append first rest))))

(defun element-combination (n list)
  (if list then
      (if (eq n 1) then (mapcar 'ncons list)
	  else (nconc (element-combination n (cdr list))
		      (loop with first = (car list)
			    for xa in (element-combination (sub1 n) (cdr list))
			    collect (cons first xa))))))

(defun get-instance-terms2 (n &aux terms)
  ; n is a number. Return some n-tuples of terms.
  (setq terms (ref-instance-seeds2 n))
  (if (< n (car terms))
      (loop with firstn = (first-n-elements (cdr terms) (sub1 n))
	    for xa in (rest-elements (cdr terms) (sub1 n))
	    collect (cons xa firstn))
      (ncons (cdr terms))))

(defun ref-instance-seeds2 (n)
  (loop for xa in $instant-seeds 
	if (<= n (car xa)) return xa
	finally
	  (return (let* ((l1 (car (last $instant-seeds)))
			 (l2 (ref-instance-seeds2 (- n (car l1)))))
		    (cons (+ (car l1) (car l2)) 
			  (append (cdr l1) (cdr l2)))))))

(defun collect-cdr-with-same-car (list)
  ; Collect the elements with the same car into groups. Assume list is not empty.
  (loop with res = (ncons (cdr (pop list)))
	with value = (caar list)
	for xa in list
	if (eq value (car xa))
	  do (nconc res (ncons (cdr xa)))
	     (setq list (cdr list))
	else return (cons res (collect-cdr-with-same-car list))
	finally (return (ncons res))))

(defun all-nonvars (term)
  (if (variablep term) then nil
      elseif (is-skolem-op (op-of term)) then (ncons term)
      elseif (null (args-of term)) 
      then (if (not (memq (op-of term) '(0 true false))) (ncons term))
      elseif (not (memq (op-of term) $bool-ops))
      then (cons term (mapcan 'all-nonvars (args-of term)))
      else (mapcan 'all-nonvars (args-of term))))

;; ======================================================================

(defun refute-rule-instances (vars terms rule)
  ; return the instances of rule by substituting "vars" by "terms" in rule.
  ; the number of the instances is the same as that of "vars" or "terms".
  (loop for n from 1 to (length terms) 
	collect (prog1 (applysubst-rule 
			 (loop for va in vars
			       for te in terms collect (cons va te))
			 rule)
		       (setq vars (append1 (cdr vars) (car vars))))))

;(defun orient-goal (eqn t1 t2)
;  ; Return a goal rule made from "eqn". 
;  ; Return nil if failed to make so.
;  (if (lrpo t1 t2) then (make-goal-rule t1 t2 (eqn-source eqn) (ruleno eqn))
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
#-lispm (memq op (allsym 's))
#+lispm (and (memq (getcharn op 1) '(83 115)) ;; #/s = 115, #/S = 83.
             (numeral (getcharn op 2)))
)

(defun skolem-terms (term)
  ; return a list of subterms of "term" which are rooted by a skolem function.
  (if (variablep term) then nil
      elseif (is-skolem-op (op-of term)) then (ncons term)
      else (mapcan 'skolem-terms (args-of term))))


