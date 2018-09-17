;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)
(declare (special $type-testset))

(defun start-test ()
  ; Determines if the specification in $rule-set are sufficiently
  ; complete relative to constructors. Returns NIL.
  (prog (temp)
    (if $sufficient then 
	(princ "Your system is already sufficiently complete.") (terpri) 
	(return t))

    (cond ((null $rule-set)
	   (princ "Note: Rule set is empty, run Kb please.") (terpri) 
	   (return nil))
	  ((constructors-check $operlist)
	   (princ "No construcotrs for that type. Stop.") (terpri)
	   (return nil))
          ((null (get-noncons))
	   (princ "Note: All operators are constructors.")
	   (terpri) (return t)))

    (if (not $confluent) then
	(terpri) (princ "Note: the system may be not canonical.") (terpri))

    (setq temp (set-timer) 
	  $reduce_time 0
	  $def-domains (get-defining-domains))
    (complete-test) 
    (terpri)
    (format t "Processor time used      =  ~f sec" 
             (setq $proc_time (get-time temp))) (terpri)
    (return $sufficient)))

(defun complete-test (&aux (flag t) type-base)
  ; Test the sufficient completeness for each operator non-constructors.
  ; If one of them is not complete, return NIL. Otherwise return T.
  (get-testset $constructors)
  (setq type-base (if (eq $prove-method 'q) 
                      then (get-basic-type-terms $constructors)
		      else $type-testset))
  (loop for op in (get-noncons)
	if (assoc op $def-domains)
  	  do (if (test-one-op op type-base) (setq flag nil))
	else if (null (get-arity2 op)) do (setq flag nil))
  (setq $sufficient flag))

(defun test-one-op (op type-base)
  ; Returns nil iff "op" is sufficiently complete relative to constructors.
  (let ((def-domain (get-def-domain op)) stones)
    (if (null (cdr def-domain)) 
     then (princ (uconcat "No definition for the operator '" op "'."))
	  (terpri)
	  (setq stones t)
     else (setq stones (get-schemes op type-base))
          (if (or $ac (eq $prove-method 'q)) then (setq stones (quasi-remover stones)))
	  (cond
	    (stones 
	     (terpri)
             (princ (uconcat "Specification of '" op "' is not "))
	     (if (or $ac $commutative) then (princ "known to be "))
	     (princ "completely defined.")
             (terpri)
             (if (null $ac) then
		 (princ "Following left hand sides of rules are proposed: ") 
		 (terpri)
		 (loop for t1 in stones do 
		   (princ "    ") (write-term t1) (princ " ---> something") (terpri))))
	    (t (terpri)
	       (princ (uconcat "Specification of '" op 
			       "' is completely defined.")) 
	       (terpri)))
	  stones)))
	
(defun c-test-one-op (op &aux stones)
  ; Returns T iff "op" is sufficiently complete relative to 
  ; constructors, where "op" is defined by conditional equations.
  (if (not (is-bool-op op)) then
    (if (null (cdr (get-def-domain op))) then
        (terpri)
        (princ (uconcat "No definition for the operator '" op "'."))
        (terpri)
	(setq stones t)
     else
        (setq stones (c-get-schemes op $type-testset))
        (cond
	 (stones
          (terpri)
          (princ (uconcat "Specification of '" op
		     "' is not completely defined."))
          (terpri)
          (princ "Following left sides of rules (with their condition) are")
          (princ " proposed :" ) (terpri)
          (loop for t1 in stones do
               (princ "    ")
	       (write-term (t-cterm t1)) (princ " ---> ")
	       (write-rhs 'something (c-cterm t1)) (terpri)))
         (t (princ (uconcat "Specification of '" op
		     "' is completely defined"))
            (terpri)))
        stones)))

(defun constructors-check (ops &aux flag)
  ; Called before doing sufficent completeness checking.
  ; Each operator in "ops" must be well-typed, otherwise, that operator
  ; will not be considered by the system.
  ; Each type must have constructors, otherwise, the checking cannot be done.
  (loop for op in ops 
	as type = (get-domain-type op)
	if (eq type 'univ)
	do (terpri) (princ (uconcat "Warning: '" op "' is untyped.")) 
	   (terpri)
	   (if (not (ok-to-continue)) then 
	       (princ "Use [op : type1, type2, ... -> type] to declare types")
	       (terpri) (princ "under the 'add' command.") (terpri)
	       (reset)
	       else
	       (princ (uconcat "The definition of '" op "' will not be considered."))
	       (terpri))
	else if (and (not (is-bool-op op))
		     (null (assoc type $type-constructors)))
	do (princ (uconcat "Note: Constructors for Type '"
			   type "' is empty.")) (terpri)
           (if (ext-operator 'constructors) then (setq flag t))
	   (if (null (assoc type $type-constructors)) then (return t))
	finally (if flag then (return nil) 
		         else
			 (display-constructors $type-constructors) 
			 (terpri)
			 (return nil))))
