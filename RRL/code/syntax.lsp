;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")



;;-----------------------------------
;; Functions on Syntax Error Checking
;;-----------------------------------

(defun input-check (eqn)
  ; Check that predicates and functions were used in the right places and 
  ; that functions were called with the same number of arguments 
  ; everywhere.  If an error happens, we throw. If no error happens, we 
  ; return eqn.
  (if* (*catch 'error
	(progn
	(if* (is-condi-eqn eqn) then (expecting-predicates (ctx eqn)))
	(cond ((is-assertion eqn) (expecting-predicates (lhs eqn)))
	      ((is-prop-eqn eqn)
	       (expecting-predicates (lhs eqn))
	       (expecting-predicates (rhs eqn))
	       (if* (is-condi-eqn eqn) (expecting-predicates (ctx eqn))))
	      (t (expecting-functions (lhs eqn))
		 (expecting-functions (rhs eqn))))))
      then (write-eqn eqn) (terpri) (synerr)
      else eqn))

(defun expecting-functions (term)
  ; Check the top level of term is a function symbol, and that it has the 
  ; right arity, and that all of its arguments satisfy the same criterion.
  (if* (nonvarp term) then
      (check-arity term)
      (enter-op (op-of term))
      (if* (memq (op-of term) '(= eq))
	  then (if* (not (type-cohere (get-term-type (first-arg term))
			             (get-term-type (second-arg term))))
	            (bad-typed term)
		 ;; >>>>>>>>> 1/7/89
		 (sloop for xa in (args-of term) do (expecting-functions xa)))
	  elseif (is-bool-op (op-of term)) 
	  then (sloop for xa in (args-of term) do (expecting-predicates xa))
	  else (sloop for ty in (get-codomain-types (op-of term)) 
		     for ar in (args-of term) 
		     if (nonvarp ar) 
		       do
			 (if* (type-cohere ty (get-domain-type (op-of ar)))
			     then (if* (eq ty 'bool) 
				      then (expecting-predicates ar)
				      else (expecting-functions ar))
			     else (bad-typed term))))))

(defun expecting-predicates (term) 
  ; Check the top level of term is a boolean expression, and that it has 
  ; the right arity, and that all of its arguments satisfy the same criterion.
  (if* (variablep term) 
      then (princ (uconcat "Warning!  " term 
			   ": variable used as predicate.")) (terpri)
           ;(synerr)
           (if* (not $induc) (synerr))
      else
      (ensure-predicate (op-of term))
      (check-arity term)
      (if* (memq (op-of term) '(= eq))
	  then (if* (not (type-cohere (get-term-type (first-arg term))
				     (get-term-type (second-arg term))))
		   (bad-typed term)
		 ;; >>>>>>>>> 1/7/89
		 (sloop for xa in (args-of term) do (expecting-functions xa)))
	  elseif (memq (op-of term) '(and or xor not -> equ)) 
	  then (sloop for xa in (args-of term) do (expecting-predicates xa))
	  elseif (memq (op-of term) '(all exist)) 
	  then (expecting-predicates (second-arg term))
	  else (sloop for ty in (get-codomain-types (op-of term)) 
		     for ar in (args-of term) 
		       do
			 (if* (and (nonvarp ar) 
				  (type-cohere ty (get-domain-type (op-of ar))))
			     then (if* (eq ty 'bool) 
				      then (expecting-predicates ar)
				      else (expecting-functions ar))
			     elseif (nonvarp ar) 
			     then (bad-typed term))))))

(defun bad-typed (term)
  (write-term term)
  (princ ": bad-typed term in the equation:")
  (terpri) 
  (synerr))

(defun input-type-check (term name)
  (if* (well-typed term) then t else
      (princ (uconcat "The " name " of the equation is not well-typed: "))
      (terpri) nil))

(defun ensure-predicate (pred)
  ; Ensure that the given operator is a predicate.
  (if* (enter-op pred) 
      then (if* (and (neq pred 'cond) (not (predicatep pred))) then
	      (terpri)
	      (princ (uconcat "!!!!!!!!! Warning: '" pred 
			      "' has been considered as a predicate."))
	      ;; >>>>>>> 1/14/89
	      (terpri)
	      (set-predicate pred))
      else (set-predicate pred)))		

(defun enter-op (op)
  ; Enter a virgin operator on the operator list, if it isn't already 
  ; there. Return t if it was already there.
  (if* (memq op $operlist) then t
      else
      (if (and (not (is-bool-op op)) (not (member op $fri-ops))) (push op $newops))
      (push-end op $operlist) nil))

(defun fixup-quantified-formula (quantifier vars formula)
  ; Given a list of variables, a quantifier, and a formula, return our 
  ; internal representation for that formula quantified with all of the 
  ; variables.  Our internal representation limits us to one variable 
  ; per quantifier, so we will usually produce several quantifiers.
  (if* (null vars) then formula
      elseif (not (memq (car vars) (free-vars formula))) then formula
      else  (make-term quantifier
		  (list (car vars) 
		      (fixup-quantified-formula quantifier
						 (cdr vars) formula)))))

(defun check-arity (func-expr)
  ; In a function or predicate expression, ensure that we have the right 
  ; number of arguments.
  (if* (get-arity (op-of func-expr)) then
      (if* (nequal (get-arity (op-of func-expr))
		  (length (args-of func-expr))) then
	  (princ "The function ")
	  (princ (op-of func-expr))
	  (princ " should have ")
	  (princ (get-arity (op-of func-expr)))
	  (princ " arguments but you gave it ")
	  (princ (length (args-of func-expr))) (princ ":")
	  (terpri)
	  (synerr))
      else (set-arity (op-of func-expr)	(length (args-of func-expr))))
  func-expr)

(defun expected (buffer expectedlist &optional flag)
  ; Tell the user that he made a boo boo.
  (terpri)
  (if* flag then (princ "Expected one of the following: ")
      else
      (princ "Found '") (princ (token-text buffer))
      (princ "' but expected one of the following: "))

  (sloop for xa in (cdr expectedlist) do (princ xa) (princ ", "))
  (princ (car expectedlist)) (terpri)
  (if* (null (token-port buffer)) 
	then (drain-it (token-port buffer))
	elseif (nequal (token-eoln buffer) 'eof)
        then (terpri) (princ "Following text has not been parsed.") (terpri)
	     (princ "  ... ... ")
	     (let ((num 0) (port (token-port buffer)))
#+franz	       (do char (readc port) (readc port)	
		  (or (= (my-tyipeek port) -1) (> num 100))
  		  (princ char)
		  (setq num (1+ num)))
	       (if* (> num 100) then (princ " ... ...") (terpri))
	       (terpri)
	       (close port)))       
  (synerr))

(defun is-valid-op (op)
  ; Returns T iff OP is a valid operator; otherwise, NIL.
  ; A valid operator is a symbol that is not a variable and is
  ; not one of the following: , ; ( ) == ---> if.
  (not (or (null op) (is-valid-var op) (memq op $separators) (listp op))))

#-franz
(defun is-infix-op (op) (and (is-valid-op op) (= 2 (get-arity op))))

(defun set-up-arity2 (op arity buffer)
  ; check whther "op" has the consistent "arity" as before.
  (if* (get-arity2 op) then
    (if* (nequal (get-arity2 op) arity)
	then (expect-arity op arity buffer))
    elseif (get-arity op) 
    then (if* (= (length (cdr arity)) (get-arity op))
		then (set-arity2 op arity)
		else (expect-arity12 op arity buffer))
    else (set-arity op (length (cdr arity)))
	 (set-arity2 op arity)
 	 (enter-op op)
	 (if* (eq 'bool (car arity)) then (set-predicate op))))

(defun expect-arity12 (op arity buffer &aux old-arity)
  ; Tell the user that he made an error.
  ; The arity of op is not consistent with the old one.
  (princ (uconcat "The operator has the arity of length " (get-arity op) "."))
  (terpri)
  (setq old-arity (get-arity2 op))
  (set-arity2 op arity)
  (princ "         but now:")
  (display-one-arity2 op)
  (set-arity2 op old-arity)
  (expected buffer '("consistent arity declaration") t))

(defun expect-arity21 (op arity buffer)
  ; Tell the user that he made an error.
  (princ "The operator has:")
  (display-one-arity2 op)
  (princ (uconcat "    but now has the arity of length " arity "."))
  (terpri)
  (expected buffer '("consistent arity declaration") t))

(defun expect-arity (op arity buffer &aux old-arity)
  ; Tell the user that he made an error.
  (if* (is-valid-var op) 
      then (princ "The variable has:") 
      else (princ "The operator has:"))
  (display-one-arity2 op)
  (setq old-arity (get-arity2 op))
  (set-arity2 op arity)
  (princ "         but now:")
  (display-one-arity2 op)
  (set-arity2 op old-arity)
  (expected buffer '("consistent arity declaration") t))

