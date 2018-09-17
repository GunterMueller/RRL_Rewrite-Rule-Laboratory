;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "RRL")



;-------------------------------------
; Miscellanous functions on operators.
;-------------------------------------

(defun is-constant-op (op) (equal (get-arity op) 0))

;; can return nil & this causes trouble in narrow etc.
;; where new ops are used like solution!
(defun get-arity (op)
  (if (numberp op) 0 (get op 'arity)))

(defun gennewsym (sym)
   ; gennewsym makes a new symbol.
   (initsym sym)
   (loop for xa = (newsym sym)
	 if (not (memq xa $operlist)) 
	 return (progn (push xa $operlist) xa)))

(defun clear-operators ()
  ; Clears the operator list.
  (loop for op in $operlist if (not (is-bool-op op))
	do (rem-arity op) (rem-arity2 op)
	   (rem-infix op) (rem-predicate op) (rem-skolem op))
  (setq $operlist nil))

(defun exist-op (op)
  (or (loop for xa in $eqn-set thereis
	   (or (memq op (op-list (lhs xa))) 
	       (memq op (op-list (rhs xa)))))
      (loop for xa in $post-set thereis
	   (or (memq op (op-list (lhs xa))) 
	       (memq op (op-list (rhs xa)))))
      (loop for xa in $rule-set thereis
	   (or (memq op (op-list (lhs xa))) 
	       (memq op (op-list (rhs xa)))))))
      
(defun same-arity (op1 op2)
  ; Return true iff there is an operator f1 equivalent to op1 and
  ; an operator f2 equivalent to op2 such that f1 and f2 have the same
  ; arity.
  (loop for xa in (ops-equiv-to op1) thereis
      (let ((l1 (get-arity xa)))
         (loop for xb in (ops-equiv-to op2) thereis (equal (get-arity xb) l1)))))
                 
(defun get-constants (ops)
  ; Returns all constant in OPS.
  (loop for xa in ops if (equal (get-arity xa) 0) collect xa))

(defun non-constants (ops)
  ; Returns all non-constant operators in OPS
  (loop for xa in ops if (nequal (get-arity xa) 0) collect xa))

(defun get-free-constructors ()
  ; Returns all free constructors in $constructors.
  (loop for op in $constructors 
	if (and (not (commutativep op))
	        (not (ac-op-p op))
		(null (cdr (get-def-domain op)))) collect op))

(defun display-constructors (type-ops)
   (princ "The system has the following constructors:") (terpri)
   (if (cddr type-ops) 
     then (loop for ty-ops in (cdr (reverse type-ops)) do
           (princ (uconcat "     Type '" (car ty-ops) "': "
		  	   (display-ops (cdr ty-ops)))) (terpri))
     else (setq type-ops (car type-ops))
	  (princ (uconcat "     Type '" (car type-ops) "': "
		  	   (display-ops (cdr type-ops)))) 
	  (terpri)))

(defun clean-ops (ops)
    (loop for xa in $rule-set 
	  as ops1 = (op-list (lhs xa))
	  as ops2 = (op-list (rhs xa)) do
	(setq ops (loop for op in ops 
			if (not (or (memq op ops1) (memq op ops2)))
			collect op))
	(if (null ops) then (return nil)))
    (loop for xa in $eqn-set 
	  as ops1 = (op-list (lhs xa))
	  as ops2 = (op-list (rhs xa)) do
	(setq ops (loop for op in ops 
			if (not (or (memq op ops1) (memq op ops2)))
			collect op))
	(if (null ops) then (return nil)))
    (loop for op in ops do 
	(setq $operlist (delq op $operlist 1)
	      $constructors (delq op $constructors 1))
	(delq op (assoc (get-domain-type op) $type-constructors))))
