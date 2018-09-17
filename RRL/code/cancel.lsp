;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Following are brand-new codes.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro many-args2 (eqn)
  `(if* (and (nonvarp (lhs ,eqn)) (ac-root (lhs ,eqn)) 
	    (> (length (lhs ,eqn)) $post-bound))
       then t
       elseif (and (nonvarp (rhs ,eqn)) (ac-root (rhs ,eqn)))
       then (> (length (rhs ,eqn)) (times $post-bound $many-args))))

(defun divisible-check (t1 t2 &aux op-term avoid unity pair)
  ; return a pair if t1 and t2 can be simplified by cancelation rules.
  (if* (and ; (not (is-assoc-pair t1 t2))
	   ;(not (is-assoc-pair-under-c t1 t2))
	   (nonvarp t1)
 	   (setq op-term (assoc (op-of t1) $divisible))) then 
      (setq avoid (second op-term)
	    unity (third op-term)
	    pair (list t1 t2))
      (if* avoid then (setq avoid (ncons avoid)))
      (if* unity then (setq unity (ncons unity)))
      (sloop with pair2 
	    while (and (nonvarp t1) 
		       (nonvarp (car pair))
		       (same-op t1 (car pair))
		       (setq pair2 (divisible-check2 (car pair) (rhs pair) avoid unity)))
	    do (setq pair pair2))
      (if* (nequal t1 (car pair)) then
	  (if* (many-args2 pair) then
	      'p
	      else
	      (trace-divisible t1 t2 pair)
	      pair))))

(defun divisible-check2 (t1 t2 avoid unity)
  (if* (or (ac-root t1) (comm-root t1))
      then (divisible-ac-check t1 t2 avoid unity)
      else (divisible-nonac-check t1 t2 avoid unity)))
	  
(defun divisible-nonac-check (t1 t2 avoid unity &aux op res)
  ; check whether t1 and t2 can be simplified by cancellation law,
  ; where t1 is rooted by a non-ac operator.
  (if* (and unity (avoidable avoid t2)) then
      (if* (equal (left-arg (setq op (op-of t1)) t1) t2) then
	  (setq t1 (remove-left-arg op t1)
		t2 unity)
	  (if* (equal t1 t2)
	      (setq res (list t t))
	    (setq res (list t1 t2)))
	  elseif (equal (right-arg op t1) t2) then 
	  (setq t1 (remove-right-arg op t1)
		t2 unity)
	  (if* (equal t1 t2)
	      (setq res (list t t))
	    (setq res (list t1 t2)))))

  (if* res then res 
      elseif (not (and (nonvarp t2) (eq (setq op (op-of t1)) (op-of t2))))
      then nil
      elseif (eq (get-status op) 'rl)
      then (if* (setq res (divisible-right-check op t1 t2 avoid))
	       then res
	       else (divisible-left-check op t1 t2 avoid))
      elseif (setq res (divisible-left-check op t1 t2 avoid))
      then res
      else (divisible-right-check op t1 t2 avoid)))

(defun divisible-left-check (op t1 t2 avoid &aux res)
  (if* (and (equal (left-arg op t1) (left-arg op t2))
	   (avoidable avoid (left-arg op t1))
	   (not (reducible (setq res (remove-left-arg op t1)))))
      then (list res (remove-left-arg op t2))))

(defun divisible-right-check (op t1 t2 avoid &aux res)
  (if* (and (equal (setq res (right-arg op t1)) (right-arg op t2))
	   (avoidable avoid (right-arg op t1))
	   (not (reducible (setq res (remove-right-arg op t1)))))
      then (list res (remove-right-arg op t2))))
	  
(defun divisible-ac-check (t1 t2 avoid unity &aux term)
  ; check whether t1 and t2 can be simplified by cancellation law,
  ; where t1 is rooted by an ac operator.
  (if* (and unity (avoidable avoid t2) (member0 t2 t1)) then
      (setq t1 (remove0 t2 t1 1)
	    t2 unity)
      (if* (null (cddr t1)) then (setq t1 (cadr t1)))
      (if* (equal t1 t2) (setq term (list t t)) (setq term (list t1 t2))))
  
  (if* term then term 
      elseif (and (nonvarp t2)
		  (same-op t1 t2)
		  (setq term (avoid-common-term avoid (args-of t1) (args-of t2)))) then
      (setq t1 (remove0 term t1 1)
	    t2 (remove0 term t2 1))
      (if* (null (cddr t1)) then (setq t1 (cadr t1)))
      (if* (null (cddr t2)) then (setq t2 (cadr t2)))
      (list t1 t2)))

(defun avoidable (avoid term)
  (if* (null avoid) then t
      elseif (variablep term) then nil
      elseif (equal avoid term) then nil
      elseif (null (all-vars term)) then t
      else nil))

(defun avoid-common-term (avoid arg1 arg2)
  (sloop for term in arg1 
	if (and (member0 term arg2) (avoidable avoid term)) return term
	finally (return nil)))

(defun right-arg (op term)
  (if* (and (memq op $associative) (eq (get-status op) 'lr))
      then (right-arg2 op term) else (second-arg term))) 


(defun remove-right-arg (op term)
  (if* (eq (get-status op) 'rl) 
      then (first-arg term) 
      else (remove-right-arg2 op term)))

(defun left-arg (op term)
  ; return the leftest arguments of the operator "op".
  (if* (and (memq op $associative) (eq (get-status op) 'rl))
      then (left-arg2 op term) else (first-arg term)))

(defun remove-left-arg (op term)
  ; Remove the leftest arguments of the operator "op".
  (if* (eq (get-status op) 'lr) 
      then (second-arg term) 
      else (remove-left-arg2 op term)))

(defun right-arg2 (op term)
  (if* (variablep term) then term
      elseif (eq op (op-of term)) then (right-arg2 op (second-arg term))
      else term))

(defun remove-right-arg2 (op term &aux new)
  (if* (variablep term) then nil
      elseif (eq op (op-of term)) 
      then (if* (setq new (remove-right-arg2 op (second-arg term)))
	       then (list op (first-arg term) new)
	       else (first-arg term))))

(defun left-arg2 (op term)
  ; return the leftest arguments of the operator "op".
  (if* (variablep term) then term
      elseif (eq op (op-of term)) then (left-arg2 op (first-arg term))
      else term))

(defun remove-left-arg2 (op term &aux new)
  ; Remove the leftest arguments of the operator "op".
  (if* (variablep term) then nil
      elseif (eq op (op-of term)) 
      then (if* (setq new (remove-left-arg2 op (first-arg term)))
	       then (list op new (second-arg term))
	       else (second-arg term))))

(defun remove-one-arg (pair eqn)
  (setq pair (append pair (cddr eqn)))
  pair)

(defun trace-divisible (t1 t2 pair)
  (if* (> $trace_flag 1) then
      (terpri) (princ "By cancellation law, the pair of the terms") (terpri)
      (princ "    [") (write-term t1) (princ ", ") 
      (write-term-simple t2) (princ "]") (terpri)
      (princ "    is simplified to: ") 
      (princ "    [") (write-term (lhs pair)) (princ ", ") 
      (write-term-simple (rhs pair)) (princ "]") (terpri)))

;;;;;;;;;;;;;;;;
;;; functions delt with associative operators.
;;;;;;;;;;;;;;;;


(defun new-rule-from-assoc (rule &aux op var lhs rhs)
  ; make a new rule for "rule" by associativity.
  (if* (and (memq (setq op (op-of (lhs rule))) $associative)
	   (get-status op)) then
      (setq var (make-new-variable))
      (caseq (get-status op)
	(lr (setq lhs (insert-term-at-right op (lhs rule) var)))
	(rl (setq lhs (insert-term-at-left  op (lhs rule) var))))
      (if* (not (reducible lhs)) then
	  (caseq (get-status op)
	    (lr (setq rhs (insert-term-at-right op (rhs rule) var)))
	    (rl (setq rhs (insert-term-at-left  op (rhs rule) var))))
	  (setq rule (make-new-rule lhs rhs (ctx rule) (list 'asso (ruleno rule))))
	  (add-rule rule))))

(defun insert-term-at-right (op t1 t2)
  ; t1 is as if a binary tree with the node "op". 
  ; Insert "t2" at the right most leaf of the tree.
  (if* (and (nonvarp t1) (eq op (op-of t1)))
      then (list op (first-arg t1) (insert-term-at-right op (second-arg t1) t2))
      else (list op t1 t2)))

(defun insert-term-at-left (op t1 t2)
  (if* (and (nonvarp t1) (eq op (op-of t1)))
      then (list op (insert-term-at-left op (first-arg t1) t2) (second-arg t1))
      else (list op t2 t1)))
      
