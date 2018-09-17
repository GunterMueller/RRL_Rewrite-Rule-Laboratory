;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1992 Hantao Zhang.  All rights reserved.

(in-package "USER")

; This file contains functions to implement the new boolean
; simplfication algorithms.

(defun new-trans-simp (term)
  (cond
    ((null term) nil)
    ((variablep term) term)
    (t (ba-simplify (new-first-trans term)))))

(defun new-first-trans (term)
  (cond
    ((null term) nil)
    ((variablep term) term)
    (t (let ((new-args (mapcar 'new-first-trans (args-of term))))
	 (case (op-of term)
	       (not `(not . ,new-args))
	       (and  `(and . ,new-args))
	       (or  `(or . ,new-args))
	       (-> `(or ,(cadr new-args) (not ,(car new-args))))
	       (equ `(= . ,new-args))
	       (xor `(= (not ,(car new-args)) ,(cadr new-args)))
	       (t (make-term (op-of term) new-args)))))))

(defun ba-simplify (term)
  ;; Simplify the term by Boolean algebra.
  ;; It's possible that a tautology is not simplified to true.
  (if (or (null term) (variablep term) (null (args-of term)))
      term
    (case (op-of term)
	  (and (ba-simp-and (mapcar #'ba-simplify (args-of term))))
	  (or (ba-simp-or (mapcar #'ba-simplify (args-of term))))
	  (not (ba-simp-not (ba-simplify (first-arg term))))
	  (eq (make-term '= (mapcar #'ba-simplify (args-of term))))
	  (t (make-term (op-of term) (mapcar #'ba-simplify (args-of term))))
	  )))

(defun ba-simp-and (args)
  (if (member0 $false-term args)
      $false-term
    (sloop with poss = nil
	   with negs = nil
	   with arg = nil
	   while args do
	   (setq arg (pop args))
	   (if (variablep arg)
	       (if (member0 (make-term 'not arg) negs)
		   (return $false-term)
		 (query-insert arg poss))
	     (case (op-of arg)
		   (true nil)
		   (and (setq args (append (args-of arg) args)))
		   (not (if (member0 (first-arg arg) poss)
			    (return $false-term)
			  (query-insert arg negs)))
		   (or (if (not (or (have-common (args-of arg) poss)
				    (have-common (args-of arg) negs)))
			   (query-insert arg poss)))
		   (t (if (member0 (make-term 'not arg) negs)
			  (return $false-term)
			(query-insert arg poss)))))
	finally (return (if (setq poss (append
					(sort poss 'total-order)
					(sort negs 'total-order)))
			    (if (cdr poss)
				(make-term 'and poss)
			      (car poss))
			  $true-term)))))

(defun ba-simp-or (args)
  (if (member0 $true-term args)
      $true-term
    (sloop with poss = nil
	   with negs = nil
	   with arg = nil
	   while args do
	   (setq arg (pop args))
	   (if (variablep arg)
	       (if (member0 (make-term 'not arg) negs)
		   (return $false-term)
		 (query-insert arg poss))
	     (case (op-of arg)
		   (false nil)
		   (or (setq args (append (args-of arg) args)))
		   (not (if (member0 (first-arg arg) poss)
			    (return $true-term)
			  (query-insert arg negs)))
		   (and (if (not (or (have-common (args-of arg) poss)
				     (have-common (args-of arg) negs)))
			    (query-insert arg poss)))
		   (t (if (member0 (make-term 'not arg) negs)
			  (return $true-term)
			(query-insert arg poss)))))
	finally (return (if (setq poss (append
					(sort poss 'total-order)
					(sort negs 'total-order)))
			    (if (cdr poss)
				(make-term 'or poss)
			      (car poss))
			  $false-term)))))

(defun ba-simp-not (arg)
  (cond ((null arg) $false-term)
	((variablep arg) (make-term-1arg 'not arg))
	(t (case (op-of arg)
		 (false $true-term)
		 (true $false-term)
		 (not (first-arg arg))
		 (t (make-term-1arg 'not arg))
		 ))))

(defun new-first-ctx-trans (ctx)
  ;; This is a termpory function. To be fixed. 12/3/90.
  (cons '*&* (first-ctx-trans ctx)))

