;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

#|
;; in xrrl.lsp
(defun structure-induc-on (eqn num &aux vars p-term conjs hypo)
  ; eqn is the equation to be proven.
  ; return a list of conjectures.
  (if* (setq conjs (str-choose-one-scheme eqn)) then
      (setq vars (car conjs)
	    p-term (make-term 'P vars))
      (terpri) (princ "Let ") (write-term p-term)
      (princ " be") (write-seq-num num) (write-f-eqn eqn nil t) (terpri)
      (princ "The induction will be done on ")
      (write-variable (car vars) nil)
      (princ " and will follow the scheme: ") (terpri)
      (sloop for n from 1 for sch in (cdr conjs) do
	(princ "   ") 
	(write-seq-num (append1 num n))
	(setq hypo nil)
	(write-term (make-term 'P (cadr sch)))
	(if* (cddr sch) then 
	    (setq hypo (list '*&* (make-pre (make-term 'P (caddr sch)) nil)))
	    (princ " if ") (write-premises (cdr hypo)))
	(terpri))
      conjs))
|#

(defun str-choose-one-scheme (eqn)
  ; Return a cons of (var1) and a list of
  ;      (nil (term1) (t11))
  (sloop with var for type-cons in $type-constructors do
    (if* (and (cdr type-cons)
	     (setq var (one-type-var-list (lhs eqn) (car type-cons))))
	(return (str-formulate-scheme (car var) (car type-cons) (cdr type-cons))))
    finally (return nil)))

(defun str-formulate-scheme (var type ops)
  (setq ops (mapcar 'basic-term ops))
  (cons (ncons var)
	(sloop for term in ops 
	      collect (if* (cdr term)
			  (list nil (ncons term) 
				; induction hypothesis.
				(ncons (car (one-type-var-list term type))))
			  (list nil (ncons term))))))

