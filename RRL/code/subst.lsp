;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")


; This file contains functions formerly in unify.
; These functions manipulate substitutions, mostly used in ac unification.


(defun size-uni (uni) 
  (if* (eq uni *empty-sub*)
      0
    (ncons (sloop for x in uni sum (size (cdr x))))))

(defun lessp-size-bindings(uni1 uni2)
  ; to make sort stable you need < on the lisp machine and <= on franz lisp.
  #+franz (<= (caar uni1) (caar uni2))
  #-franz (< (caar uni1) (caar uni2))
  ) 

(defun empty-sub(sub) (equal sub *empty-sub*))

(defun compose (sub1 sub2)
  ; form the composition of the two substitutions, sub1(sub2)
  (if* (or (null sub1) (null sub2)) nil
      (if* (empty-sub sub2) sub1
	  (if* (empty-sub sub1) sub2
			  (append
			    (sloop for sub in sub2 collecting
				 (cons (car sub) (apply-to (cdr sub) sub1 )))
			    sub1)))))

(defun compose1 (sub1 sub2)
  (sloop for xa in sub1
	if (not (assoc (car xa) sub2)) 
	do (setq sub2 (cons (cons (car xa) (apply-to (cdr xa) sub2)) sub2))
	finally (return sub2)))

; domain(sub1) intersect domain(sub2) == empty
; and sub1 and sub2 are valid. returns normal form of
; sub1 wrt sub2 .

(defun norm-sub (sub1 sub2)
  (sloop with bin for xb in sub1
	if (occurs-in (car xb) (setq bin (apply-to (cdr xb) sub2)))
	  return nil
	else collect (cons (car xb) bin) into new
        finally (return new)))

; domains non-intersecting as above returns composition
(defun comp1 (sub1 sub2)
  (sloop for sub in sub2
	if (and (setq sub (norm-sub (ncons sub) sub1))
		(setq sub1 (norm-sub sub1 sub))) 
	  do (nconc sub1 sub)
	else return nil
	finally (return sub1)))

; resolves 2 substitutions sigma1 and sigma2 . Returns
; all possible most-general sigma such that
;  sigma = sigma1 o phi1  and sigma = sigma2 o phi2

(defun resolve (sub1 sub2)
  (let ((l1 nil) (int nil) (d1 nil) (d2 nil))
    (setq l1 (sloop for sub in sub1
		   if (assoc (car sub) sub2) collect (car sub) into i1
		   else collect sub into i2
		   finally(return (cons i1 i2))))
    (setq d1 (cdr l1) int (car l1))
    (if* int then
	(setq d2 (sloop for sub in sub2
		       if (not (memq (car sub) int)) collect sub))
	(if* (and d1 d2) (setq d1 (comp1 d1 d2))
	    (setq d1 (or d1 d2)))
	(if* d1 then
	    (setq l1 (unicompound (sloop for x in int
					collect (apply-to (cdr (assoc x sub1)) d1))
				  (sloop for x in int
					collect (apply-to (cdr (assoc x sub2)) d1))))
	    (if* l1 
		(sloop with ans = nil
		      for sub in l1 
		      do (nconc sub
				(sloop for x in int 
				      collect (cons x (apply-to 
							(cdr (assoc x sub1)) 
							sub))))
			 (setq ans (cons (compose sub d1) ans))
		      finally (return ans)))
	    else
	    (setq l1 (unicompound (sloop for x in int 
					collect (cdr (assoc x sub1)))
				  (sloop for x in int 
					collect (cdr (assoc x sub2)))))
	    (sloop for sub in l1
		  collect (nconc sub
				 (sloop for x in int 
				       collect
					 (cons x (apply-to (cdr (assoc x sub1))
							   sub))))))
	else (ncons (comp1 sub1 sub2)))))

(defun compose2 (sub sublis)
  (if* sub (sloop for s1 in sublis
		collect (compose s1 sub)) sublis))

(defun apply-to2 (term sigma)
  ; takes flattened term, returns flattened substitued term
  ; sigma is already flattened.
  (cond
    ((variablep term) (or (cdr (assoc term sigma)) term))
    ((null (args-of term)) term)
    (t (let ((args (sloop for arg in (args-of term) collect
						     (apply-to arg sigma))))
	 (compress-flat (op-of term) args)))))

(defun apply-to (term sigma) (applysubst sigma term))
 
