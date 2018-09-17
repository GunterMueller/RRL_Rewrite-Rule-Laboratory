;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "RRL")

#+franz
(declare (special $premises-set $reduced-premises $old $falsed-pre $deep-condi))

; ********WARNING*********
; *****Parental guidance suggested for children under the age of 17*********
; ********WARNING*********

;;;;  Functions to use premises to simplify other terms

(defun normalize-by-premises (term)
  (setq term (subst-var-premises term))
  (norm-by-premises term (cdr $premises-set)))

(defun norm-by-premises (term rules)
  (loop with tmp1 = term 
	if (setq tmp1 (reduce-by-premises term rules))
	do (setq term tmp1)
	else return term))

(defun subst-var-premises (term)
  (if $var-premises
      (flat-term (applysubst $var-premises term)) 
    term))

(defun reduce-by-premises-at-root (term rules)
  ; return the reduced term if rules xan reduce term.
  ; Otherwise, return nil.
  (loop with nterm for rule in rules 
        if (setq nterm (reduce-by-premise-at-root (get-pre-lhs rule) 
						  (get-pre-rhs rule) term))
        return (progn (if (not (is-used-pre rule)) 
			  then (mark-used-pre rule))
		      (cycle-check nterm)
		      nterm)
	finally (return nil)))

(defun reduce-by-premise-at-root (lhs rhs term)
  (if (equal lhs term) then rhs
    elseif (or (variablep term) (variablep lhs)) then nil
    elseif (and (same-op lhs term) (ac-root lhs) (is-sublist lhs term))
    then (make-flat (make-term (op-of term)
			       (cons rhs (list-diff term lhs))))))	

(defun reduce-by-premises (term pres)
  ; reduce term once by pres, where pres are a bunch of premises.
  ; return the reudced term if term is reducible. Otherwise, nil.
  (loop with newterm for rule in pres 
        if (and (nonvarp (first rule))
		(setq newterm (reduce-by-premise-at-root 
				(get-pre-lhs rule) 
				(get-pre-rhs rule) term)))
	  return (progn (if (not (is-used-pre rule)) 
			    then (mark-used-pre rule))
			(cycle-check newterm)
			newterm)
	finally (return (reduce-args-by-premises term pres))))

(defun reduce-args-by-premises (term pres)
  ; reduce the arguments of term once by pres, where pres are a bunch of premises.
  ; return the reudced term if term is reducible. Otherwise, nil.
  (cond ((variablep term) nil)
	((loop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (reduce-by-premises xa pres)))
	   return (flat-term (rplnthsubt-in-by i term xa))
	   finally (return nil)))))

(defun subst-premises (subst pres)
  ; apply "subst" on each premises in "pres".
  (if (and pres (cdr pres)) then
      (cons '&& (loop for pre in (cdr pres) 
		      collect (make-pre (flat-term (applysubst subst (car pre)))
					(flat-term (applysubst subst (cadr pre))))))))

