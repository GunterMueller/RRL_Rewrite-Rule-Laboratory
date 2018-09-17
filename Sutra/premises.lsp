;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "RRL")


#+franz (declare (special $falsed-pre $reduced-premises))
(setq $falsed-pre nil)

; ********WARNING*********
; *****Parental guidance suggested for children under the age of 17*********
; ********WARNING*********

; The premise set of an equation or a rule is organized as
; a ground rewriting system. 
; The mark of a premise set is "&&".
; Each premise is in form of
;          (lhs rhs property-list)
; lhs is a predicate term. Sometimes lhs is rooted by "and" and sometimes
; is rooted by "=", in this case, two function terms are arguments of "=".
; rhs is either nil, means true or a predicate term.
; We have the following macros for premises.
;    make-pre: make a new premise from a pair of terms.
;    is-premise-set: return t if (eq (car (ctx eqn)) '&&).
;    get-premises: return a list of premises without the mark.
;    get-pre-lhs: return the left-hand side when a premise is viewed as a rule.
;    get-pre-rhs: return the right-hand side when a premise is viewed as a rule.

#+franz (declare (special $try))
(setq $try nil)

;;; Functions to process and simplify premises.

(defun pre-process-premises (pre)
  ; pre is a premises or a conjuction of premises.
  ; turn all premises in standard forms and put them in $premises-set
  ; without simplify other premises.
  (if pre then
      (caseq (op-of pre)
	(eq (if (null (cdddr pre))
		then (pre-process-pre-ass (cons '= (cdr pre)))
		else (pre-process-pre-ass pre)))
	(and (mapcar 'pre-process-premises (args-of pre)))
	(t (pre-process-pre-ass pre)))))

(defun pre-process-pre-ass (term)
  ; make a new premise from term and put it at the end of $premises-set.
  (if (falsep $premises-set) then nil
      elseif (variablep term) then
      (setq $premises-set (cons 'false (cdr $premises-set)))
      elseif (eq (op-of term) 'and) 
      then (mapcar 'pre-process-pre-ass (args-of term))
      elseif (truep term) then nil
      else (add-premise-end (make-pre-ass term nil))))

(defun simplify-one-pre (pre &aux first second)
  ; simplify pre using rules and premsies, put the reduced result 
  ; at the end of $premises-set.
  (if (variablep (car pre))
      then (add-simplify-others (subst-var-premises pre))
      else
      (setq first (norm-ctx (first pre))
	    second (second pre))
      (if (and (or (truep second)
		   (equal (setq second (norm-ctx second)) (cadr pre)))
	       (equal first (car pre)))
	  then (add-simplify-others pre)
	  elseif (equal first second) then nil
	  elseif (and (variablep first) (truep second)) 
	  then (setq $premises-set (cons 'false (cdr $premises-set)))
	  else
	  (if (not (truep second)) 
	      (setq first (eqn2assertion (list first second))))
	  (process-pre-ass first (cddr pre)))))

(defun add-simplify-others (pre &aux lhs)
  ; add "pre" at the end of $premises-set and $reduced-premises
  ; Simplify all premises of $reduced-premises.
  (setq lhs (if (variablep (car pre)) (car pre) (get-pre-lhs pre)))
  (loop for pre2 in $reduced-premises
	if (is-subterm lhs (first pre2))
	do (setq $reduced-premises (remove pre2 $reduced-premises)))
  (add-premise-end pre)
  (push pre $reduced-premises))

(defun add-premise-end (pre)
  (if (variablep (car pre)) 
      then
    (if (memq 'body pre) (push (ncons 'body-role) $var-premises))
    (push (cons (car pre) (cadr pre)) $var-premises)
    else
    (add-end pre $premises-set)))

(defun simplify-premises (pres &optional save)
  (if save then (setq save $premises-set $premises-set '(&&)))
  (loop for xa in pres do (simplify-pre xa t))
  (if (falsep $premises-set) then nil
      elseif (null (cdr $premises-set)) 
      then (setq $premises-set nil $var-premises nil))
  (if save then (prog1 $premises-set (setq $premises-set save))))

(defun simplify-pre (pre &optional add)
  (if (and add (falsep $premises-set)) 
      then $premises-set 
      elseif (variablep (car pre))
      then (if add (add-premise-end pre) pre)
      elseif (truep (cadr pre))
      then (process-pre-ass (norm-ctx (car pre)) (cddr pre) add)
      else (process-pre-ass (norm-ctx (eqn2assertion pre)) (cddr pre) add)))

(defun process-pre-ass (term &optional info (add t))
  ; If add is t then adding term to $premises-set and simplifying  
  ; other premises. Otherwise, returns the premise made from term.
  (if (truep term) then nil
      elseif (not add)
      then (if (falsep term) term (make-pre-ass term info))
      elseif (falsep term)
      then (setq $premises-set (cons 'false (cdr $premises-set)))
      elseif (eq (op-of term) 'and)
      then (loop for arg in (args-of term) 
		 do (add-simplify-others (make-pre-ass arg info)))
      elseif (eq (op-of term) 'xor)
      then (loop for pair in (separate-xor-args (args-of term)) do
		 (add-simplify-others (make-pre (car pair) (cdr pair) info)))
      else (add-simplify-others (make-pre-ass term info))))

;;;
;;; Some special tricks to simplify premises.
;;;

(defun reduce-reverse-premises (pres &optional eqn)
  ; A premise can be reversed if it is of form
  ;          (f(t1, t2, ..., tn) = t)
  ; Try to use (t = f(t1, t2, ..., tn)) to reduce others.
  ; Restore $premeises-set when exit.
  (loop with eqn2 with pre2 for pre in (cdr $premises-set) do
    (if (and (is-eq-true-pre pre) 
	     (or (variablep (setq pre2 (second-arg (car pre))))
		 (is-constant-term pre2))) then
	(setq pre2 (args-of (first pre))
	      $premises-set (subst (first pre2) (second pre2) (remove pre pres))
	      $reduced-premises nil
	      eqn (subst (first pre2) (second pre2) eqn))
	(simplify-all-premises)
	(if (or (falsep $premises-set)
		(and eqn (null (checkeq-normal eqn2)))) then
	    (terpri) (princ "Note: The premise ") 
	    (write-one-pre pre nil t) 
	    (princ " is used reversely.") (terpri)
	    (setq $premises-set (cons 'false (cdr pres)))
	    (if (not (is-used-pre pre)) then (mark-used-pre pre))
	    (return t)))
	finally (progn (setq $premises-set pres)
		       (return nil))))

(defun reverse-premise (term)
  ; term is of form (= term1 term2)
  ; return (term2 . term1) if term2 is variable.
  (if (variablep (second-arg term))
      then (cons (second-arg term) (first-arg term))))

(defun premises-are-true (pres)
  ; return t iff all premises in "pres" are true.
  (loop for pre in (cdr pres) 
	if (not (one-premise-is-true pre))
	  return nil
	finally (return t)))

(defun one-premise-is-true (pre &aux first second)
  ; simplify pre using rules and premsies, put the reduced result 
  ; at the end of $premises-set.
  (if (variablep (car pre))
      then nil
      else
      (setq first (norm-ctx (first pre))
	    second (second pre))
      (if (equal first (car pre)) then nil
	  elseif (truep second) then (truep first)
	  else (equal (norm-ctx second) first))))

(defun nofalse-premises (pres &optional sigma)
  ; If one of premises in "pres" is false then return "false".
  ; Otherwise, return all premises in "pres" that is not equal to true.
  (if (eq $induc 'c) then
      (cons '&& (loop for pre in (cdr pres) 
		      collect (flat-term (applysubst sigma pre))))
      else
      (loop with result 
	    for pre in (cdr pres) do
		(setq pre (simplify-pre (flat-term (applysubst sigma pre))))
		(if pre then
		    (caseq (op-of pre)
		      (false (return pre))
		      (and (loop for xa in (args-of pre) do (push xa result)))
		      (t (push pre result))))
	    finally (return (if result then (make-term '&& result))))))

;; Functions to make new premises.

(defun make-pre-ass (ass info)
  ; "ass" is a predicate term. Make it as a standard premises.
  (if ass then
      (caseq (op-of ass)				
	(true nil)
	(= (make-pre-eqn (args-of ass) info))
	(eq (if (cdddr ass) 
		then (make-pre ass nil info)
		else (make-pre-eqn (commu-exchange (args-of ass)) info)))
	(xor (make-pre-xor-args (args-of ass) info))
	(t (make-pre ass nil info)))))

(defun remake-premises (ctx)
  (if (eq (car ctx) '&&) then
      (cons '&& (loop for xa in (cdr ctx) 
		      collect (if (truep (cadr xa)) 
				  then (make-pre-ass (car xa) (cddr xa))
				  else xa)))
      else ctx))

(defun make-pre-xor-args (args info)
  (loop with one = (car args)
	for arg in (cdr args) 
	if (pseudo-term-ordering one arg) 
	do (setq one arg)
	finally (return (make-pre one (negate-xor-args (remq one args 1)) info))))

(defun separate-xor-args (args &aux lhs)
  ; Check if "args" is in form of "((t1 and t2) t1 t2)". 
  ; If it is, return ((t1 (false)) (t2 (false))), where t1, t2 are terms.
  ; Otherwise, pick out the biggest of "args", say "lhs", then
  ; return ((lhs "args - lhs")).
  (setq lhs (car args))
  (loop for arg in (cdr args) 
	if (pseudo-term-ordering lhs arg) do (setq lhs arg))
  (setq args (negate-xor-args (remq lhs args 1)))  
  (if (and (eq (op-of lhs) 'and) (equal (args-of lhs) (args-of args)))
      then (loop for arg in (args-of args) collect (cons arg '(false)))
      else (ncons (cons lhs args))))

(defun make-pre-eqn (eqn info)
  (if eqn  then
    (let ((lhs (lhs eqn)) (rhs (rhs eqn)))
      (if (nequal lhs rhs) then
	  (if (variablep lhs)
	      then (if (is-subterm lhs rhs) 
		       then (make-pre (list '= rhs lhs) nil info)
		       else (make-pre lhs rhs info))
	      elseif (variablep rhs)
	      then (if (is-subterm rhs lhs) 
		       then (make-pre (list '= lhs rhs) nil info)
		       else (make-pre rhs lhs info))
	      elseif (pseudo-term-ordering lhs rhs)
	      then (if (predicatep (op-of lhs))
		       then (make-pre rhs lhs info) 
		       else (make-pre (list '= rhs lhs) nil info))
	      else (if (predicatep (op-of lhs))
		       then (make-pre lhs rhs info) 
		       else (make-pre (list '= lhs rhs) nil info)))))))

;;; Some operations on premises.

(defun negate-premises (vars pres &optional info) 
  ; return a list of negations of premise if that premise is not leading by a 
  ; variable and has variables in vars.
  (loop for pre in (cdr pres)
	if (and (nonvarp (car pre)) (have-common vars (pre-vars pre)))
	  collect (negate-one-pre pre info)))

(defun negate-one-pre (pre &optional info) 
   ; negate-one-pre: return a negation of pre, still as a premise.
   (if (null info) then (setq info (cddr pre)))
   (if (null (cadr pre)) then (make-pre (car pre) '(false) info)
       elseif (variablep (car pre)) 
       then (make-pre (list '= (cadr pre) (car pre)) '(false) info)
       elseif (falsep (cadr pre)) then (make-pre-ass (car pre) info)
       else (make-pre (car pre) (negate-predicate (cadr pre)) info)))

(defun mark-used-pre (pre) (rplacd (cdr pre) (cons 'used (cddr pre))))

(defun get-pres-ops (pres)
  ; return the ops in pres.
  (loop for pre in pres 
	nconc (loop for op in (op-list (car pre)) 
		    if (not (memq op $bool-ops)) collect op)))

(defun pre-vars (pre) 
  ; Return all vars of pre.
  (rem-dups (nconc (all-vars (car pre)) (if (cadr pre) then (all-vars (cadr pre))))))

(defun pre-ops (pre) 
  ; Return all ops of pre.
  (rem-dups (nconc (all-ops (car pre)) (all-ops (cadr pre)))))

(defun super-itself-pre (pre)
  (let ((lhs (get-pre-lhs pre)) (rhs (get-pre-rhs pre)))
    (if (and (nonvarp lhs) (eq (op-of lhs) 'and))
	(loop for y1 in (args-of pre)
	      collect `((and ,y1 ,lhs) (and ,y1 ,rhs))))))

(defun merge-premises (condi1 condi2)
  (if (null condi1) then condi2
   elseif (null condi2) then condi1
   else (append condi1 (cdr condi2))))

(defun more-vars-premise (vars pres)
  ; return the first premise in "pres" that covers properly vars.
  (loop with big 
	for pre in pres 
	as prevars = (pre-vars pre)
	if (and (is-subset vars prevars) (not (is-subset prevars vars)))
	do (if (or (null big) 
		   (lrpo (car pre) (car big)))
	       then (setq big pre))
	finally (return big)))

(defun pres-size (pres)
  (apply '+ (loop for pre in (cdr pres) 
		    collect (+ (size (car pre)) (size (cadr pre))))))

(defun is-eq-false-pre (pre)
  ; return t iff pre is in form of ((= term1 term2) (false)).
  (and (nonvarp (cadr pre)) (falsep (cadr pre)) (eq (caar pre) '=)))

(defun is-eq-true-pre (pre)
  ; return t iff pre is in form of ((= term1 term2) nil).
  (and (null (cadr pre)) (eq (caar pre) '=)))
