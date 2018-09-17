;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

(in-package "USER")

(setq $falsed-pre nil)

; The premise set of an equation or a rule is organized as
; a ground rewriting system. 
; The mark of a premise set is "*&*".
; Each premise is in form of
;          (lhs rhs property-list)
; lhs is a predicate term. Sometimes lhs is rooted by "and" and sometimes
; is rooted by "=", in this case, two function terms are arguments of "=".
; rhs is either nil, means true or a predicate term.
; We have the following macros for premises.
;    make-pre: make a new premise from a pair of terms.
;    is-premise-set: return t if (eq (car (ctx eqn)) '*&*).
;    get-premises: return a list of premises without the mark.
;    get-pre-lhs: return the left-hand side when a premise is viewed as a rule.
;    get-pre-rhs: return the right-hand side when a premise is viewed as a rule.

;;; Functions to process and simplify premises.

(defun my-first-ctx-trans (ctx)
  ;; This is a termpory function. To be fixed. 12/3/90.
  (cons '*&* (first-ctx-trans ctx)))

(defun first-ctx-trans (ctx)
  (if (variablep ctx) 
      (list (make-pre ctx nil))
    (case (op-of ctx)
	  (and (mapcan 'first-ctx-trans (args-of ctx)))
	  (not (list (make-pre (new-trans-simp (first-arg ctx)) $false-term)))
	  (t (list (make-pre-ass (new-trans-simp ctx) nil))))))

(defun first-process-premises (ctx)
  (setq $premises-set (ncons '|*&*|) $var-premises nil)
  (pre-process-premises ctx)
  (append $premises-set 
	  (sloop for xa in $var-premises
		collect (list (car xa) (cdr xa)))))

(defun pre-process-premises (pre)
  ; pre is a premises or a conjuction of premises.
  ; turn all premises in standard forms and put them in $premises-set
  ; without simplify other premises.
  (if* pre then
      (case (op-of pre)
	    (eq (if (null (cdddr pre))
		    (pre-process-pre-ass (cons '= (cdr pre)))
		  (pre-process-pre-ass pre)))
	    (and (mapcar 'pre-process-premises (args-of pre)))
	    (t (if $var-premises
		   (setq pre (flat-term (applysubst $var-premises pre))))
	       (pre-process-pre-ass pre)))))

(defun pre-process-pre-ass (term &optional head)
  ; make a new premise from term and put it at the end of $premises-set.
  (if* (falsep $premises-set) then nil
       elseif (variablep term) then
       (setf $premises-set (cons 'false (cdr $premises-set)))
       elseif (eq (op-of term) 'and) 
       then (mapcar 'pre-process-pre-ass (args-of term))
       elseif (truep term) then nil
       elseif (eq (op-of term) '=)
       then (add-premise-end (make-pre-eqn (args-of term) nil) head)
       else (add-premise-end (make-pre-ass term nil) head)))

(defun simplify-one-pre (pre)
  ; simplify pre using rules and premsies, put the reduced result 
  ; at the end of $premises-set.
  ;;(mark pre "norm-one-pre1")
  (setq pre (norm-one-pre pre))
  ;;(mark pre "norm-one-pre2")

  (if* (null pre)
      then nil
      elseif (falsep pre)
      then (setq $premises-set (cons 'false (cdr $premises-set)))
      elseif (eq (car pre) '*&*)
      then (setq $reduced-premises nil)
      (nconc $premises-set (cdr pre))
      elseif (variablep (car pre))
      then (add-simplify-others (subst-var-premises pre))
      elseif (and (truep (cadr pre)) 
		  (eq (op-of (car pre)) 'cond))
      then (if* (falsep (second-arg (car pre)))
		then 
		(pre-process-pre-ass (cadddr (car pre)) t)
		(pre-process-pre-ass (negate-predicate (first-arg (car pre))) t)
		elseif (falsep (cadddr (car pre)))
		then 
		(pre-process-pre-ass (second-arg (car pre)) t)
		(pre-process-pre-ass (first-arg (car pre)) t)
		else (add-simplify-others pre)
		)
      else (add-simplify-others pre)))

(defun first-var-pre (first second info)
  (if* (truep second) 
      $false-term
    (make-pre first (cover-norm-term second) info)))

(defun norm-one-pre (pre &aux (first (car pre)) (second (cadr pre)) (info (cddr pre)))

  (if* (variablep first)
    then (first-var-pre first (cadr pre) info)
    elseif (eq (op-of first) 'hint)
    then pre
    else

    (if (not (or (truep second) (falsep second)))
	(setq second (cover-norm-term second)))
    (setq first (cover-norm-term first))
    (make-better-pre first second info)
    ))

(defun make-better-pre (first second info)
  (if (variablep first) (psetq first second second first))

  (if* (equal first second)
       then nil
       elseif (variablep first)
       then (make-pre first second info) ;; this is no good!
       elseif (and second (variablep second) (not (occurs-in second first)))
       then (make-pre second first info) ;; this is a special case!
       else ;; first is not a vairable.
       (arrange-eq-args first second)
       (if (truep second) (setq second nil))

       (when (eq (op-of first) 'not)
	     (setq first (first-arg first)
		   second (if (truep second) $false-term
			    (if (falsep second) nil
			      (ba-simp-not second)))))

       (when (and (eq (op-of first) '=)
		  (falsep second)
		  (nonvarp (first-arg first))
		  (predicatep (op-of (first-arg first))))
	     (setq info (make-better-pre 
			(first-arg first) (ba-simp-not (second-arg first)) info))
	     (return-from make-better-pre info))

       (if* (equal first second)
	    then nil
	    elseif (falsep first) 
	    then first
	    elseif (truep first)
	    then second ;; second is either nil or $false-term

	    elseif (equal first (ba-simp-not second))
	    then $false-term

	    elseif (and (eq (op-of first) '=) (truep second))
	    then (make-eq-pre (first-arg first) (second-arg first) info)

	    elseif (and (eq (op-of first) 'and) (truep second))
	    then (make-better-pres (args-of first) nil info)

	    elseif (and (eq (op-of first) 'or) (falsep second))
	    then (make-better-pres (args-of first) $false-term info)

	    elseif (or (predicatep (op-of first)) 
		       (falsep second) (truep second))
	    then (make-pre first second info)

	    elseif (consistent-pair first second t)
	    then (make-pre (list '= first second) nil info)
	    else $false-term)))

(defun make-better-pres (olds second info &aux news pre)
  ;; make a list of premises of form (x second) for any x in olds.
  (sloop while olds do
	 (setq pre (make-better-pre (pop olds) second info))
	 (if* (null pre) then nil
	      elseif (falsep pre) 
	      then (return-from make-better-pres pre)
	      elseif (variablep (car pre)) then
	      (setq olds (subst (cadr pre) (car pre) olds))
	      (push pre news)
	      elseif (eq (car pre) '*&*) then
	      (sloop for arg in (cdr pre) do
		     (if (variablep (car arg)) 
			 (setq olds (subst (cadr arg) (car arg) olds)))
		     (push arg news))
	      else (push pre news)))
  (if news (if (cdr news) (cons '*&* news) (car news))))

(defun make-eq-pre (first second info)
  (if (or (variablep first) (pseudo-term-ordering first second))
      (psetq first second second first))
  (if (and (variablep second) (not (occurs-in second first)))
      (make-pre second first info)
    (if (predicatep (op-of first))
	(make-better-pre first second info) 
      (make-pre (list '= first second) nil info))))

(defun add-simplify-others (pre &aux rhs lhs)
  ; add "pre" at the end of $premises-set and $reduced-premises
  ; Simplify all premises of $reduced-premises.
  (setq lhs (if (variablep (car pre)) (car pre) (get-pre-lhs pre))
	rhs (get-pre-rhs pre))

  (sloop for pre2 in $reduced-premises
	if (is-subterm lhs (first pre2)) do
	(setq $reduced-premises (remove0 pre2 $reduced-premises))
;	(setf (first pre2) (subst0 rhs lhs (first pre2)))
;	(when (not (truep (second pre2)))
;	      (setf (first pre2) (eqn2assertion 
;				  (list (first pre2) (second pre2))))
;	      (setf (second pre2) nil))
	)

  (add-premise-end pre)
  (push pre $reduced-premises))

(defun add-premise-end (pre &optional head)
  (if* (falsep pre)
       then (break)
       elseif (variablep (car pre)) 
      then
      (if (truep (cadr pre)) (setf (cadr pre) $true-term))
      (if (memq 'head pre) (query-insert (ncons 'head-role) $var-premises))
      (setq $var-premises (subst0 (cadr pre) (car pre) $var-premises))
      (setq $premises-set (subst0 (cadr pre) (car pre) $premises-set))
      (setq $reduced-premises nil)
      (push (cons (car pre) (cadr pre)) $var-premises)
      elseif head
      then (setq $premises-set (cons '*&* (cons pre (cdr $premises-set))))
      else (setq $premises-set (append $premises-set (ncons pre)))
      ))

(defun simplify-premises (pres &optional save)
  (if* save then (setq save $premises-set $premises-set '(*&*)))
  (sloop for xa in pres 
	if (falsep $premises-set) return nil
	else do (simplify-one-pre xa))
  (if* (falsep $premises-set) then nil
      elseif (null (cdr $premises-set)) 
      then (setq $premises-set nil $var-premises nil))
  (if* save then (prog1 $premises-set (setq $premises-set save))))

#|
(defun process-pre-ass (term &optional info (add t))
  ; If add is t then adding term to $premises-set and simplifying  
  ; other premises. Otherwise, returns the premise made from term.
  (if* (truep term) then nil
      elseif (not add)
      then (if (falsep term) term (make-pre-ass term info))
      elseif (falsep term)
      then (setq $premises-set (cons 'false (cdr $premises-set)))
      elseif (eq (op-of term) 'and)
      then (sloop for arg in (args-of term) 
		 do (add-simplify-others (make-pre-ass arg info)))
      elseif (eq (op-of term) 'xor)
      then (sloop for pair in (separate-xor-args (args-of term)) do
		 (add-simplify-others (make-pre (car pair) (cdr pair) info)))
      else (add-simplify-others (make-pre-ass term info))))
|#

(defun process-pre-ass (args &optional info)
  (add-simplify-others (make-pre-eqn args info)))

;;;
;;; Some special tricks to simplify premises.
;;;

(defun reduce-reverse-premises (pres &optional eqn)
  ; A premise can be reversed if it is of form
  ;          (f(t1, t2, ..., tn) = t)
  ; Try to use (t = f(t1, t2, ..., tn)) to reduce others.
  ; Restore $premeises-set when exit.
  (sloop with eqn2 with pre2 for pre in (cdr $premises-set) do
    (if* (and (is-eq-true-pre pre) 
	      (setq pre2 (second-arg (car pre)))
	      (or (variablep pre2) (is-constant-term pre2))) then
	(setq pre2 (args-of (first pre))
	      $premises-set (subst0 (first pre2) (second pre2) (remove0 pre pres))
	      $reduced-premises nil
	      eqn (subst0 (first pre2) (second pre2) eqn))
	(simplify-all-premises)
	(if* (or (falsep $premises-set)
		 (and eqn (null (checkeq-normal eqn2)))) 
	     then
	     (when (> $trace_flag 1)
		   (terpri) (princ "Note: The premise ") 
		   (write-one-pre pre nil t) 
		   (princ " is used reversely.") (terpri))
	     (setq $premises-set (cons 'false (cdr pres)))
	     (if* (not (is-used-pre pre)) then (mark-used-pre pre))
	     (return t)))
	finally (progn (setq $premises-set pres) (return nil))))

(defun reverse-premise (term)
  ; term is of form (= term1 term2)
  ; return (term2 . term1) if term2 is variable.
  (if* (variablep (second-arg term))
      then (cons (second-arg term) (first-arg term))))

(defun premises-are-true (pres)
  ; return t iff all premises in "pres" are true.
  (sloop for pre in (cdr pres) always (one-premise-is-true pre)))

(defun one-premise-is-true (pre &aux first second)
  ; simplify pre using rules and premsies, put the reduced result 
  ; at the end of $premises-set.
;  (if* (variablep (car pre))
;      then t
;      else)
      (setq first (norm-ctx (first pre))
	    second (second pre))
      (if* (equal first (car pre)) then nil
	   elseif (truep second) then (truep first)
	   else (equal (norm-ctx second) first)))

(defun nofalse-premises (pres &optional sigma)
  ; If one of premises in "pres" is false then return "false".
  ; Otherwise, return all premises in "pres" that is not equal to true.
  (if* (eq $induc 'c) then
      (cons '*&* (sloop for pre in (cdr pres) 
		      collect (flat-term (applysubst sigma pre))))
      else
      (sloop with result 
	    for pre in (cdr pres) do
		(setq pre (norm-one-pre (flat-term (applysubst sigma pre))))
		(if* pre then
		    (caseq (op-of pre)
		      (false (return pre))
		      (*&* (sloop for xa in (args-of pre) do (push xa result)))
		      (t (push pre result))))
	    finally (return (if* result (make-term '*&* result))))))

;; Functions to make new premises.

(defun make-pre-ass (ass info)
  ; "ass" is a predicate term. Make it as a standard premises.
  (if* ass then
      (case (op-of ass)				
	(true nil)
	(= (make-pre-eqn (args-of ass) info))
	(eq (if (cdddr ass) 
		(make-pre ass nil info)
	      (make-pre-eqn (commu-exchange (args-of ass)) info)))
	(xor (make-pre-xor-args (args-of ass) info))
	(and (cons '*&* (sloop for arg in (args-of ass) 
			      collect (make-pre arg nil info))))
	(t (make-pre ass nil info)))))

(defun remake-premises (ctx)
  (if* (eq (car ctx) '*&*) then
      (cons '*&* (sloop for xa in (cdr ctx) 
		      collect (if* (truep (cadr xa)) 
				  then (make-pre-ass (car xa) (cddr xa))
				  else xa)))
      else ctx))

(defun make-pre-xor-args (args info)
  (sloop with big = (car args)
	for arg in (cdr args) 
	if (pseudo-term-ordering big arg) 
	do (setq big arg)
	finally (return (make-pre big (negate-xor-args (remq big args 1)) info))))

(defun separate-xor-args (rhs &aux lhs)
  ; Check if "rhs" is in form of "((t1 and t2) t1 t2)". 
  ; If it is, return ((t1 (false)) (t2 (false))), where t1, t2 are terms.
  ; Check if "rhs" is in form of "((t1 and t2) t1)". 
  ; If it is, return ((t1 (true)) (t2 (false))), where t1, t2 are terms.
  ; Otherwise, pick out the biggest of "rhs", say "lhs", then
  ; return ((lhs "rhs - lhs")).
  (setq lhs (car rhs))
  (sloop for arg in (cdr rhs) 
	if (pseudo-term-ordering lhs arg)
	do (setq lhs arg))
  (setq rhs (negate-xor-args (remq lhs rhs 1)))
  ;; rhs now is a term.

;(mark lhs "LHS")
;(mark rhs "RHS")

  (if* (and (nonvarp lhs) (eq (op-of lhs) 'and) 
	   (null (cdddr rhs)) (null (cdddr lhs)))
      then (if* (equal (args-of lhs) (args-of rhs))
	       then (sloop for arg in (args-of rhs) collect (cons arg $false-term))
	       elseif (and (eq (op-of rhs) 'xor)
			   (truep (first-arg rhs))
			   (member0 (second-arg rhs) (args-of lhs)))
	       then (list (cons (second-arg rhs) nil)
			  (cons (if* (equal (second-arg rhs) (second-arg lhs))
				    (first-arg lhs) (second-arg lhs))
				$false-term))
	       else (ncons (cons lhs rhs)))
      else (ncons (cons lhs rhs))))

(defun make-pre-eqn (eqn info)
  (when (and eqn (nequal (car eqn) (cadr eqn)))
	(make-better-pre (car eqn) (cadr eqn) info)))

;;; Some operations on premises.

(defun negate-premises (vars pres &optional info &aux news) 
  ; return a list of negations of premise if that premise is not leading by a 
  ; variable and has variables in vars.
  (sloop for pre in (cdr pres)
	if (and (nonvarp (car pre)) (have-common vars (pre-vars pre))) do
	(setq pre (negate-one-pre pre info))
	(if (eq (car pre) '*&*)
	    (setq news (append (cdr pre) news))
	  (push pre news)))
  (nreverse news))

(defun negate-one-pre (pre &optional info) 
   ; negate-one-pre: return a negation of pre, still as a premise.
   (if (null info) (setq info (cddr pre)))
   (if* (truep (car pre)) then 
	(if (falsep (cadr pre)) 
	    nil
	  (make-pre (ba-simp-not (cadr pre)) nil info))
	elseif (truep (cadr pre)) then 
	(if (equal (car pre) $false-term)
	    nil 
	  (make-pre (car pre) $false-term info))
       elseif (variablep (car pre)) 
       then (make-pre (list '= (cadr pre) (car pre)) $false-term info)
       elseif (falsep (cadr pre))
       then (make-pre-ass (car pre) info)
       else (make-pre (car pre) (ba-simp-not (cadr pre)) info)))

(defun mark-used-pre (pre) (rplacd (cdr pre) (cons 'used (cddr pre))))

(defun get-pres-ops (pres)
  ; return the ops in pres.
  (sloop for pre in pres 
	nconc (sloop for op in (op-list (car pre)) 
		    if (not (memq op $bool-ops)) collect op)))

(defun pre-vars (pre) 
  ; Return all vars of pre.
  (rem-dups (nconc (all-vars (car pre)) (if* (cadr pre) then (all-vars (cadr pre))))))

(defun pre-ops (pre) 
  ; Return all ops of pre.
  (rem-dups (nconc (all-ops (car pre)) (all-ops (cadr pre)))))

(defun super-itself-pre (pre)
  (let ((lhs (get-pre-lhs pre)) (rhs (get-pre-rhs pre)))
    (if* (and (nonvarp lhs) (eq (op-of lhs) 'and))
	(sloop for y1 in (args-of pre)
	      collect (list (list 'and y1 lhs) (list 'and y1 rhs))))))

(defun merge-premises (condi1 condi2)
  (if* (null condi1) then condi2
   elseif (null condi2) then condi1
   else (append condi1 (cdr condi2))))

(defun more-vars-premise (vars pres)
  ; return the first premise in "pres" that covers properly vars.
  (sloop with big 
	for pre in pres 
	as prevars = (pre-vars pre)
	if (and (is-subset vars prevars) (not (is-subset prevars vars)))
	do (if* (or (null big) 
		   (lrpo (car pre) (car big)))
	       then (setq big pre))
	finally (return big)))

(defun pres-size (pres)
  (apply '+ (sloop for pre in (cdr pres) 
		    collect (+ (size (car pre)) (size (cadr pre))))))

(defun is-eq-false-pre (pre)
  ; return t iff pre is in form of ((= term1 term2) (false)).
  (and (nonvarp (cadr pre)) (falsep (cadr pre)) (eq (caar pre) '=)))

(defun is-eq-true-pre (pre)
  ; return t iff pre is in form of ((= term1 term2) nil).
  (and (null (cadr pre)) (eq (caar pre) '=)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; from premnorm.lsp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;  Functions to use premises to simplify other terms

(defun normalize-by-premises (term)
;  (setq term (subst-var-premises term))
  (norm-by-premises term (cdr $premises-set)))

(defun norm-by-premises (term rules)
  (sloop with tmp1 = term 
	if (setq tmp1 (reduce-by-premises term rules))
	do (setq term tmp1)
	else return term))

(defun subst-var-premises (term)
  (if* $var-premises
      (flat-term (applysubst $var-premises term)) 
    term))

(defun reduce-by-premises-at-root (term rules)
  ; return the reduced term if rules xan reduce term.
  ; Otherwise, return nil.
  (sloop with nterm for rule in rules 
        if (setq nterm (reduce-by-premise-at-root (get-pre-lhs rule) 
						  (get-pre-rhs rule) term))
        return (progn (if* (not (is-used-pre rule)) 
			  then (mark-used-pre rule))
		      (cycle-check nterm)
		      nterm)
	finally (return nil)))

(defun reduce-by-premise-at-root (lhs rhs term)
  (if* (equal lhs term) then rhs
    elseif (or (variablep term) (variablep lhs)) then nil
    elseif (and (same-op lhs term) (ac-root lhs) (is-sublist lhs term))
    then (make-flat (make-term (op-of term)
			       (cons rhs (list-diff term lhs))))))	

(defun reduce-by-premises (term pres)
  ; reduce term once by pres, where pres are a bunch of premises.
  ; return the reudced term if term is reducible. Otherwise, nil.
  (sloop with newterm for rule in pres 
        if (and (nonvarp (first rule))
		(setq newterm (reduce-by-premise-at-root 
				(get-pre-lhs rule) 
				(get-pre-rhs rule) term)))
	  return (progn (if* (not (is-used-pre rule)) 
			    then (mark-used-pre rule))
			(cycle-check newterm)
			newterm)
	finally (return (reduce-args-by-premises term pres))))

(defun reduce-args-by-premises (term pres)
  ; reduce the arguments of term once by pres, where pres are a bunch of premises.
  ; return the reudced term if term is reducible. Otherwise, nil.
  (cond ((variablep term) nil)
	((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (reduce-by-premises xa pres)))
	   return (flat-term (rplnthsubt-in-by i term xa))
	   finally (return nil)))))

(defun subst-premises (subst pres)
  ; apply "subst" on each premises in "pres".
  (if* (and pres (cdr pres)) then
      (cons '*&* (sloop for pre in (cdr pres) 
		      collect (make-pre (flat-term (applysubst subst (car pre)))
					(flat-term (applysubst subst (cadr pre))))))))


