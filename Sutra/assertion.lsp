;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "RRL")

; ********WARNING*********
; *****Parental guidance suggested for children under the age of 17*********
; ********WARNING*********

(defun process-ass-simple (ass source)
  (if ass then
      (add-time $norm_time 
                (setq $used-rule-nums nil
                      ass (norm-ctx ass))) ; normalization
      (if $trace-proof then
	  (setq source (append source (rem-dups $used-rule-nums))
		$used-rule-nums nil)) ; put in the numbers of used rules.
      (add-time $ord_time (order-ass ass source))))

(defun process-ass2 (ass source) (process-ass-simple (first-trans ass) source))
(defun process-ass1 (ass source) 
      (process-ass2 (if (eq $more-break 'n)
			then (skolemize ass)
			else (break-ass ass source)) source))

(defun process-ass (ass source &aux l1)
  ; Add a new equation, doing all of the simplifications that we know how 
  ; to do. At first, try to reduce the size of ass. Then try to break ass
  ; to small sub-assertions. then try to skolemize, then boolean ring 
  ; transfomation ...
  (if ass then
      (caseq (op-of ass)
	(true nil)
	(false (refuted-result source))
	(and (loop for x in (args-of ass) do (process-ass x source)))
	((all exist) (process-ass 
		       (skolemize-away-quants ass ass nil) source))
	(equ (if (truep (first-arg ass))
		 then  (process-ass (second-arg ass) source)
		 elseif (truep (second-arg ass))  
		 then (process-ass (first-arg ass) source)
		 elseif (have-common '(all exist) (all-ops ass))
		 then (process-ass `(-> ,(first-arg ass) ,(second-arg ass))
				   source)
	         (process-ass `(-> ,(second-arg ass) ,(first-arg ass))
			      source)
		 else (process-ass1 (make-term 'xor 
					       (cons '(true) (args-of ass)))
				    source)))
	(xor (process-ass1 ass source))
	(or  (if (and (not (eq $more-break 'n)) (greaterp (or-count ass) 3))
		 then (loop for xa in (break-at-or ass) do
			(process-ass xa source))
		 else (process-ass1 ass source)))
	(->  (if (eq (op-of (first-arg ass)) 'or) 
		 then (setq l1 (args-of (first-arg ass)))
		 (loop for xa in l1 do 
		   (process-ass `(-> ,xa ,(second-arg ass)) source))
		 elseif (eq (op-of (second-arg ass)) 'and) 
		 then (setq l1 (args-of (second-arg ass)))
		 (loop for xa in l1 do 
		   (process-ass `(-> ,(first-arg ass) ,xa) source))
		 else (process-ass1 ass source)))
	(not (setq l1 (first-arg ass))
	     (caseq (op-of l1)
	       (false nil)
	       (true (refuted-result source))
	       (not (process-ass (first-arg l1) source))
	       (equ (process-ass `(xor . ,(args-of l1)) source))
	       (xor (process-ass `(equ . ,(args-of l1)) source))
	       ((all exist)
		(process-ass `(not ,(skolemize-away-quants l1 ass t)) source))
	       (or (loop for xa in (args-of l1) do
		     (process-ass `(not ,xa) source)))
	       (-> (process-ass (first-arg l1) source)
		   (process-ass `(not ,(second-arg l1)) source))
	       (t (process-ass1 ass source))))
	(eq (if (= (length ass) 3) 
		then (push (make-eqn (first-arg ass) 
				     (second-arg ass) nil source) $eqn-set) nil
		else (process-ass-simple ass source)))
	(t (process-ass-simple ass source)))))

(defun break-ass (ass source &optional flag &aux l1)
   ; Attempt to break up equations in a more intelligent fashion.
   ; At present, every quantifier is under one of operators or, equ,
   ; ->, xor. Hence, we replace every quantified formula by a new one.
   (if (quantifierp (op-of ass)) then
        (setq l1 ass)
	(loop while (quantifierp (op-of (second-arg l1))) 
	    do (setq l1 (second-arg l1)))
	(rplaca (cddr l1) (break-ass (second-arg l1) source))
        (substvarfor ass source) 
      elseif (eq (op-of ass) 'not) then
	`(not ,(break-ass (first-arg ass) source flag))
      elseif (boolean-opp (op-of ass)) then
	(setq ass (make-term (op-of ass)
	  		     (loop for xa in (args-of ass) collect 
		       		      (break-ass xa source (not flag)))))
        (if (and flag (eq $more-break 'm)) 
	     then (substvarfor ass source)
	     else ass)
      else ass))

(defun substvarfor (ass source)
   ; Substitute a variable for ass.
   ; We call process-ass2 to introduce a new constraining equation,
   ; and we return a value that should be used for the variable.
   ; If flag is true, then just return ass.
   (let ((func (gennewsym $func-name)) (args (free-vars ass)))
        (if $set_pred (set-predicate func))
	(set-arity func (length args))

	(if $var-type-list then
	    (set-arity2 func 
			(cons (get-domain-type (op-of ass))
			      (loop with xc for xa in args 
				    collect (if (setq xc (assoc xa $var-type-list))
						then (cdr xc)
						else 'univ)))))
	(terpri) (princ "  Introducing") (display-one-arity2 func)
	(setq func (make-term func args))
	(princ "  ") (write-term func) 
	(princ " stands for ") (write-term ass) (terpri)
        (if (predicatep (op-of ass)) 
	    then (set-predicate (op-of func))
		 (if (quantifierp (op-of ass)) 
		    then (subst-quant-form func ass source)
		    else (process-ass2 `(equ ,func ,ass) source))
	    else (push (make-eqn ass func nil source) $eqn-set))
	func))

(defun or-count (ass)
   ; Count the number of ors on the top level of a ass.
   (if (equal (op-of ass) 'or) 
      then (+ 1 (or-count (first-arg ass)) (or-count (second-arg ass)))
      else 0))

(defun break-at-or (ass)
   ; Substitute a predicate for ass.
   ; We call process-ass to introduce a new constraining equation,
   ; and we return a value that should be used for the variable.
   ; If flag is true, then just return ass.
   (let ((args (flatten 'or (args-of ass))) 
	  func term asses vars)
      (loop while (> (length args) 4) do
            (setq term (pop args)
                  vars (var-list term))	  
            (loop for i from 1 to 2 do
               (setq term (list 'or term (car args))
                     vars (intersection vars (var-list (pop args)))))
	    (setq func (make-term (gennewsym $func-name) vars))
  	    (set-arity (op-of func) (length vars))
	    (push `(equ ,term ,func) asses)
   	    (push-end func args))

      (setq term (pop args))
      (loop for arg in args do (setq term (list 'or term arg)))
      (push term asses)

      (terpri) (princ "Following assertion") (terpri) (princ "    ")
      (write-term ass) (terpri) 
      (setq asses (reverse asses))
      (princ "    is broken into") (terpri)
      (loop for xa in asses do (princ "    ") (write-term xa) (terpri))
      (terpri)
      asses))

(defun trivial-simplify (ass)
  (if (variablep ass) then ass else
   (caseq (op-of ass)
    (equ (if (truep (first-arg ass))
	    then (second-arg ass)
          elseif (truep (second-arg ass))  
	    then (first-arg ass)
	    else ass))
;    (xor (if (truep (first-arg ass))
;	    then `(not ,(second-arg ass))
;          elseif (truep (second-arg ass)) 
;	    then `(not ,(first-arg ass))
;	    else ass))
    (not (if (variablep (first-arg ass)) then ass else
	   (setq ass (first-arg ass))
	   (caseq (op-of ass)
	     (true '(false))
	     (false '(true))
 	     (not (first-arg ass))
	     (equ `(xor . ,(args-of ass)))
	     (xor `(equ . ,(args-of ass)))
	     (t `(not ,ass)))))
    (t ass))))


(defun negate-predicate (pred)
  (if pred then
      (caseq (op-of pred)
	(false '(true))
	(true '(false))
	(xor (negate-xor-args (args-of pred)))
	(t (m-xor-m pred '(true))))
      else '(false)))

(defun negate-xor-args (args)
  (if (member '(true) args) then
      (setq args (remove '(true) args 1))
      (if (null args) then '(false)
	  elseif (cdr args) then (make-term 'xor args) 
	  else (car args))
      else
      (m-xor-p '(true) (cons 'xor args))))
