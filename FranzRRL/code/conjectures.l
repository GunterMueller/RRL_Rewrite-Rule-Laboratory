;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.
#-lispm (include datamacs.l)

(declare (special $induc-terms))
(setq $try t $first-induc-op nil)

; The data structure of pattern is: <lhs ctx rec-calls>

(defun make-conjectures (eqn num &aux vars p-term conjs hypo)
  ; eqn is the equation to be proven.
  ; return a list of conjectures.
  (if (setq conjs (choose-best-schemes eqn (if (null num) $first-induc-op))) then
      (setq vars (car conjs)
	    p-term (make-term 'P vars))
      (terpri) (princ "Let ") (write-term p-term)
      (princ " be") (write-seq-num num) (write-f-eqn eqn nil t) (terpri)
      (princ "The induction will be done on ")
      (write-variable (car vars) nil)
      (loop for xa in (cdr vars) do (princ ", ") (write-variable xa nil))
      (princ " in ")
      (loop for xa in $induc-terms do (write-term-simple xa) (princ ", "))
      (if (null num) (setq $first-induc-op (op-of (car $induc-terms))))
      (princ "and will follow the scheme: ") (terpri)
      (loop for n from 1 for sch in (cdr conjs) do
	(princ "   ") 
	(write-seq-num (append1 num n))
	(setq hypo (car sch))
	(write-term (make-term 'P (cadr sch)))
	(if (cddr sch) then 
	    (setq p-term (make-term '&& (loop for xa in (cddr sch)
					      collect (make-pre (make-term 'P xa) nil)))
		  hypo (merge-premises hypo p-term)))
	(if hypo then (princ " if ") (write-premises (cdr hypo)))
	(terpri))
      conjs))

(defun form-conjectures (terms)
  ; Return a cons of (var1 ... vark) and
  ;           ((term1, ..., termk) condition (term1, ..., termk)...)s)
  (if terms then
      (setq $induc-terms terms)
      (loop with first = (form-conjecture-single (car terms))
	    for term in (cdr terms) do
	        (setq first (add-conjectures term first))
	    finally (return first))))

(defun form-conjecture-single (term &aux cover l1)
  ; make conjectures from the definitions of the root of term.
  (setq	cover (cdr (cover-of (op-of term)))
	l1 (compatible-patterns term (cdr cover))
	l1 (loop for pat in l1 
		 collect (one-conjecture (first cover) (args-of term) pat)))
  (remove-dup-vars (get-scheme-vars term) l1))

(defun compatible-patterns (term patterns)
  ; return a list of patterns that are compatible with "term".
  ; A pattern is compatible with "term" if for each argument y of "term",
  ; either y is a variable, or the correspoding argument in the pattern 
  ; subsums y.
  (loop with sigma 
	for pt in patterns 
	as pat = (rename-pattern pt)
	if (or (and (setq sigma (applies (car pat) term))
				 (setq pat (applysubst sigma pat)))
	       (loop for xa in (args-of term)
		     for xb in (args-of (car pat))
		     always (or (and (setq sigma (applies xb xa))
				     (setq pat (applysubst sigma pat)))
				(variablep xa))))
	  collect pat))

(defun one-conjecture (mode args pat &aux lhs condi conjs)
  ; return (premises lhs . hypotheses), an internal representation
  ; of a conjecture, where lhs is a tuple of terms reserved for each
  ; inductive variables; premises is the condition in the definition
  ; and hypotheses are a list of tuples of terms, of which the terms
  ; in each tuple are reserved for each inductive variables.
  (setq mode (loop for m in mode
		   for arg in args 
		   collect (and m (variablep arg)))
	; Now a "t" in mode denotes a correspoding inductive variable position.
	lhs (loop for arg in (args-of (first pat))	
		  for mod in mode if mod collect arg) 
	condi (second pat) 
	conjs (if (loop for xa in lhs thereis (listp xa)) then
		  (loop for term in (cddr pat) 
			collect (loop for arg in (args-of term)
				      for mod in mode 
				      if mod collect arg))))
  (cons condi (cons lhs conjs)))

(defun remove-dup-vars (vars conjs &aux n1 n2)
  ; If a variable appears in "vars" more than once, then remove one of them
  ; and check if the inductive patterns are compatible.
  (if (setq n2 (has-nonlinear-vars vars)) then
      (setq n1 (car n2) 
	    n2 (cdr n2)
	    vars (delq (nth n1 vars) vars 1)
	    conjs (loop for conj in conjs 
			if (setq conj (rem-dup-vars conj n1 n2))
			  collect conj))
      (remove-dup-vars vars conjs)
      else (cons vars conjs)))

(defun has-nonlinear-vars (vars)
  ; return the two positions of a single variable if that variable
  ; occurs more than once in vars.
  (loop with res for n1 from 0 for va on vars 
        if (setq res (loop for n2 from (add1 n1) 
			   for vb in (cdr va) 
			   if (eq vb (car va))
			   return (cons n1 n2)
			   finally (return nil)))
	 return res
      finally (return nil)))

(defun rem-dup-vars (conj n1 n2 &aux condi t1 t2 sigma)
  (setq condi (first conj))
  (loop with result for tup in (cdr conj) do
    (setq t1 (nth n1 tup)
	  t2 (nth n2 tup))
    (if (setq sigma (applies t1 t2))
	then (setq condi (applysubst sigma condi)
		   tup (delq t1 tup 1))
	     (push tup result)
	elseif (setq sigma (applies t2 t1))
	then (setq condi (applysubst sigma condi)
		   tup (delq t2 tup 1))
	     (push tup result)
	else (return nil))
    finally (return (cons condi (reverse result)))))

(defun add-conjectures (term conjs) 
  (let (result posi stock1 stock2 newconjs newvars vars tuple)
    ; conjs is (vars . list-of-<condition, tuples>)
    ; return the same data structure as conjs.
    (setq newconjs (form-conjecture-single term)
	  newvars (set-diff (car newconjs) (car conjs))
	  vars (append (car conjs) newvars))
    (loop for conj in (cdr conjs) do
      (if (cddr conj)
	  then (setq stock1 conj)
	  else (push (list (car conj) (append (cadr conj) newvars)) result)))
    
    (setq posi (loop for n from 0 for va in (car newconjs) collect (cons va n)))
    (loop for conj in (cdr newconjs) do
      (if (cddr conj)
	  then (setq stock2 conj)
	  else (setq tuple (add-old-vars vars posi (cadr conj)))
	       (push (list (first conj) tuple) result)))
    (if (setq posi (merge-two-conjs stock1 stock2 vars posi))
	then (cons vars (remove-subsumed (cons posi result)))
	else conjs)))

(defun merge-two-conjs (stock1 stock2 vars posi	&aux condi tuple)
  ; merge two induction schemes with hypotheses into one.
  (setq condi (merge-premises (car stock1) (car stock2))
	tuple (merge-two-tuples (cadr stock1) (cadr stock2) vars posi))
  (if tuple then 
      (setq stock1 (loop for xa in (cddr stock1) append
			 (loop for xb in (cddr stock2) 
			       if (setq xa (merge-two-tuples xa xb vars posi))
				 collect xa)))
      (cons condi (cons tuple (rem-dups stock1)))))

(defun merge-two-tuples (tu1 tu2 vars posi &aux t1 t2)
 (loop with vn2 for n1 from 0 
       for va in vars collect
       (if (null (setq vn2 (assoc va posi)))
	   then (nth n1 tu1)
	   elseif (null (setq t1 (nth n1 tu1)))
	   then (setq t2 (nth (cdr vn2) tu2))
	   elseif (applies t2 t1)
	   then t1
	   else (return nil))))

(defun a-conjectures (conjs)
  ; conjs is a list of (number . <condition, term, a-list-of-terms>s).
  ; Return (number number . <condition, term, a-list-of-terms>s).
  (loop with first = (car conjs)
        for rest in (cdr conjs) 
	do (setq first rest)
	finally (return (cons (length conjs) first))))

(defun rename-pattern (pat)
  (if (car pat)
      then (cdr (newvarsin (cons 'xxx pat)))
      else (newvarsin pat)))

(defun remove-subsumed (conjs)
  ; remove conjectures in "conjs" that is subsumed by others.
  (loop with result for cs on conjs 
	as xa = (car cs) do
	  (if (not (loop for xb in (cdr cs) 
		      thereis (subsumed-tuple xa xb)))
	      then (push xa result))
	  finally (return result)))

(defun subsumed-tuple (con1 con2)
  ; return t iff both "con1" and "con2" do not have hypotheses and
  ; "con1" is an instance of "con2".
  (and (null (cddr con1)) 
       (null (cddr con2))
       (applies (cons 'x (second con2)) (cons 'x (second con1)))))
