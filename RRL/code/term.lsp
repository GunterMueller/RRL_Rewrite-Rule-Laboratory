;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

;  This file contains various functions for representing terms and
;  useful operations on terms. The basic data-structure for a term is
;  just a list of 2 elements of the form (operator arguments) where
;  arguments may themselves be terms. We distinguish between variables
;  and non-variable terms as follows. A variable is an atom whose print-name
;  starts with u-z . A non-variable term, even of 0-arity is a list.
;
;  Examples:
;
;    Variable terms:            x , y , z , x2 , z6
;
;    Non-variable terms:        (* x y)
;                               (* (+ x2 y3) (f u2))
;                               (g (e) x) [represents g(e,x)
;                                          where e is constant]
;
;  Below we define various functions on terms:

;       op-list:        Returns the operator set of a term.
;       var-list:       Returns the variable set of a term.
;       var1-list:      Returns all variables (with duplicate) in a term.
;       all-vars:       Returns all variables (with duplicate) in a term.
;       size:           number of symbols in a term.

;       subtat:         subterm at specified position in a term.
;       rplnthsubt-in-by:
;                       replaces nth top-level subterm of a term by a
;                       specified term.
;       rplat-in-by:    replaces subterm at a given position in a term
;                       by a specified term.
;       rpl-by-terms:   replaces subterm at a given position in a term
;  			by a list of terms.
;       newvarsin:      replaces variables in a term by new symbols.
;       repvarsin:      used by newvarsin.
;       is-subt:        Returns t if one term is a subterm of the other.

;       depth:          Returns the depth of a term:
;			   depth(t) = 1 if t is a variable or a constant;
;				    = 1 + max(depth(ti)) if t = f(t1, ..., tn)
;       is-primitive:   Returns t iff a term does not contain any 
;			non-constructor operators.
;       is-limited:     Returns t iff a term contains only operators in
;			a limited set.
;       subs-are-primitive: 
;			Returns t iff the subterms of a term are primitive.
;	is-linear:	Returns t iff each variable in a term has only one
;			occurrence.
;	non-linear-vars: Returns all variables having more than once 
;			occurrence in a term.
;       crplnthsubt:    replaces nth top-level subterm by each  term in CLIST.

;  Returns a list of the operators in TERM.
(defun op-list (term) (rem-dups (all-ops term)))

;  Returns a list of variables in TERM.
(defun var-list (term) (rem-dups (all-vars term)))

(defun all-ops (term)
  ; Returns a list of all variables (with duplicates) in TERM.
  (cond ((null term) nil)
        ((variablep term) nil)
	(t (cons (op-of term) (mapcan 'all-ops (args-of term))))))

(defun all-vars (term)
  ; Returns a list of all variables (with duplicates) in TERM.
  (cond ((null term) nil)
        ((variablep term) (list term))
	(t (mapcan 'all-vars (args-of term)))))

(defun is-ground (term)
  ; Returns a list of all variables (with duplicates) in TERM.
  (cond ((null term) t)
        ((variablep term) nil)
	(t (sloop for xa in (args-of term) always (is-ground xa)))))

(defun var1-list (term) (all-vars term))

(defun size (term)
  ; Returns the number of symbols in TERM (the size of TERM).
  (cond ((null term) 0)
	((variablep term) 1)
	((or (memq (op-of term) $ac) (and $polynomial (eq (op-of term) '*)))
	 (+ -1 (length (args-of term)) (apply '+ (mapcar 'size (args-of term)))))
	(t (1+ (apply '+ (mapcar 'size (args-of term)))))))

(defun w-size (term &aux l1)
  ; Returns the weighted size of TERM.
  (cond ((null term) 0)
	((variablep term) 1)
	(t (+ (if* (setq l1 (assoc (op-of term) $f-weights)) (cdr l1) 1)
	      (apply '+ (mapcar 'w-size (args-of term)))))))

(defun term-size-order (t1 t2) (not (greaterp (size t1) (size t2))))

(defun make-new-variable (&optional var)
   (setq var 
	(copysymbol (if* var var 'z) nil))
   (set var (setq $symbnum (1+ $symbnum)))
   var)

(defun free-vars (term)
   ; Figure out what the free variables of a term are.
   (cond ((variablep term) (ncons term))
	 ((memq (op-of term) '(all exist))
	  (delete (first-arg term) (free-vars (second-arg term))))
         (t (rem-dups
	     (sloop for this in (args-of term) nconc (free-vars this))))))

(defun subtat (pos term)
  ; Returns a subterm at position POS of term TERM.
  ; POS is a list of integers.
  ; Example: let T = F(G(X,Y), X)  (subtat (1 2) T) returns Y
  (if* pos then (sloop for i in pos do (setq term (nthsubt i term))))
  term)

(defun rplnthsubt-in-by (n term t1)
  ;  Replaces then Nth top-level subterm of TERM by T1.
  (make-term (op-of term)
	     (sloop for xa in (args-of term) as i from 1 collect
		   (if* (= i n) then t1 else xa))))

(defun rplat-in-by (pos term t1)
  ;  Replaces the subterm at position POS in term TERM by T1.
  (cond ((null pos) t1)
	(t (make-term (op-of term)
		      (sloop for xa in (args-of term) as i from 1 collect
			    (if* (= i (car pos))
				then (rplat-in-by (args-of pos) xa t1)
				else xa))))))
 
(defun rpl-by-terms (pos t1 ts)
  ;  Replaces the subterm at position POS in T1 by the terms in TS.
  (mapcar 'flat-term-func (rpl-by-terms2 pos t1 ts)))

(defun rpl-by-terms2 (pos t1 ts)
  ;  Replaces the subterm at position POS in T1 by the terms in TS.
  (cond ((null pos) ts)
        (t (let (news args1 (args2 (args-of t1)) (n (pop pos)))
	      (setq args1 (sloop for i from 1 to (sub1 n) collect (pop args2))
		    news (rpl-by-terms2 pos (pop args2) ts))
	      (sloop for xa in news 
		    collect (make-term (op-of t1) (append args1 (ncons xa) args2)))))))

(defun newvarsin (term &optional vars)
  ; Replaces all variables in TERM by new symbols with same print name.
  (setq v_binds 
     (sloop for var in (sort (or vars (var-list term)) 'order-vars) collect
	  (cons var (make-new-variable var))))
  (if* v_binds (applysubst v_binds term) term))

(defun order-vars (var1 var2)
  ;  Returns t if var1 is less or equal to var2.
  (cond ((alphalessp var1 var2) t)
	((alphalessp var2 var1) nil)
	(t
	 ; at this point, s1 and s2 have the same print name.
	 (if* (and (boundp var1) (boundp var2))
	     then (lessp (symeval var1) (symeval var2))
	     elseif (boundp var2) then t
	     elseif (boundp var1) then nil
	     else #+franz nil
	          #-franz t))))

(defun repvarsin (term) 
  (if* v_binds (applysubst v_binds term) term))

#+franz
(defun new-vars (vars1 vars2)
  ;  Checking each v1 in VARS1, if v1 is also in vars2, then
  ; replace x by a new variable which is not in VARS1 or in VARS2.
  (let ((vars (append vars1 vars2)))
     (initsym 'x) (initsym 'y) (initsym 'z)
     (sloop for v1 in vars1 if (member0 v1 vars2) 
		collect (cons v1 (new-var vars)))))

#+franz
(defun new-var (vars)
  ;  Return a new variable name which is not in VARS1 or VARS2.
  (prog (v1)
     (sloop while (setq v1 (newsym 'x)) do
        (if* (> (getchar v1 2) 9) then (return (setq v1 nil))
	 elseif (not (member0 v1 vars)) then (return)))
     (if* v1 then (return v1))
     (sloop while (setq v1 (newsym 'y)) do
        (if* (> (getchar v1 2) 9) then (return (setq v1 nil))
	 elseif (not (member0 v1 vars)) then (return)))
     (if* v1 then (return v1))
     (sloop while (setq v1 (newsym 'z)) do
	 (if* (not (member0 v1 vars)) then (return)))
     (return v1)))

(defun is-subt (t1 t2)
  ;  Returns t if T1 is a subterm of T2; otherwise, nil.
  (if* (equal t1 t2) then t
    else (sloop for arg in (args-of t2) thereis (is-subterm t1 arg))))
       
(defun is-subterm (t1 t2)
  ;  Returns t if T1 is a subterm of T2; otherwise, nil.
  (if* (equal t1 t2) then t
    elseif (or (variablep t2) (null (args-of t2))) then nil
    elseif (and (nonvarp t1) (same-op t1 t2) (ac-c-root t1) (is-subset t1 t2)) then t
    else (sloop for arg in (args-of t2) thereis (is-subterm t1 arg))))

(defun occurs-in (var term)
  (if* (eq var term) t
    (if* (variablep term) nil
	(sloop for arg in (args-of term) thereis (occurs-in var arg)))))

(defun is-sub-nonvar-term (t1 t2)
  ; return T iff t1 is a subterm of t2 without considering variables.
  (if* (variablep t2) then nil
      elseif (variablep t1) then t
      elseif (same-op t1 t2)
      then (if* (args-of t2) then
	       (sloop for arg1 in (set-diff (args-of t1) (args-of t2))
		     always (sloop for arg2 in (set-diff (args-of t2) (args-of t1))
				  thereis (is-sub-nonvar-term arg1 arg2))))
      else (sloop for arg2 in (args-of t2) thereis (sub-or-eq-term t1 arg2))))

(defun sub-or-eq-term (t1 t2)
  ; return T iff t1 is a subterm of t2 or equal to t2 without considering variables.
  (if* (variablep t1) then t
      elseif (variablep t2) then nil
      elseif (same-op t1 t2)
      then (sloop for arg1 in (args-of t1) 
		 always (sloop for arg2 in (args-of t2) 
			      thereis (sub-or-eq-term arg1 arg2)))
      else (sloop for arg2 in (args-of t2)
		     thereis (sub-or-eq-term t1 arg2))))

(defun depth (t1)
  ;  Returns the depth of "t1"
  (cond ((variablep t1) 0)
	((null (args-of t1)) 1)
        (t (1+ (apply 'max (mapcar 'depth (args-of t1)))))))

(defun rename-vars (t1) 
   (cond ((variablep t1) (make-new-variable t1))
	 (t (make-term (op-of t1) (mapcar 'rename-vars (args-of t1))))))

(defun rename-var (t1 &optional vars)
   ; Suppose T1 is linear. Rename all variable names of T1 by
   ;		 {x1, x2, ..., xn}. 
   (initsym 'x)
   (rename-var1 t1 'x vars))

(defun rename-var1 (t1 name &optional vars)
   ; Auxillary function of "rename-var".
   (cond ((variablep t1) (sloop for xa = (newsym name) then (newsym name) 
			         if (not (member0 xa vars)) return xa))
	 (t (make-term (op-of t1) 
		       (sloop for arg in (args-of t1) 
				collect (rename-var1 arg name vars))))))

(defun rename-vary (t1)
   ; Suppose T1 is linear. Rename all variable names of T1 by
   ;		 {y1, y2, ..., yn}. 
   (initsym 'y)
   (rename-var1 t1 'y))

(defun is-limited (t1 op-set)
  ;  Returns "t" iff "t1" does not contain any non-contructor operator.
  (cond ((variablep t1) t)
        ((not (member0 (op-of t1) op-set)) nil)
        ((null (args-of t1)) t)
        (t (sloop for xa in (args-of t1) always (is-limited xa op-set)))))

(defun is-primitive (t1) (is-limited t1 $constructors))

(defun primitive-subst (subst)
  ; Return t iff subst is a constructor substitution.
  (sloop for xa in subst always (is-primitive (cdr xa))))

(defun subs-are-primitive (t1)
  ;  Returns "t" iff the all subterms of "t1" are primitives.
  (cond ((null (args-of t1)) t)
        (t (sloop for xa in (args-of t1) always (is-primitive xa)))))

(defun is-linear (term)
  ;  returns "t" iff  there is all variables have at least occurrence
  ;         once in "term".
  (null (non-linear-vars term)))

(defun non-linear-vars (term &aux global)
  ;  Returns a list of all variables which have more occurrences
  ;  than once in TERM.
  (sloop for var in (all-vars term) 
	if (query-insert var global) collect var))

(defun pseudo-term-ordering (s1 s2)
  ;  Returns t if S1 is less or equal to S2.
  (cond ((equal s1 s2) nil)
	((or (truep s2) (falsep s2)) nil)
	((or (truep s1) (falsep s1)) t)
	((and (variablep s1) (variablep s2))
	 (cond ((alphalessp s1 s2) t)
	       ((alphalessp s2 s1) nil)
	       (t ; at this point, s1 and s2 have the same print name.
		 (if* (and (boundp s1) (boundp s2))
	             then (lessp (symeval s1) (symeval s2))
		     elseif (boundp s2) then t
		     else nil))))
	((variablep s1) t)
	((variablep s2) nil)
	((lrpo s1 s2) nil)
	((lrpo s2 s1) t)
	((same-op s1 s2)
	 (if* (= (length s1) (length s2)) 
	     then (order-pc-seq (args-of s1) (args-of s2))
	     else (< (length s1) (length s2))))
	(t (operator-ordering (op-of s1) (op-of s2)))))

(defun operator-ordering (s1 s2)
  ;  Returns t if S1 is less or equal to S2.
  (if* (grt-prec s1 s2) then nil
      elseif (grt-prec s2 s1) then t
      elseif (and (numberp s1) (numberp s2)) then (lessp s1 s2)
      elseif (numberp s1) then t
      elseif (numberp s2) then nil
      else (alphalessp s1 s2)))

(defun smaller-size (t1 t2) (lessp (size t1) (size t2)))

(defun literal-num (term)
   (caseq (op-of term)
     ((xor and) (apply '+ (mapcar 'literal-num (args-of term))))
;     (and (length (args-of term)))
     (eq (1- (length (args-of term))))
     (t 1)))

(defun is-constant-term (term) (and (nonvarp term) (null (args-of term)))) 
(defun is-value-term (term) (and (is-limited term $free-constructors) (groundp term)))

(defun groundp (term &optional varlist)
  (cond
    ((variablep term) (member0 term varlist))
    (t (sloop for x in (args-of term) always (groundp x varlist)))))

(defun one-type-var-list (term type)
  ; Returns a list of all variables of type "type" in TERM.
  (cond ((variablep term) (ncons term))
	(t (rem-dups (one-type-all-vars term type)))))

(defun one-type-all-vars (term type)
  ; Returns a list of all variables of type "type" (with duplicates) in TERM.
  (sloop for xa in (get-codomain-types (op-of term))
	for xb in (args-of term) 
	append (if* (nonvarp xb) then (one-type-all-vars xb type)
	        elseif (eq xa type) then (ncons xb))))

(defun type-all-vars (term)
  (sloop for xa in (get-codomain-types (op-of term))
	for xb in (args-of term) 
	nconc (if* (nonvarp xb) then (type-all-vars xb)
			       else (ncons (cons xa xb)))))

(defun type-var-list (term)
  ; Return a list of two lists: one for the vars in term and the other for 
  ; their types.
  (if* (variablep term) then (list '(univ) (ncons term)) 
     elseif (setq term (rem-dups (type-all-vars term)))
     then (split-alist term)))
