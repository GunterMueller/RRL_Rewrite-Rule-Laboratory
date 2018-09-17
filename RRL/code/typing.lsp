;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")



#+franz
(declare (special $var-type-list $deep-condi))

(setq $var-type-list nil)
(setq $strong-type t) ; strong type checking.

(defun well-typed (term)
  ; Return T iff "term" is well-typed.
  ; A term "t" is well-typed if
  ;    1. "t" is a variable;
  ; or 2. "t" is form of f(t1, t2, ..., tn), and
  ;       t1, t2, .., tn are well-typed, and
  ;       f is signature of [type1, type2, ..., typen -> type]
  ;	  and typei is included in the type of ti, for i in [1..n].
  (if* (null term) then t
      elseif (variablep term) then t 
      else (setq $var-type-list nil)
      (well-typed2 term)))

(defun well-typed2 (term)
  (if* (memq (op-of term) '(= eq))
   then (sloop with ty = (get-term-type (first-arg term))
	      for xa in (args-of term) 
	      always (if* (variablep xa) 
			 then (if* $strong-type then (well-typed-var xa ty) else t)
			 else (and (type-cohere ty (get-term-type xa)) (well-typed2 xa))))
   elseif (is-bool-op (op-of term)) 
   then (sloop for arg in (args-of term) always (well-typed arg))
   elseif (is-type-predicate (op-of term)) 
   then (sloop for arg in (args-of term) always (well-typed arg))
   elseif (get-arity2 (op-of term))
   then
   (sloop for ty in (get-codomain-types (op-of term)) 
	 for ar in (args-of term)
	 always (if* (variablep ar) then
		    (if* $strong-type then (well-typed-var ar ty) else t)
		    else (and (type-cohere ty 
					   (get-domain-type (op-of ar)))
			      (well-typed2 ar))))
   else (sloop for ar in (args-of term) 
	      always (or (variablep ar) (well-typed2 ar)))))

(defun well-typed3 (term)
  (if* (get-arity2 (op-of term)) then
      (sloop for ty in (get-codomain-types (op-of term)) 
	    for ar in (args-of term)
	    always (if* (variablep ar) 
		       then (well-typed-var ar ty) 
		       else (type-cohere ty (get-domain-type (op-of ar)))))
      else t))


(defun complete-well-typed (term)
  ; Return T iff "term" is well-typed.
  ; A term "t" is well-typed if
  ;    1. "t" is a variable;
  ; or 2. "t" is form of f(t1, t2, ..., tn), and
  ;       t1, t2, .., tn are well-typed, and
  ;       f is signature of [type1, type2, ..., typen -> type]
  ;	  and typei is included in the type of ti, for i in [1..n].
  (if* (null term) then t
      elseif (variablep term) then t 
      elseif (memq (op-of term) '(= eq))
      then (sloop with ty = (get-term-type (first-arg term))
		 for xa in (args-of term) 
		 always (if* (variablep xa) 
			    then (if* $strong-type then (well-typed-var xa ty) else t)
			    else (and (type-cohere ty (get-term-type xa)) 
				      (complete-well-typed xa))))
      elseif (is-bool-op (op-of term)) 
      then (sloop for arg in (args-of term) always (complete-well-typed arg))
      elseif (get-arity2 (op-of term))
      then
      (sloop for ty in (get-codomain-types (op-of term)) 
	    for ar in (args-of term)
	    always (if* (variablep ar) then
		       (if* $strong-type then (well-typed-var ar ty) else t)
		       else (and (type-cohere ty 
					      (get-domain-type (op-of ar)))
				 (complete-well-typed ar))))
      else (sloop for ar in (args-of term) 
		 always (or (variablep ar) (complete-well-typed ar)))))

(defun get-term-type (term)
  (if* (variablep term) then 'univ else (get-domain-type (op-of term))))

(defun well-typed-var (var type &aux var-type)
  (if* (eq type 'univ) then t 
   elseif (setq var-type (assoc var $var-type-list))
   then (if* (memq (cdr var-type) (assoc type $type-rela)) 
	    then (if* (eq $deep-condi $over-rewrite) then (rplacd var-type type)) t 
	    elseif (memq type (assoc (cdr var-type) $type-rela))
	    then t)
   elseif (eq $deep-condi $over-rewrite) 
   then (push (cons var type) $var-type-list)
   else t))

(defun get-domain-type (op) 
  ; The default types are:
  ;    1. variables are type of "univ";
  ;    2. numbers are type of "num";
  ;    3. the predicates are type of "bool".
  ;    3. If no type is given to an operator, then "univ".
  (cond ; ((numberp op) (if* $num-type then (car $num-type) else 'univ))
	((get-arity2 op) (car (get-arity2 op)))
	((and (not (numberp op)) (predicatep op)) 'bool)
	(t 'univ)))

(defun get-codomain-types (op) 
  ; If no type is given, then suppose "op" has 
  ;      (univ, univ, ..., univ).
  (cond ((numberp op) nil)
	((get-arity2 op) (cdr (get-arity2 op)))
	(t (sloop for i from 1 to (get-arity op) collect 'univ))))

(defun ext-type-relation ()
  ; Sets the type relation between two types given by the user.
  ; $type_rela is updated.
  (if* (is-empty-line $in-port) then
      (princ "Type type names in including order.") (terpri)
      (princ "  (eg. 'type1 type2 type3' to set type1 C type2 C type2 ) ")
      (terpri) (princ "--> "))
  (let ((ty1 (read-atom 'noend)) tys2)
    (setq tys2 (progn (if* (is-empty-line $in-port) then
		        (princ (uconcat ty1 " is included in type name ? ")))
	              (read-args $in-port)))
    (if* (sloop for ty2 in (cons ty1 tys2) always 
	     (if* (is-exist-type-name ty2) then t else
	       (princ (uconcat ty2 ": unknown type name, relation not set."))
	       (terpri) nil))
 	then (sloop for ty2 in tys2 do
	       (add-sugg-type ty1 ty2)
	       (princ (uconcat "Type relation, " ty1 " C " ty2 ", is added."))
	       (terpri)
               (setq ty1 ty2)))))

(defun add-sugg-type (ty1 ty2)
  ; Adds the relation ty1 C ty2 and makes sure the global
  ; varaible $type-rela is updated correctly.
  (cond ((null $type-rela) 
         (setq $type-rela (ncons (list ty1 ty2))))
        ((assoc ty1 $type-rela) (add-sugg-type1 ty1 ty2))
	(t (nconc $type-rela (ncons (ncons ty1)))
	   (add-sugg-type1 ty1 ty2))))

(defun add-sugg-type1 (ty1 ty2)
  ; Called by ADD-SUGG-TYPE.
  (sloop for xa in $type-rela do
     (if* (member0 ty1 xa) then 
	(add-at-end xa ty2)
	(sloop for o2 in (assoc ty2 $type-rela) do (add-at-end xa o2)))))

(defun type-cohere (ty1 ty2)
  ; Checks if TY1 is included in TY2 or vice verca.
  (or (eq ty1 ty2) (is-subtype ty1 ty2) (is-subtype ty2 ty1)))

(defun is-subtype (ty1 ty2)
  (or (eq ty2 'univ) (memq ty1 (assoc ty2 $type-rela))))

(defun get-subtypes (ty1)
  (if* (eq ty1 'univ) 
     then (sloop for xa in $type-rela collect (car xa))
     else (cdr (assoc ty1 $type-rela))))

(defun display-type-arity (ops &optional port)
  (setq ops (sloop for op in ops 
		  if (not (or (memq op '(eq typed))
			      (is-bool-op op)
			      (assoc op $type-rela)))
		    collect op))
  (if* ops then
      (terpri port)
      (princ "The arities of the operators are:" port) (terpri port)
      (display-arity2 ops port)
      (terpri port)))

(defun display-arity2 (ops &optional port)
   (sloop for op in ops do (display-one-arity2 op port)))

(defun display-one-arity2 (op &optional port &aux types)
  (if* (get-arity2 op) then
    (princ (uconcat "      [" op " :") port)
    (if* (setq types (get-codomain-types op)) then
      (princ " " port) (princ (car types) port)
      (sloop for ty in (cdr types) do (princ ", " port) (princ ty port)))
    (princ (uconcat " -> " (get-domain-type op)) port)
    (princ " ]" port)
    (terpri port)))

(defun is-exist-type-name (ty2)
 ; return t iff "ty2" is a valid type name.
 ; num, list and univ are pre-defined type names.
 (or (memq ty2 '(num list univ)) (assoc ty2 $type-rela)))

(defun well-typed-eqn (eqn)
  (and (well-typed (lhs eqn)) (well-typed (rhs eqn)) 
       (if* (ctx eqn) then
	   (if* (is-premise-set (ctx eqn)) 
	       then (sloop for xa in (cdr (ctx eqn)) 
			      always (well-typed (car xa)))
	       else (well-typed (ctx eqn)))
	   else t)))
