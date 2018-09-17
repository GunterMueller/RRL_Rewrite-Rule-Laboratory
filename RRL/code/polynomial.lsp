;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")



#+franz
(declare (special $subs $xnx))

(setq $xnx 5)

(defmacro change-mono-sign (num mset)
  `(sloop for xa in ,mset collect (cons (car xa) (- ,num (cdr xa)))))

(defmacro times-cdr (n1 list) 
  `(if* (= ,n1 1)
       ,list
       (sloop for xa in ,list collect (cons (car xa) (times ,n1 (cdr xa))))))

; This file contains functions to implement the polynomial simplifications.
; A polynomial is defined by +, * and 0, where 
;     + is AC;
;     * is associative;
;     0 is the zero of * and the unit of +;
;     + distributes over *;
;     + satisfies the cancellation law.
;   
; * is optionally commutative;
; * has optionally the unit;
; * has optionally the characteristic m: x^m == x;
; + has optionally the characteristic n: nx == 0.
;
; Three main group of functions needed to be done:
; 1. Normalize a polynomial;
; 2. Reduction in built-in associativity of *;
; 3. Superpose a rule with the distributation law;


;;;; First Group of Functions.

(defun poly-simplify (term)
  ; Applies polynomial transform on term.
  ; Works on reductions in a bottom fashion. 
  ; Returns simplified term.
  ; Applies polynomial transform on term. It assumes nothing about
  ; whether it is flattened or not.
  (if* (or (null term) (variablep term)) 
      term
      (caseq (op-of term)
	(+ (simplify-+ (mapcar 'poly-simplify (args-of term))))
	(* (simplify-* (mapcar 'poly-simplify (args-of term))))
	(t (make-term (op-of term) (mapcar 'poly-simplify (args-of term)))))))

(defun simplify-+ (args)
  (sloop with res = '(0)
	for arg in args do
    (setq res
	  (if* (and (nonvarp arg) (eq '+ (op-of arg)))
	      (if* (and (nonvarp res) (eq '+ (op-of res)))
		  (p-+-p res arg)
		  (m-+-p res arg))
	      (if* (and (nonvarp res) (eq '+ (op-of res)))
		  (m-+-p arg res)
		  (m-+-m res arg))))
	finally (return res)))

(defun simplify-* (args)
  (sloop with res = nil for arg in args 
	if (equal arg '(0)) return arg ; We should have this.
	else do
	       (setq res (if* (and (nonvarp arg) (eq '+ (op-of arg))) 
			     (if* (and (nonvarp res) (eq '+ (op-of res)))
				 (p-*-p res arg)
				 (m-*-p res arg))
			     (if* (and (nonvarp res) (eq '+ (op-of res)))
				 (if* (memq '* $ac) (m-*-p arg res) (p-*-m res arg))
				 (m-*-m res arg))))
	finally (return res)))

(defun p-+-p (poly1 poly2)
  ; This function takes two perfect polynomials (arguments already sorted)
  ; and returns their sum.
  (if* (or poly1 poly2)
      (let ((new-args (merge-sort-args (args-of poly1) (args-of poly2) 'total-order-2)))
	(if* (cdr new-args) 
	    (make-term '+ new-args)
	    (car new-args)))
      '(0)))

(defun m-*-m (mon1 mon2)
  ; This function takes two perfect monomials and returns their product. 
  ; mon1 is not equal to 0.
  (cond ((null mon1) mon2)
	((null mon2) mon1)
	((equal '(0) mon2) mon2)
	(t (let ((res-args (if* (memq '* $ac)
			       (merge-sort-args
				 (*-canonicalize mon1)
				 (*-canonicalize mon2)
				 'total-order-2)
			       (append 
				 (*-canonicalize mon1)
				 (*-canonicalize mon2)))))
	     (if* (cdr res-args)	;more than one argument to the and.
		 (make-term '* res-args)
		 (car res-args))))))

(defun m-*-p (mon poly) 
  ; This function takes a perfect monomial and a perfect polynomial 
  ; (arguments already sorted) and returns their product.
  (cond ((null (args-of poly)) '(0))
	((equal '(0) mon) mon)
	((null mon) poly)
	((memq '* $ac)
	 (sloop with monomials-that-get-smaller = nil
	       with monomials-that-dont = nil
	       with mon-size = (length (*-canonicalize mon))
	       for m in (args-of poly)
	       as new-m = (m-*-m mon m)
	       as m-size = (length (*-canonicalize m))
	       as new-m-size = (length (*-canonicalize new-m))
	       do
	   ; This function assumes that if m1 > m2 then m*m1 > m*m2 (using total-order-2)
	   ; This might not be the case if m and m1 or m and m2 share atomic formulae
	   ; To check for this I check the size of the m*m1 and see if it is equal to
	   ; the sum of the sizes of m and m1.
	   ; If it isn't then I know that I have to reinsert m*m1 into the list at the end.
	   (if* (= new-m-size (+ mon-size m-size))
	       then (setq monomials-that-dont (append monomials-that-dont (ncons new-m)))
	       else (setq monomials-that-get-smaller
			  (insert-sort-arg new-m monomials-that-get-smaller 'total-order-2)))
	       finally
		 (return
		   (let ((res-args (merge-sort-args monomials-that-get-smaller
						    monomials-that-dont 'total-order-2)))
		       (if* (null res-args) then '(0)
			   elseif (cdr res-args) then (make-term '+ res-args)
			   else (car res-args))))))
	(t (setq poly (sloop for m in (args-of poly) collect (m-*-m mon m)))
	   (if* (null poly) 
	       then '(0)
	       elseif (cdr poly) then (make-term '+ poly)
	       else (car poly)))))

(defun p-*-m (poly mon)
  (cond ((null (args-of poly)) '(0))
	((equal '(0) mon) mon)
	((null mon) poly)
	(t (setq poly (sloop for m in (args-of poly) collect (m-*-m m mon)))
	   (if* (null poly) 
	       then '(0)
	       elseif (cdr poly) then (make-term '+ poly)
	       else (car poly)))))

(defun p-*-p (poly1 poly2)
  ; This function takes two perfect polynomials (arguments already sorted)
  ; and returns their product.
  (sloop with res = '(+)
	for m1 in (args-of poly1)
	as new-arg = (m-*-p m1 poly2) do
    (setq res
	  (if* (and (nonvarp new-arg) (eq '+ (op-of new-arg)))
	      (if* (and (nonvarp res) (eq '+ (op-of res)))
		   (p-+-p res new-arg)
		   (m-+-p res new-arg))
	      (if* (and (nonvarp res) (eq '+ (op-of res)))
		 (m-+-p new-arg res)
		 (m-+-m res new-arg))))
	finally (return res)))

(defun m-+-m (mon1 mon2)
  ; This function takes two perfect monomials and returns their sum.
  (cond ((equal '(0) mon1) mon2)
	((equal '(0) mon2) mon1)
	(t (if* (total-order-2 mon1 mon2)
	       (list '+ mon1 mon2)	; mon1 > mon1
	       (list '+ mon2 mon1)))))	; mon1 <= mon2

(defun m-+-p (mon poly)
  ; This function takes a perfect monomial (arguments already sorted)
  ; and a perfect polynomial
  ; and returns their sum.
  ; This is basically insertion of mon into poly taking care to remove a duplicate mon.
  (if* (equal '(0) mon)
      then poly
      else (sloop with 1st-part-of-poly = nil
		 for rest-of-poly on (args-of poly)
		 as m = (car rest-of-poly) 
		 do (if* (total-order-2 mon m)
			(return (make-term '+ (append 1st-part-of-poly
						      (ncons mon) rest-of-poly)))
			(setq 1st-part-of-poly (append1 1st-part-of-poly m)))
		 finally (return (make-term '+ (append1 1st-part-of-poly  mon))))))

(defun merge-sort-args (l1 l2 &optional (pred 'alphalessp))
  ; This functions takes two sorted lists and merges them.
  ; Good for +'s args or *'s args if * is commutative.
  (sloop with res = nil
	with ll1 = l1
	with ll2 = l2
	with cl1
	with cl2
	while (and ll1 ll2) do
    (setq cl1 (car ll1)
	  cl2 (car ll2))
    (cond ((funcall pred cl1 cl2)
	   (setq res (append res (ncons cl1))
		 ll1 (cdr ll1)))
	  (t (setq res (append res (ncons cl2))
		   ll2 (cdr ll2))))
	finally (return (cond (ll1 (append res ll1))
			      (ll2 (append res ll2))
			      (t res)))))

(defun insert-sort-arg (g_object l_list &optional u_comparefn)
  ; This functions takes a sorted list l_list and inserts g_object into it.
  ; If g_object is already in l_list then this function returns
  ; l_list with one g_object removed from it.
  (cond
    ((null l_list) (ncons g_object))
    (t (if* (null u_comparefn) (setq u_comparefn 'string-lessp))
       (sloop with prev-position = nil
	     for position on l_list
	     as x = (car position)
	     if (funcall u_comparefn g_object x)
	       return (if* prev-position
			  (progn (rplacd prev-position (cons g_object position)) l_list)
			  (cons g_object l_list))
	     else do (setq prev-position position)
	     finally (return (progn (rplacd prev-position (ncons g_object)) l_list))))))

(defun +-canonicalize (term)
  ; Convert anything into args of a product. 
  (if* (nonvarp term) 
      (if* (eq (op-of term) '+) then (args-of term) 
	  elseif (eq (op-of term) '0) then nil
	  else (ncons term))
      (ncons term)))

(defun *-canonicalize (term)
  ; Convert anything into args of a product. 
  (if* (and (nonvarp term) (eq (op-of term) '*))
      (args-of term)
      (ncons term)))


;;; Group Two: reduction in built-in associativity.


(defun poly-reduce-at-root (term op-rules)
  ; Returns rewritten term iff p-term can be rewritten.
  (caseq (op-of term)
    (+ (reduce-+-term term (get-rules-with-op '+ op-rules)))
    (* (reduce-*-term term (get-rules-with-op '* op-rules)))
    (t nil)))

(defun poly-reduce-at-root-one-rule (term rule &aux l1)
  ; return the reduced term by rule.
  (if* (variablep term)
      nil
      (if* (same-op term (lhs rule)) then
	  (setq l1 (polish-premises (ctx rule) rule))
	  (caseq (op-of term)
	    (* (if* (eq (op-of (lhs rule)) '*) 
		   (flat-term (reduce-*-term term (ncons rule)))))
	    (+ (if* (eq (op-of (lhs rule)) '+) 
		   (flat-term (reduce-+-term term (ncons rule)))))
	    (t (if* (setq l1 (polish-premises (ctx rule) rule)
			 l1 (applies (lhs rule) term l1))
		   (flat-term (add-to-args rule l1))))))))

(defun poly-cycle-reduce-at-root-one-rule (term rule &aux condi)
  ; return the reduced term by rule.
  (if* (variablep term)
      nil
      (if* (same-op term (lhs rule)) then
	  (setq condi (list (var-list (rhs rule)) (rhs rule)))
	  (caseq (op-of term)
	    (* (flat-term (reduce-*-term term (ncons rule) condi)))
	    (+ (flat-term (reduce-+-term term (ncons rule))))
	    (t (if* (setq condi (applies (lhs rule) term condi))
		   (add-to-args rule condi)))))))
;		   (flat-term (add-to-args rule condi))))))))

(defun poly-cycle-luck (new old) (total-order new old))
;(or (total-order new old) (reducible new)))

(defun reduce-+-term (term &optional rules condi)
  (sloop for rule in (or rules (get-rules-with-op '+ nil))
	with rest-args
	with left-*-args
	with right-*-args
	with res
	if (and (not (and $instant (is-homogeneous-rule rule)))
		(setq res (poly-match-+ (lhs rule) term condi)))
	  do
	    (if* $trace-proof then (push (ruleno rule) $used-rule-nums))
	    ;; Structure of the value returned by poly-match-+ is
	    ;;    ((rest-of-+-args left-*-args . right-*-args) . substitution)
	    (setq right-*-args (pop res)
		  rest-args (pop right-*-args)
		  left-*-args (pop right-*-args)
		  res (applysubst res (rhs rule)))
	    (if* (or left-*-args right-*-args)
		(setq res (nconc left-*-args (ncons res) right-*-args)
		      res (make-term '* res)))
	    (if* rest-args 
		(setq res (nconc (list '+ res) rest-args)))
	    (return res)))
;	    (return (flat-term res))))

(defun reduce-*-term (term &optional rules condi)
  ; "term" is rooted by "*". 
  ; If "term" is reducible at the root, then return the reduced term.
  ; Otherwise, nil.
  (sloop for rule in (or rules (get-rules-with-op '* nil))
	with left-args
	with right-args
	with res
	do
    (if* (setq res (poly-match-* (lhs rule) term *empty-sub* condi nil)) then
	(if* $trace-proof then (push (ruleno rule) $used-rule-nums))
	
	;; Structure of the value returned by match-set is
	;;    ((left-args . right-args) . substitution)
	(setq right-args (pop res)
	      left-args (pop right-args)
	      res (applysubst res (rhs rule)))

	(if* (and (null left-args) (null right-args))
	    (return (flat-term res))
	    (return (simplify-* (nconc left-args (ncons res) right-args)))))))

(defun poly-match-+ (t1 t2 &optional condi &aux res)
  ; Return ((rest-of-args left-*-args . right-*-args) . substitution) 
  ; if the matching exists.
  ; Return NIL otherwise.
  (if* (setq res (ac-match (ncons (list t1 t2 nil)) nil condi t))
      (let ((rest-*-args (pop res))
	    (rest-+-args (assoc '$extra res)))
	(if* rest-+-args then
	    (setq res (remove0 rest-+-args res)
		  rest-+-args (ncons (cdr rest-+-args))))
	(cons (cons rest-+-args rest-*-args) res))))

(defun poly-match-* (first second &optional (sigma *empty-sub*) condi triples)
  ; Return ((left-*-args . right-*-args) . substitution)
  ; Return (rest-of-xor-args rest-of-and-args . substitution) if the matching exists.
  ; Return NIL otherwise.
  (let ((args1 (args-of first))
	(args2 (args-of second))
	(not-first (pop sigma)))
    (if* not-first 
	(poly-match-test-rest-*-args args1 args2 sigma condi triples not-first)
	(poly-match-find-rest-*-args args1 args2 sigma condi triples))))

(defun poly-match-one-to-* (first second sigma condi triples)
  (let ((args1 (ncons first))
	(args2 (args-of second))
	(not-first (pop sigma)))
    (if* not-first 
	(poly-match-test-rest-*-args args1 args2 sigma condi triples not-first)
	(poly-match-find-rest-*-args args1 args2 sigma condi triples))))
  
(defun poly-match-test-rest-*-args (args1 args2 sigma condi triples rest-args)
  (let ((left-args (car rest-args))
	(right-args (cdr rest-args))
	(n1 (length args1)))
    (if* (and (sloop for xa in left-args always (equal xa (pop args2)))
	     (= (length args2) (+ n1 (length right-args)))
	     (equal right-args (rest-elements args2 n1))
	     (sloop for xa in args1 
		   as xb in args2 
		   always (setq sigma (match xa xb sigma))))
	(ac-match triples (cons rest-args sigma) condi t))))

(defun poly-match-find-rest-*-args (args1 args2 sigma condi triples)
  ;; try to make different "left-args" and "right-args".
  (sloop with left-args with new
	with n1 = (length args1)
	with n2 = (length args2)
	for i from 0 to (- n2 n1)
	for args-2 on args2
	do (setq new sigma)
	   (if* (and (sloop for xa in args1 
			  for xb in args-2 
			  always (setq new (match xa xb new)))
		    (setq new
			  (ac-match triples 
				    (cons (cons left-args
						(if* (nequal i n2) 
						    (rest-elements args-2 n1)))
					  new)
				    (append1 condi 
					     (make-term '* args-2))
				    t)))
	       (return new)
	       (push-end (car args-2) left-args))
	finally (return nil)))

(defun rest-elements (args-2 n1)
  ; return the last |args-2| - n1 elements of args-2 in order.
  (sloop for i from 1 to n1 do (setq args-2 (cdr args-2))
	finally (return args-2)))

(defun first-n-elements (args n1)
  ; return the first n1 elements of args in order.
  (sloop for i from 1 to n1 for xa in args collect xa))


;;; Group Three: Superposition with built-in distribution law and associativity law.

(defun poly-super-at-* (r1 r2 lhs2 sub pos source flag)
  (let* ((lhs1 (lhs r1))
	 (rhs1 (rhs r1))
	 (n1 (length (cdr lhs1)))
	 ;(vn (length (var-list lhs1)))
	 (n2 (length (cdr sub))) 
	 left-args res ctx subst)

;    (if* (and (= vn 1) (is-subset (args-of sub) $subs)) then nil else
;         (if* (= vn 1) (setq $subs (append $subs (args-of sub))))

    (sloop with last-arg = (car (last sub))
	  for i downfrom n2 to 2
	  for args on (args-of sub) 
	  as first-n = (first-n-elements args n1)
	  if $no-rule-del
	    do					
	      (if* (member0 first-n $subs) then nil else
		  (push first-n $subs)
		  (if* (> n1 i) then
		      (if* (variablep last-arg) then
			  (add-time $unif_time 
				    (setq subst (unifier (compact-last-elements lhs1 i)
							 (make-term '* args))))
			  (setq res nil)
			  else (setq subst nil)); rest args is empty.
		      elseif (= flag 0) then
		      (add-time $unif_time 
				(setq subst (unifier lhs1 (make-term '* first-n))))
		      (if* subst (setq res (rest-elements args n1)))
		      else (setq subst nil))
		  
		  (if* subst then
		      (if* (or (ctx r1) (ctx r2)) 
			  (setq ctx (handle-conditions (ctx r1) (ctx r2) subst)))
		      (if* (not-falsep ctx) then
			  (setq res (if* (or left-args res) 
					(make-term '* (append left-args (ncons rhs1) res))
					rhs1)
				res (make-eqn
				  (applysubst subst (rplat-in-by pos lhs2 res))
				     (applysubst subst (rhs r2))
				     ctx 
				  source)
				res (flatten-eqn res)
				$ncritpr (1+ $ncritpr))		      
			  (if* (well-typed-eqn res) (process-critpair res subst))))
	      (push-end (car args) left-args))
	      else return nil)))

(defun poly-super-at-*-0 (r1 r2 lhs2 sub pos source)
  (let* ((lhs1 (lhs r1))
	 (rhs1 (rhs r1))
	 (n1 (length (cdr lhs1)))
	 ;(vn (length (var-list lhs1)))
	 (n2 (length (cdr sub))) 
	 left-args res ctx subst)

    (if* (is-subset (args-of sub) $subs) then nil else
	(setq $subs (append $subs (args-of sub)))

    (sloop for i downfrom n2 to 2
	  for args on (args-of sub) 
	  as first-n = (first-n-elements args n1)
	  if (and $no-rule-del (>= i n1))
	    do					
	      (add-time $unif_time 
			(setq subst (unifier lhs1 (make-term '* first-n))))
	      (if* subst then
		  (setq res (rest-elements args n1))
		  (if* (or (ctx r1) (ctx r2)) 
		      (setq ctx (handle-conditions (ctx r1) (ctx r2) subst)))
		  (if* (not-falsep ctx) then
		      (setq res (if* (or left-args res) 
				    (make-term '* (append left-args (ncons rhs1) res))
				    rhs1)
			    res (make-eqn
				  (applysubst subst (rplat-in-by pos lhs2 res))
				  (applysubst subst (rhs r2))
				  ctx 
				  source)
			    res (flatten-eqn res)
			    $ncritpr (1+ $ncritpr))		      
		      (if* (well-typed-eqn res) (process-critpair res subst))))
	      (push-end (car args) left-args)
	  else return nil))))

(defun poly-super-at-*-1 (r1 r2 lhs2 sub pos source)
  (let* ((lhs1 (lhs r1))
	 (rhs1 (rhs r1))
	 (n1 (length (cdr lhs1)))
	 (n2 (length (cdr sub))) 
	 left-args res ctx subst
	 (last-arg (car (last sub))))

    (if* (and (variablep last-arg) (not (member0 last-arg $subs))) then
	(sloop for vars in (ref-symmetry-vars r2)
	      if (memq last-arg vars) 
		return (setq $subs (append $subs vars))
	      finally (push last-arg $subs))

    (sloop for i downfrom n2 to 2
	  for args on (args-of sub) 
	  if $no-rule-del
	    do					
	      (if* (> n1 i) then
		  (add-time $unif_time 
			    (setq subst (unifier (compact-last-elements lhs1 i)
						 (make-term '* args))))
		  (if* subst then
		      (if* (or (ctx r1) (ctx r2)) 
			  (setq ctx (handle-conditions (ctx r1) (ctx r2) subst)))
		      (if* (not-falsep ctx) then
			  (setq res (if* (or left-args res) 
					(make-term '* (append left-args (ncons rhs1)))
					rhs1)
				res (make-eqn
				      (applysubst subst (rplat-in-by pos lhs2 res))
				      (applysubst subst (rhs r2))
				      ctx 
				      source)
				res (flatten-eqn res)
				$ncritpr (1+ $ncritpr))		      
			  (if* (well-typed-eqn res) (process-critpair res subst)))
		      (return nil)))
	      (push-end (car args) left-args)
	  else return nil))))
	     
(defun compact-last-elements (term n)
  ; term is of form: f(t1, t2, ..., tk), 
  ; return a term of form: f(t1, t2, ..., f(tj, .., tk)).
  (sloop for j from 1
	for xa in term 
	if (<= j n) collect xa into l1
	else collect xa into l2
	finally (return (append1 l1 (make-term (op-of term) l2)))))

(defun poly-super-distribution (rule)
  (if* (or (not $instant) 
	  (eq (car (rule-source rule)) 'distr)
	  (not (is-rooted-+ (lhs rule)))
	  (is-homogeneous-rule rule)) then
      (sloop with eqn 
	    for xa in (one-presentative (nonlinear-vars-under-* (lhs rule))
					(ref-symmetry-vars rule))
	    as new = (list '+ (make-new-variable 'y) (make-new-variable 'z))
	    if $no-rule-del do
		(setq eqn (make-eqn (subst0 new xa (lhs rule))
				    (subst0 new xa (rhs rule))
				    (subst0 new xa (ctx rule))
				    (list 'distr (ruleno rule)))
		      eqn (flatten-eqn eqn)
		      $ncritpr (1+ $ncritpr))
		(process-critpair eqn))))

(defun nonlinear-vars-under-* (term)
  (if* (variablep term) 
      nil
      (rem-dups (caseq (op-of term)
		  (* (eles-more-than-1 (sloop for xa in (args-of term)
					   if (variablep xa) collect xa)))
		  (t (mapcan 'nonlinear-vars-under-* (args-of term)))))))

(defun eles-more-than-1 (lis)
  ; return a set of elements of lis that have more than one copy.
  (sloop with l2 for xa in lis
	if (memq xa l1) do (query-insert xa l2)
	else collect xa into l1
	finally (return l2)))


;;;; Group Four: Utility functions

(defun move-lhs-args (ruleno-c rule)
  ; a rule is a character rule if it is of form 
  ;       x+x+x+ ... +x ---> 0
  ; where + is ac and 0 is the unit of +. Its abrev. form is
  ;       nx ---> 0
  ; where n is a natural number, called as the characteristics
  ; "c" is a number and the root of the lhs of "rule" has character "c".
  ; If the lhs of "rule" has n copies of a smaller argument less then others,
  ; move c-n copies of that argument to the rhs.
  ; If not and there exists n copies of any arguments and c <= 2n,
  ; then move n arguments to the rhs.
  (let ((ruleno (car ruleno-c))
	(c (cadr ruleno-c))
	(lhs (mult-form (args-of (lhs rule)))) small)
    ; At first, partition lhs into big and small two sets.
    (if* (cdr lhs) then
	(sloop for xa in lhs as t1 = (car xa) do
	  (pop lhs)
	  (if* (sloop for ya in lhs thereis (poly-lrpo (car ya) t1))
	      (push xa small)
	      (setq lhs (append1 lhs xa))))

	(if* (and (null small) (null (cddr lhs)) (equal (rhs rule) '(0)))
	    (setq small (ncons (car lhs))))

	(if* small then
	    (setq lhs (args-of (lhs rule)))
	    (sloop for xa in small do (setq lhs (remove0 (car xa) lhs)))
	    (setq lhs (if* (cdr lhs) (make-term (op-of (lhs rule)) lhs) (car lhs))
		  c (nconc (list (op-of (lhs rule)) (rhs rule))
			   (sloop for xa in small 
				 append (ntimes (- c (cdr xa)) (car xa))))
		  c (make-eqn lhs c (ctx rule)
			      (list ruleno (ruleno rule) 'ext2))
		  c (flatten-eqn c)
		  $ncritpr (1+ $ncritpr))
	    (process-critpair c)
	    elseif $instant-seeds then
	    (make-rule-instances c lhs rule)))))

(defun make-rule-instances (character mlhs rule &aux vars eqn)
  (if* (setq vars (rem-dups (sloop for xa in mlhs append (all-vars (car xa))))) 
      then
      ; If there are different monomials in lhs, then do the following ...
      (sloop for terms in (get-instance-terms (length vars)) 
	    as sigma = (sloop for var in vars for ter in terms 
			     collect (cons var ter))
	    do (setq eqn (make-eqn (lhs rule) (rhs rule) nil
				   (list 'insta (ruleno rule)))
		     eqn (applysubst-eqn sigma eqn))
	       (if* (> $trace_flag 1) then
		   (terpri) 
		   (princ (uconcat "Making an instance of Rule [" (ruleno rule)
			 "], and simplifying it by Polynomial machine:"))
		   (terpri) (princ "    ") 
		   (write-eqn eqn)
		   (princ "    with the substitution: ") 
		   (write-sigma sigma) (terpri))
	       (setq $used-rule-nums nil)
	       (move-monos eqn character))))

(defun move-monos (eqn &optional char)
  ; At first, turn rhs into a mult-set form and merge lhs and rhs into one by 
  ; deleting the common part and change the sign of mons in rhs.
  (let ((lhs (lhs eqn)) (rhs (rhs eqn)) small)
    (setq lhs (norm-mult-monos (mult-form (+-canonicalize lhs)))
	  rhs (norm-mult-monos (mult-form (+-canonicalize rhs))))
    
    (setq small (mult-diff2 lhs rhs)
	  rhs (mult-diff2 rhs lhs)
	  lhs (nconc small (change-mono-sign char rhs))
	  small nil
	  lhs (sloop for xa in lhs 
		    if (nequal (remainder (cdr xa) char)  0)
		    collect (cons (car xa) (remainder (cdr xa) char))))
    
    ; Next, partition lhs into big and small two sets.
    (sloop for xa in lhs as t1 = (car xa) do
      (pop lhs)
      (if* (sloop for ya in lhs thereis (poly-lrpo (car ya) t1))
	  (push xa small)
	(setq lhs (append1 lhs xa))))
    
    (if* (and small (null (cdr lhs))) then
      (setq lhs (car lhs))
      (if* (< (times 2 (cdr lhs)) char) then
	(setq small (norm-sign-changed-monos char small))
	(setq lhs (ntimes (cdr lhs) (car lhs)))
	else
	(setq lhs (ntimes (- char (cdr lhs)) (car lhs))))
      
      (setq lhs (if* (cdr lhs) (make-term '+ lhs) (car lhs))
	    rhs (demult-form small)
	    rhs (if* (cdr rhs) (make-term '+ rhs) (car rhs))
	    rhs (make-new-rule lhs rhs nil
			       (append (eqn-source eqn)
				       (rem-dups $used-rule-nums)))
	    rhs (flatten-rule rhs)
	    $ncritpr (1+ $ncritpr))
      (add-rule rhs))))
		  
(defun poly-lrpo (m1 m2)
  (if* (lrpo m1 m2) then t
      elseif (lrpo m2 m1) then nil
      elseif (or (variablep m1) (variablep m2)) then nil
      elseif (and (eq (op-of m1) '*) (same-root m1 m2))
      then (let ((l1 (length m1)) (l2 (length m2)))
	     (if* (= l1 l2) then
		 (sloop for xa in (cdr m1) for xb in (cdr m2)
		       if (nequal xa xb) return (lrpo xa xb)
		       finally (return nil))
		 else (> l1 l2)))
      else nil))

(defun is-character-rule (rule &optional test)
  ; a rule is a character rule if it is of form 
  ;       x+x+x+ ... +x ---> 0
  ; where + is ac and 0 is the unit of +. Its abrev. form is
  ;       nx ---> 0
  ; where n is a natural number, called as the characteristics
  (if* (or $polynomial $check-symmetry) then
  (let ((ruleno (ruleno rule)) (lhs (lhs rule)))
    (if* (assoc ruleno $character-rules) 
	then (assoc ruleno $character-rules)
	elseif (and test 
		    (ac-root lhs)
		    (variablep (first-arg lhs))
		    (null (remove0 (first-arg lhs) (cddr lhs)))
		    (is-constant-term (rhs rule)))
	then
	(push (setq rule (list ruleno (length (args-of lhs))
			       (op-of lhs) (rhs rule)))
	      $character-rules)
	rule))
  else nil))

(defun reduce-by-character (char term)
  (sloop with succ with l1
	with num = (cadr char)
	with rhs = (cadddr char)
	with margs = (mult-form (args-of term))
	for xa in margs
	if (>= (cdr xa) num)
	  do (setq margs (delete0 xa margs 1)
		   l1 (quotient (cdr xa) num))
	     (sloop for i from 1 to l1 do (push rhs succ))
	     (sloop for i from 1 to (- (cdr xa) (times l1 num))
		   do (push (car xa) succ))
	finally (return 
		  (if* succ then
		      (query-insert (car char) $used-rule-nums)
		      (setq succ (nconc succ (demult-form margs)))
		      (if* (cdr succ) (make-term (caddr char) succ) (car succ))))))

(defun poly-size (term &aux l1)
  (if* (variablep term) then 1
      else
      (caseq (op-of term)
	(+ (1+ (apply '+ (mapcar 'poly-size (args-of term)))))
	(* (+ (max 0 (times 10 (- (length (args-of term)) $xnx)))
		(apply '+ (mapcar 'w-size (args-of term)))))
	(t (+ (if* (setq l1 (assoc (op-of term) $f-weights)) (cdr l1) 1)
		(apply '+ (mapcar 'poly-size (args-of term))))))))

(defun poly-initialize ()
  (if* (not (memq '+ $operlist)) then
      (push '+ $operlist)
      (set-infix '+)
      (set-arity '+ 2))
  (if* (not (memq '* $operlist)) then
      (push '* $operlist)
      (set-infix '*)
      (set-arity '* 2))
  (set-status '* 'lr)
  (if* (not (memq '0 $operlist)) then (push '0 $operlist))

  (query-insert '+ $ac)
  (query-insert '* $associative)
  (query-insert '(+ nil 0) $divisible)

  (setq $post-bound (times 100 $many-args))
  ;(setq $ordering 's)
  ;(if* (= $idem 1) (setq $idem 2 $ex2 10))
  (terpri) (princ "Polynomial machine is running ...")
  (terpri))


;;; Another group of functions for normalizing rhs of rules.

(defun is-homogeneous-term (term)
  (and (is-rooted-+ term)
       (nonvarp (first-arg term))
       (sloop with first = (car (args-of term))
	     for xa in (cddr term) always (equal xa first))))

(defun is-homogeneous-rule (rule) (is-homogeneous-term (lhs rule)))

(defun poly-add-homo-rules (rule)
  (add-associate-list (length (args-of (lhs rule))) rule $poly-homo-rules))

(defun norm-poly (term &optional (strong t))
  ; term is +-rooted and $polynomial is on.
  (setq term (norm-mult-monos (mult-form (+-canonicalize (flat-term term))))
	term (demult-form term)
	term (if* (null term) then '(0) 
		 elseif (cdr term) 
		 then (simplify-+ term) 
		 else (car term)))

  (if* (and strong (is-rooted-+ term))
      (sloop for new = (reduce-+-term term)
	    if new do (setq term (flat-term new))
		      (if* (not (is-rooted-+ term)) (return term))
	    else return term)
      term))
						
(defun norm-sign-changed-monos (num monos &aux reduced mono new)
  (setq monos (change-mono-sign num monos))
  (sloop while monos do
    (setq mono (pop monos))
    (if* (and (> (times 2 (cdr mono)) num)
	     (setq new (reduce-mono mono))) then
	(sloop for xa in reduced 
	      if (sloop for xb in new thereis (equal (car xa) (car xb)))
		do (setq new (mult-insert xa new))
		   (setq reduced (remove0 xa reduced)))
	(setq monos (mult-sort-merge monos new))
	else
	(setq reduced (push-end mono reduced)))
	finally (return reduced)))

(defun norm-mult-monos (monos &aux reduced mono new)
  ; normalize each monomials.
  (sloop while monos do
    (setq mono (pop monos))
    (if* (setq new (reduce-mono mono)) then
	(sloop for xa in reduced 
	      if (sloop for xb in new thereis (equal (car xa) (car xb)))
		do (setq new (mult-insert xa new))
		   (setq reduced (remove0 xa reduced)))
	(setq monos (mult-sort-merge new monos))
	else
	(setq reduced (push-end mono reduced)))
	finally (return reduced)))

(defun reduce-mono (mono)
  ;; coef is the coeffcient of the term in a monomial.
  ;; return a list of monomials.
  (let ((coef (cdr mono)) (term (car mono)))
    (cond ((sloop for xa in $character-rules 
		 if (and (eq '+ (caddr xa)) (>= coef (cadr xa)))
		   return (if* (= (setq xa (remainder coef (cadr xa))) 0)
			      `((nil . 0))
			      (ncons (cons term xa)))))
	  ((variablep term) nil)
	  ((sloop for xa in $p-commut-rules 
		 if (eq '+ (cadr xa))
		   return (reduce-by-p-commut2 xa coef term)))
	  ((sloop for xa in $poly-homo-rules 
		 if (>= coef (car xa))
		   do (if* (setq xa (reduce-by-homo-rules coef term (car xa) (cdr xa)))
			  (return xa))))
	  ((sloop for rule in $rule-set 
		 do (if* (setq rule (flat-term (reduce-by-one-rule term rule)))
			(return (if* (is-rooted-+ rule)
				    (times-cdr coef
					       (mult-form (args-of rule)))
				    (ncons (cons rule coef))))))))))

(defun reduce-by-homo-rules (coef term num rules)
  ;
  (sloop for rule in rules 
	as first = (first-arg (lhs rule))
	as res = (op-of (lhs rule))
	if (eq res '+)
	  do (if* (setq res (flat-term (reduce-by-one-at-root 
					term (change-lhs rule first)))) then
		 ;(query-insert (ruleno rule) $used-rule-nums)
		 (setq first (quotient coef num)
		       res (if* (is-rooted-+ res) 
			       (times-cdr first (mult-form (args-of res)))
			       (ncons (cons res first))))
		 (return (if* (= (setq num (times first num)) coef)
			     res
			     (cons (cons term (- coef num)) res))))))
