;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

; This file contains functions to implement the boolean ring transform
; reductions. First-trans takes a term in conjunctive normal form as
; set up by the reading routines, and returns one with 'and' and 'xor'
; (exclusive or). Brt is the main function that controls the reductions.
; This file also contains functions for the eq-find and transitive
; closure algorithms. These are prefixed 'union' and 'tr' respectively.
; They have been assimilated within the brt functions for maximum 
; efficiency. Simp-and is the function that calls the eq-find and
; transitive closure algorithms with each of its list of conjuncts.
; Trans-simp is the toplevel functions to convert a boolean ring
; polynomial back into disjunctive normal form. It only needs to
; apply conversions if the top-level operator of its argument is xor.

(defun simp-first-trans (term)
  (cond
    ((null term) nil)
    ((variablep term) term)
;;  ((memq (op-of term) '(and &))
;;   (make-term 'and (mapcar 'simp-first-trans (args-of term))))
    (t (simplify (first-trans term)))))

(defun first-trans (term)
  ;  Transforms a boolean term with 'and' and 'or' operators into a
  ;  boolean ring term with '&' and 'xor', exclusive or.
  ;  Returns modified term.
  (cond
   ((null term) nil)
   ((variablep term) term)
   (t (let ((new-args (mapcar 'first-trans (args-of term))))
	(caseq (op-of term)
	       (not `(xor (true) . ,new-args))
	       (and  `(and . ,new-args))
	       (or  `(xor (and . ,new-args) . ,new-args))
	       (equ `(xor (true) . ,new-args))
	       (-> `(xor (and . ,new-args) ,(car new-args) (true)))
	       (t (make-term (op-of term) new-args)))))))

(defun or-args (arg1 arg2)
  ; Return an equivalent term (ARG1 or ARG2).
  (cond ((not (and arg1 arg2)) nil)
        ((equal arg1 arg2) arg1)
        (t (brt `(xor (and ,arg1 ,arg2) ,arg1 ,arg2)))))

(defun not-arg (arg1)
  ; Return an equivalent term (not ARG1).
  (cond ((null-ctx arg1) '(false))
        ((falsep arg1) nil)
        (t (m-xor-p `(true) arg1))))

(defun canonicalize (term)
   ; Convert anything into a sum of products.  If it isn't already a sum of
   ; products, then insert trivial sums and products until it is.
   (if* (eq (op-of term) 'xor) then (setq term (args-of term))
		 	      else (setq term (ncons term)))
   (make-term 'xor (sloop for xa in term collect
                     (if* (eq (op-of xa) 'and) then xa else (list 'and xa)))))

(defun decanon-and (mon) 
  (caseq (length mon) ((1 0) '(true)) (2 (first-arg mon)) (t mon)))

(defun decanon-xor (poly) 
  (caseq (length poly)
	((1 0) '(false)) 
	(2 (decanon-and (first-arg poly))) 
	(t (make-term 'xor (sloop for xa in (args-of poly) 
				 collect (decanon-and xa))))))

(defun merge-and-remove-pairs (l1 l2 &optional (pred 'alphalessp))
  ; This functions takes two sorted lists which contain no duplicates and merges them
  ; removing common pairs
;  (add-time $brt-sort-time
  (sloop with res = nil
	with ll1 = l1
	with ll2 = l2
	with cl1
	with cl2
	while (and ll1 ll2) do
    (setq cl1 (car ll1)
	  cl2 (car ll2))
    (cond ((equal cl1 cl2)
	   (setq ll1 (cdr ll1)
		 ll2 (cdr ll2)))
	  ((funcall pred cl1 cl2)
	   (setq res (append res (ncons cl1))
		 ll1 (cdr ll1)))
	  (t (setq res (append res (ncons cl2))
		   ll2 (cdr ll2))))
	finally (return (cond (ll1 (append res ll1))
			      (ll2 (append res ll2))
			      (t res)))));)

(defun merge-and-remove-dups (l1 l2 &optional (pred 'alphalessp))
 ; This functions takes two sorted lists which contain no duplicates and merges them
 ; making common pairs into one
;  (add-time $brt-sort-time
  (sloop with res = nil
	with ll1 = l1
	with ll2 = l2
	with cl1
	with cl2
	while (and ll1 ll2) do
    (setq cl1 (car ll1)
	  cl2 (car ll2))
    (cond ((equal cl1 cl2)
	   (setq res (append res (ncons cl1))
		 ll1 (cdr ll1)
		 ll2 (cdr ll2)))
	  ((funcall pred cl1 cl2)
	   (setq res (append res (ncons cl1))
		 ll1 (cdr ll1)))
	  (t (setq res (append res (ncons cl2))
		   ll2 (cdr ll2))))
	finally (return (cond (ll1 (append res ll1))
			      (ll2 (append res ll2))
			      (t res))))); )

(defun insert-and-remove-pairs (g_object l_list &optional u_comparefn)
  ; This functions takes a sorted list l_list and inserts g_object into it.
  ; If g_object is already in l_list then this function returns
  ; l_list with one g_object removed from it.
  (cond
    ((null l_list) (cons g_object l_list))
    (t
     (when (null u_comparefn)(setq u_comparefn 'string-lessp))
     (sloop
       with prev-position = nil
       for position on l_list
       for x = (car position)
       if (equal g_object x) return (remonce x l_list)
       else if (funcall u_comparefn g_object x)
       return (if*  prev-position
		   (progn (rplacd prev-position (cons g_object position)) l_list)
		   (cons g_object l_list))
       else do (setq prev-position position)
       finally (return (progn (rplacd prev-position  (ncons g_object)) l_list))))))

(defun m-and-m (mon1 mon2 &aux (hcm1 (half-canonicalize mon1)) (hcm2 (half-canonicalize mon2)))
  ; This function takes two perfect monomials (arguments already sorted)
  ; and returns their product.
  ; mon1 is not equal to false or to $anspred.
  (cond ((truep mon1) mon2)
	;((falsep mon1) mon1)
	((truep mon2) mon1)
	((falsep mon2) mon2)
	((eq $anspred (op-of mon2)) mon2) ; We should have this.
	((and (eq-tr-member hcm1) (eq-tr-member hcm2))
	 ; one of the atomic formula is an eq or transitive operator.
	 ; we have to run the union of the monomials through the transitive closure algorithm again.
	 (and-of-monomials (append hcm1 hcm2)))
	(t (let ((res-args (merge-and-remove-dups hcm1 hcm2 'total-order)))
	     (if* (cdr res-args)			;more than one argument to the and.
		 then (make-term 'and
				 (merge-and-remove-dups hcm1 hcm2 'total-order))
		 else (car res-args))))))

(defun m-and-p (mon poly &aux (poly-args (args-of poly)))
  ; This function takes a perfect monomial (arguments already sorted)
  ; and a perfect polynomial
  ; and returns their product.
  (cond ((null poly-args) '(false))
	((falsep mon) mon)
	((eq (op-of mon) $anspred) mon)  ; We should have this.
	((truep mon) poly)
	(t (sloop with monomials-that-get-smaller = nil
		 with monomials-that-dont = nil
		 with mon-size = (length (half-canonicalize mon))
		 for m in poly-args
		 for new-m = (m-and-m mon m)
		 for m-size = (length (half-canonicalize m))
		 for new-m-size = (length (half-canonicalize new-m))
		 do
	     ; This function assumes that if m1 > m2 then m*m1 > m*m2 (using total-order)
	     ; This might not be the case if m and m1 or m and m2 share atomic formulae
	     ; To check for this I check the size of the m*m1 and see if it is equal to
	     ; the sum of the sizes of m and m1.
	     ; If it isn't then I know that I have to reinsert m*m1 into the list at the end.
	     (if* (= new-m-size (+ mon-size m-size))
		 then (setq monomials-that-dont (append monomials-that-dont (ncons new-m)))
		 else (setq monomials-that-get-smaller
			    (insert-and-remove-pairs new-m monomials-that-get-smaller 'total-order)))
		 finally
		   (return
		     (let ((res-args (merge-and-remove-pairs monomials-that-get-smaller
							     monomials-that-dont 'total-order)))
		       (if* (null res-args) then '(false)
			   elseif (cdr res-args) then (make-term 'xor res-args)
			   else (car res-args))))))))

(defun p-and-p (poly1 poly2)
  ; This function takes two perfect polynomials (arguments already sorted)
  ; and returns their product.
  (sloop with res = '(xor)
	for m1 in (args-of poly1)
	for new-arg = (m-and-p m1 poly2) do
    (setq res
	  (selectq (op-of new-arg)
	    (xor (selectq (op-of res)
		   (xor (p-xor-p res new-arg))
		   (t (m-xor-p res new-arg))))
	    (t (selectq (op-of res)
		 (xor (m-xor-p new-arg res))
		 (t (m-xor-m res new-arg))))))
	finally (return res)))

(defun m-xor-m (mon1 mon2)
  ; This function takes two perfect monomials (arguments already sorted)
  ; and returns their sum.
  (cond ((falsep mon1) mon2)
	((falsep mon2) mon1)
	;((or (listp (op-of mon1)) (listp (op-of mon2))) (dbg))
	(t (selectq (total-order-res mon1 mon2)
	     (1 (make-term 'xor `(,mon1 ,mon2)))	; mon1 < mon2
	     (2 (make-term 'xor `(,mon2 ,mon1)))	; mon2 < mon1
	     (0 '(false))				; mon1 = mon2
	     ))))

(defun m-xor-p (mon poly)
  ; This function takes a perfect monomial (arguments already sorted)
  ; and a perfect polynomial
  ; and returns their sum.
  ; This is basically insertion of mon into poly taking care to remove a duplicate mon.
  (if* (falsep mon) then poly
      else (sloop with 1st-part-of-poly = nil
		 with res-args
		 for rest-of-poly on (args-of poly)
		 for m = (car rest-of-poly) do
	     (selectq (total-order-res mon m)
	       (0 (setq res-args (append 1st-part-of-poly (cdr rest-of-poly)))
		  (return (if* res-args then
			      (if* (= (length res-args) 1) then (car res-args)
				  else (make-term 'xor res-args))
			      else '(false))))
	       (1 (return (make-term 'xor (append 1st-part-of-poly (cons mon rest-of-poly)))))
	       (2 (setq 1st-part-of-poly (append 1st-part-of-poly (ncons m)))))
		 finally (return (make-term 'xor (append 1st-part-of-poly (ncons mon)))))))

(defun p-xor-p (poly1 poly2)
  ; This function takes two perfect polynomials (arguments already sorted)
  ; and returns their sum.
  (let ((new-args (merge-and-remove-pairs (args-of poly1) (args-of poly2) 'total-order)))
    (if* new-args
	then (if* (cdr new-args) then (make-term 'xor new-args)
		 else (car new-args))
	else '(false))))

(defun brt-if (new old) (if* (equal new old) then old else (brt new)))

(defun brt (term &optional short)
  ; "brt" stands for boolean ring transform.
  ; Applies boolean ring transform on term. Works on reductions
  ; in a bottom fashion. Returns simplified term.
  (if* term then (add-time $brt_time (if* short
					then (simplify-almost-flat term)
					else (simplify term)))))

(defun simplify-almost-flat (term)
  ;  Applies boolean ring transform on term; it has already been flattened. 
  ;  The arguments of the operators "and" and "xor" are not already flatten.
  (if* (or (null term) (variablep term)) then term else
     (caseq (op-of term)
       (and (simp-and-simp (args-of term)))
       (xor (simp-xor-simp (sloop for arg in (args-of term) 
				 collect (simplify-flat arg))))
       (eq  (car (eq-find (ncons term))))
       (t (if* (member0 (op-of term) $translist) 
	      then (car (tr-find `((,(op-of term) ,term))))
	      else term)))))

(defun simplify-flat (term)
  ;  Applies boolean ring transform on term; it has already been flattened. 
  ;  The arguments of the operators "and" and "xor" are not already flatten.
  (if* (or (null term) (variablep term)) then term else
     (caseq (op-of term)
       (and (simp-and-simp (args-of term)))
       (xor (make-term 'xor (sloop for arg in (args-of term) collect (simplify-flat arg))))
       (eq  (car (eq-find (ncons term))))
       (t (if* (member0 (op-of term) $translist) 
	     then (car (tr-find `((,(op-of term) ,term))))
             else term)))))

(defun simplify (term)
  ;  Applies boolean ring transform on term. 
  ;  The arguments of the operators "and" and "xor" are not already flatten.
  (if* (or (null term) (variablep term)) then term else
     (caseq (op-of term)
       (and (simp-and (sloop for arg in (args-of term) collect (simplify arg))))
       (xor (simp-xor (sloop for arg in (args-of term) collect (simplify arg))))
       (eq  (car (eq-find (ncons term))))
       (t (if* (member0 (op-of term) $translist) 
	     then (car (tr-find `((,(op-of term) ,term))))
             else term)))))

(defun and-of-monomials (args &aux newargs)
  ; Returns simplified TERM whose top level operator is and.
  ; The term has been flattened, and all subterms simplified.
  (setq args (sort (eq-tr args) 'total-order))
  (cond ((member0 '(false) args) '(false))
;        ((sloop for ar in args			;
;	       if (or (falsep ar) (eq $anspred (op-of ar)))
;		 return ar 
;	       finally (return nil)))
	((setq newargs (ans-member args))	; Check is $anspred is a term
	 (if* (null (cdr newargs))
	     then (car newargs)
	     else (make-term 'and newargs)))
        (t (let ((pre (pop args)))
             (sloop while (truep pre) do (setq pre (pop args)))
             (setq args (sloop for this in args
                            if (not (or (truep this) 
                                        (equal this pre)))
                            collect (prog1 pre (setq pre this))))
             (cond (args (make-term 'and (append args (ncons pre))))
                   (pre pre)
                   (t '(true)))))))

(defun simp-and (args)
  (sloop with res = '(true) for arg in args do
    (if* (eq (op-of arg) $anspred) (return arg)) ; We should have this.
    (setq res
	  (selectq (op-of arg)
	    (xor (selectq (op-of res)
		   (xor (p-and-p res arg))
		   (t (m-and-p res arg))))
	    (false (return arg)) ; We should have this.
	    (t (selectq (op-of res)
		 (xor (m-and-p arg res))
		 (t (m-and-m res arg))))))
	finally (return res)))

(defun simp-and-simp (args &aux pre)
  ; Returns simplified TERM whose top level operator is and.
  ; The term has been flattened, and all subterms simplified.
  (setq args (sort (eq-tr args) 'total-order))
  (if* (member0 '(false) args) then '(false) else
      (setq pre (pop args))
      (sloop while (equal pre '(true)) do (setq pre (pop args)))
      (setq args (sloop for this in args
		       if (not (or (equal this '(true)) 
				   (equal this pre)))
			 collect (prog1 pre (setq pre this))))
      (cond (args (make-term 'and (nconc args (ncons pre))))
	    (pre pre)
	    (t '(true)))))

(defun xor-of-monomials (args)
  ; Returns simplified (xor ARGS), a sum. The TERM has been flattened.
  (let (previous)
     (setq args (sort args 'total-order)
           previous (pop args))
     (sloop while (equal previous '(false)) do (setq previous (pop args)))
     (setq args 
        (sloop for this in args 
           if (cond
                    ((equal this '(false)) nil)
                    ((equal this previous) (setq previous nil))
                    (previous t) 
                    (t (setq previous this) nil))
           collect (prog1 previous (setq previous this))))
     (if* (null args) then
        (if* previous then previous else '(false))
      elseif previous then (make-term 'xor (add-at-end args previous))
      elseif (null (cdr args)) then (car args)
      else (make-term 'xor args))))

(defun simp-xor (args)
  (sloop with res = '(false)
	for arg in args
	do

    ;(if* (eq (op-of arg) 'xor) then (setq arg (simp-xor (args-of arg))))

    (setq res
	  (selectq (op-of arg)
	    (xor (selectq (op-of res)
		   (xor (p-xor-p res arg))
		   (t (m-xor-p res arg))))
	    (t (selectq (op-of res)
		   (xor (m-xor-p arg res))
		   (t (m-xor-m res arg))))))
	finally (return res)))

(defun simp-xor-simp (args)
  ; Returns simplified TERM, a sum. The TERM has been flattened.
  (let (previous)
     (setq args (sort args 'total-order)
           previous (pop args))
     (sloop while (equal previous '(false)) do (setq previous (pop args)))
     (setq args 
        (sloop for this in args 
           if (cond
                    ((equal this '(false)) nil)
                    ((equal this previous) (setq previous nil))
                    (previous t) 
                    (t (setq previous this) nil))
           collect (prog1 previous (setq previous this))))
     (if* (null args) then
        (if* previous then previous else '(false))
      elseif previous then (make-term 'xor (add-at-end args previous))
      elseif (null (cdr args)) then (car args)
      else (make-term 'xor args))))

(defun eq-tr-member (args)
  ; returns true if one of the operators is eq or transitive.
  (sloop for arg in args
	as op = (op-of arg)
	thereis (or (eq op 'eq)
		    (member0 op $translist))))

(defun init-bool-ops ()
  ; Initialize boolean operators
  (set-arity2 'all '(bool univ bool))
  (set-arity2 'exist '(bool univ bool))
  (set-arity 'false 0)
  (set-arity2 'false '(bool)) 
  (set-arity 'true 0) 
  (set-arity2 'true '(bool)) 
  (set-arity 'not 1)
  (set-arity2 'not '(bool bool)) 
  (set-arity2 'eq '(bool univ univ))
  (set-infix '=)
  (set-arity2 '= '(bool univ univ))

  ; constructors for 
  ;     "num": { suc, 0 }
  ;     "list": { nl, cons }
;  (set-arity 'suc 1)
;  (set-arity2 'suc '(num num))
;  (set-arity 'nl 0)
;  (set-arity2 'nl '(list))
;  (set-arity 'cons 2)
;  (set-arity2 'cons '(list univ list))
  (sloop for op in '(xor and equ equ -> or and & *&*) do
	(set-infix op) (set-arity op 2) (set-arity2 op '(bool bool bool)))
  (sloop for op in $bool-ops do (set-predicate op))
  (setq $type-rela '((bool)) ; (list) (num))
	$constructors '(true false) ; (0 suc nl cons)
	$free-constructors '(true false) ; ( 0 suc nl cons)
	$num-type nil  ; the type name for numbers. the default "univ".
	$type-constructors '((bool true false)))) ; (num 0 suc) (list nl cons))))

(defun eqn2assertion (eqn)
  (if* (equal (lhs eqn) (rhs eqn)) then '(true)
      else
      (let ((lhs (lhs eqn)) (rhs (rhs eqn)))
	(caseq (op-of lhs)
	  (false (caseq (op-of rhs)
		   (true '(false))
		   (xor (m-xor-p '(true) rhs))
		   (t (m-xor-m '(true) rhs))))
	  (true rhs)
	  (xor (caseq (op-of rhs)
		 (true lhs)
		 (false (m-xor-p '(true) lhs))
		 (xor (setq lhs (m-xor-p '(true) lhs))
		      (caseq (op-of lhs)
			(xor (p-xor-p rhs lhs))
			(t (m-xor-p lhs rhs))))
		 (t (p-xor-p lhs (m-xor-m '(true) rhs)))))
	  (t (caseq (op-of rhs)
	       (true lhs)
	       (false (m-xor-m '(true) lhs))
	       (xor (p-xor-p rhs (m-xor-m '(true) lhs)))
	       (t (m-xor-p '(true) (m-xor-m lhs rhs)))))))))

;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

;#+franz (include "datamacs.l")
;#-franz (in-package "USER")

; ********WARNING*********
; *****Parental guidance suggested for children under the age of 17*********
; ********WARNING*********

(defun process-ass-simple (ass source)
  (if* ass then
      (add-time $norm_time 
                (setq $used-rule-nums nil
                      ass (norm-ctx ass))) ; normalization
      (if* $trace-proof then
	  (setq source (append source (rem-dups $used-rule-nums))
		$used-rule-nums nil)) ; put in the numbers of used rules.
      (add-time $ord_time (order-ass ass source))))

(defun process-ass2 (ass source)
  (process-ass-simple (simp-first-trans ass) source))
(defun process-ass1 (ass source) 
      (process-ass2 (if* (eq $more-break 'n)
			then (skolemize ass)
			else (break-ass ass source)) source))

(defun process-ass (ass source &aux l1)
  ; Add a new equation, doing all of the simplifications that we know how 
  ; to do. At first, try to reduce the size of ass. Then try to break ass
  ; to small sub-assertions. then try to skolemize, then boolean ring 
  ; transfomation ...
  (if* ass then
      (caseq (op-of ass)
	(true nil)
	(false (refuted-result source))
	(and (sloop for x in (args-of ass) do (process-ass x source)))
	((all exist) (process-ass 
		       (skolemize-away-quants ass ass nil) source))
	(equ (if* (truep (first-arg ass))
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
	(or  (if* (and (not (eq $more-break 'n)) (greaterp (or-count ass) 3))
		 then (sloop for xa in (break-at-or ass) do
			(process-ass xa source))
		 else (process-ass1 ass source)))
	(->  (if* (eq (op-of (first-arg ass)) 'or) 
		 then (setq l1 (args-of (first-arg ass)))
		 (sloop for xa in l1 do 
		   (process-ass `(-> ,xa ,(second-arg ass)) source))
		 elseif (eq (op-of (second-arg ass)) 'and) 
		 then (setq l1 (args-of (second-arg ass)))
		 (sloop for xa in l1 do 
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
	       (or (sloop for xa in (args-of l1) do
		     (process-ass `(not ,xa) source)))
	       (-> (process-ass (first-arg l1) source)
		   (process-ass `(not ,(second-arg l1)) source))
	       (t (process-ass1 ass source))))
	(eq (if* (= (length ass) 3) 
		then (push (make-eqn (first-arg ass) 
				     (second-arg ass) nil source) $eqn-set) nil
		else (process-ass-simple ass source)))
	(t (process-ass-simple ass source)))))

(defun break-ass (ass source &optional flag &aux l1)
   ; Attempt to break up equations in a more intelligent fashion.
   ; At present, every quantifier is under one of operators or, equ,
   ; ->, xor. Hence, we replace every quantified formula by a new one.
   (if* (quantifierp (op-of ass)) then
        (setq l1 ass)
	(sloop while (quantifierp (op-of (second-arg l1))) 
	    do (setq l1 (second-arg l1)))
	(rplaca (cddr l1) (break-ass (second-arg l1) source))
        (substvarfor ass source) 
      elseif (eq (op-of ass) 'not) then
	`(not ,(break-ass (first-arg ass) source flag))
      elseif (boolean-opp (op-of ass)) then
	(setq ass (make-term (op-of ass)
	  		     (sloop for xa in (args-of ass) collect 
		       		      (break-ass xa source (not flag)))))
        (if* (and flag (eq $more-break 'm)) 
	     then (substvarfor ass source)
	     else ass)
      else ass))

(defun substvarfor (ass source)
   ; Substitute a variable for ass.
   ; We call process-ass2 to introduce a new constraining equation,
   ; and we return a value that should be used for the variable.
   ; If flag is true, then just return ass.
   (let ((func (gennewsym $func-name)) (args (free-vars ass)))
        (if* $set_pred (set-predicate func))
	(set-arity func (length args))

	(if* $var-type-list then
	    (set-arity2 func 
			(cons (get-domain-type (op-of ass))
			      (sloop with xc for xa in args 
				    collect (if* (setq xc (assoc xa $var-type-list))
						then (cdr xc)
						else 'univ)))))
	(terpri) (princ "  Introducing") (display-one-arity2 func)
	(setq func (make-term func args))
	(princ "  ") (write-term func) 
	(princ " stands for ") (write-term ass) (terpri)
        (if* (predicatep (op-of ass)) 
	    then (set-predicate (op-of func))
		 (if* (quantifierp (op-of ass)) 
		    then (subst-quant-form func ass source)
		    else (process-ass2 `(equ ,func ,ass) source))
	    else (push (make-eqn ass func nil source) $eqn-set))
	func))

(defun or-count (ass)
   ; Count the number of ors on the top level of a ass.
   (if* (equal (op-of ass) 'or) 
      then (+ 1 (or-count (first-arg ass)) (or-count (second-arg ass)))
      else 0))

(defun break-at-or (ass)
   ; Substitute a predicate for ass.
   ; We call process-ass to introduce a new constraining equation,
   ; and we return a value that should be used for the variable.
   ; If flag is true, then just return ass.
   (let ((args (flatten 'or (args-of ass))) 
	  func term asses vars)
      (sloop while (> (length args) 4) do
            (setq term (pop args)
                  vars (var-list term))	  
            (sloop for i from 1 to 2 do
               (setq term (list 'or term (car args))
                     vars (intersection vars (var-list (pop args)))))
	    (setq func (make-term (gennewsym $func-name) vars))
  	    (set-arity (op-of func) (length vars))
	    (push `(equ ,term ,func) asses)
   	    (push-end func args))

      (setq term (pop args))
      (sloop for arg in args do (setq term (list 'or term arg)))
      (push term asses)

      (terpri) (princ "Following assertion") (terpri) (princ "    ")
      (write-term ass) (terpri) 
      (setq asses (reverse asses))
      (princ "    is broken into") (terpri)
      (sloop for xa in asses do (princ "    ") (write-term xa) (terpri))
      (terpri)
      asses))

(defun trivial-simplify (ass)
  (if* (variablep ass) then ass else
   (caseq (op-of ass)
    (equ (if* (truep (first-arg ass))
	    then (second-arg ass)
          elseif (truep (second-arg ass))  
	    then (first-arg ass)
	    else ass))
;    (xor (if* (truep (first-arg ass))
;	    then `(not ,(second-arg ass))
;          elseif (truep (second-arg ass)) 
;	    then `(not ,(first-arg ass))
;	    else ass))
    (not (if* (variablep (first-arg ass)) then ass else
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
  (if* pred then
      (caseq (op-of pred)
	(false '(true))
	(true '(false))
	(xor (negate-xor-args (args-of pred)))
	(t (m-xor-m pred '(true))))
      else '(false)))

(defun negate-xor-args (args)
  ;; accept a list of terms
  ;; return a term, NOT a list of terms.
  (if* (member0 '(true) args) then
      (setq args (remove0 '(true) args 1))
      (if* (null args) then '(false)
	  elseif (cdr args) then (make-term 'xor args) 
	  else (car args))
      else
      (m-xor-p '(true) (cons 'xor args))))

;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

;#+franz (include "datamacs.l")
;#-franz (in-package "USER")


; ********WARNING*********
; *****Parental guidance suggested for children under the age of 17*********
; ********WARNING*********

(defun skolemize (ass &optional sign)
  ; Remove all quantifiers of ASS. Take special care of "equ" and "xor".
  (caseq (op-of ass)
    ((all exist) (skolemize (skolemize-away-quants ass ass sign) sign))
    (equ (let ((a1 (sloop for xa in (args-of ass)
			     if (have-common (all-ops xa) '(exist all))
			       return xa)) a2)
	   (if* a1 then 
	       (setq a2 (remq a1 (args-of ass))
		     a2 (if* (cdr a2) then (make-term 'xor a2) else (car a2)))
	       (remove-quan-args `(and (-> ,a1 ,a2) (-> ,a2 ,a1)) sign)
	       else
	       (remove-quan-args `(xor (true) . ,(args-of ass)) sign))))
    (xor (let ((a1 (sloop for xa in (args-of ass)
			     if (have-common (all-ops xa) '(exist all))
			       return xa)) a2)
	   (if* a1 then 
	       (setq a2 (remq a1 (args-of ass))
		     a2 (if* (cdr a2) then (make-term 'xor a2) else (car a2)))
	       (if* (equal a2 '(true)) then
		   `(xor (true) ,(skolemize a1 (not sign)))
		   else
		   (remove-quan-args `(not (and (-> ,a1 ,a2) (-> ,a2 ,a1))) (not sign)))
	       else
	       (remove-quan-args ass sign))))
    (->  `(-> ,(skolemize (first-arg ass) (not sign))
              ,(skolemize (second-arg ass) sign)))
    (not `(not ,(skolemize (first-arg ass) (not sign))))
    ((and or) (remove-quan-args ass sign))
    (t ass)))

(defun remove-quan-args (ass sign)
  ; remove the quantifiers from the arguments of ass.
  (make-term (op-of ass) 
	     (sloop for xa in (args-of ass) 
		   collect (skolemize xa sign))))

(defun skolemize-away-quants (ass whole-ass sign)
   ; Remove the leading quantifiers from ass by introducing a skolem 
   ; function or a skolem variable.
   (let ((quant (op-of ass)) (var (first-arg ass)) (form (second-arg ass))
	 newvar)
    (if* (eq sign (eq quant 'exist))  
	then (setq newvar (make-new-variable var))
	     (if* (assoc var $var-type-list) then
		 (push (cons newvar (cdr (assoc var $var-type-list))) $var-type-list))
	else (setq newvar (get-sko-func var form whole-ass)))
    (setq form (special-subst newvar var form))
    (if* (quantifierp (op-of form)) 
	then (skolemize-away-quants form whole-ass sign)
	else form)))

(defun special-subst (new old form)
  (cond ((variablep form) 
	 (if* (eq form old) then new else form))
        ((memq (op-of form) `(exist all))
	 (if* (eq (first-arg form) old) 
	    then form
	    else (list (op-of form) (first-arg form)  
		       (special-subst new old (second-arg form)))))
	(t (make-term (op-of form)
		      (sloop for xa in (args-of form)
			  collect (special-subst new old xa))))))

(defun subst-quant-form (func ass source &aux l1)
    (setq l1 `(-> ,ass ,func))
    (process-ass2 `(-> ,(skolemize-away-quants ass l1 t) ,func) source)
    (setq l1 `(-> ,func ,ass))
    (process-ass2 `(-> ,func ,(skolemize-away-quants ass l1 nil)) source))

(defun hasquant (ass)
  ; Determine whether a formula has any quantifiers.
    (cond ((variablep ass) nil)
	  ((quantifierp (op-of ass)) t)
          (t (sloop for xa in (args-of ass) thereis (hasquant xa)))))

(defun get-sko-func (var ass whole-ass) 
    ; Given that we have to introduce a skolem function to replace var in
    ; ass, figure out what that function should be.
    (let ((op (gennewsym 's)) (args (remonce var (free-vars ass))))
	(set-arity op (length args))

	(if* (assoc var $var-type-list) then
	    (set-arity2 op 
			(cons (cdr (assoc var $var-type-list))
			      (sloop for xa in args 
				    collect (if* (setq xa (assoc xa $var-type-list))
						then (cdr xa)
						else 'univ)))))
	(set-skolem op)
	(setq args (make-term op args))
	(if* (> $trace_flag 1) then
	    (terpri) (princ "  Introducing") (display-one-arity2 op)
	    (princ "  ") (write-term args)
	    (princ " is a skolem function for ") (princ var) 
	    (terpri) (princ "     in the assertion: ") 
	    (write-term whole-ass) (terpri))
	args))
