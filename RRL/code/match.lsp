;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-

#+franz (include "datamacs.l")
#-franz (in-package "USER")

;; non-AC match and unify. written sharing most of the code
;; and to do well in failure cases. -- Siva DEC 4 1989.
;; No loops/setq/globals etc. just mapcar and tail recursion.
;; a matching/unification routine that uses mapcar & throw
;; checking conflicts at the end. 

;; will gain if failure due to fn-symbol clash occurs often.
;; first decompose into equations with one side a variable and
;; then resolve sunstitutions.

;; (defmacro fail-uni-match() `(throw '*unimatch* nil))

(defmacro add-bind-to-sub (v1 t1 sub)
     `(cons (cons ,v1 ,t1) ,sub))

;; takes two terms and returns list of equations with 
;; lhs a variable
;; throws away trivial eqns like (x x) for unification. 
;; detects symbol clash.
;; flag can be 'match or 'unify. in unify vars in rhs are also
;; made into equations.
;;
(defun decompose-terms (t1 t2 ans flag)
  (cond ((var? t1) (let ((cval (assq t1 ans)))
		     (case flag
			   (match (if* cval (if* (equal t2 (cdr cval)) ans 'fail)
				    (add-bind-to-sub t1 t2 ans)))
			   (unify (if* (eq t1 t2) ans
				    (if* cval (decompose-terms (cdr cval) t2 ans flag)
				     (add-bind-to-sub t1 t2 ans)))))))
	((var? t2) (case flag
			 (match 'fail)
			 (unify (decompose-terms t2 t1 ans flag))))
	((and (same-op? t1 t2) (= (length t1) (length t2)))
	    (sloop for xa in (args-of t1)
		  as  ya in (args-of t2)  
                  while (not (eq (setq ans (decompose-terms xa ya ans flag)) 'fail))
			finally (return ans)))
	(t 'fail)))

;; to give answer in normal form for unification. and do occurs check.
;;;;; first occur-check and then re-sub
(defun normal-form-sub (sub ans)
  (if* sub
     ;; occur-check here
      (let ((v1 (caar sub))
	    (t1 (applysubst ans (cdar sub))))
	(if* (occurs-in v1 t1) nil
	  (normal-form-sub (cdr sub) (cons (cons v1 t1)
					   (applysubst (list (cons v1 t1)) ans)))))
    ans))

;;
;; match and unify now easily defined below.
;; We can call either match or unify with some variables already bound
;; in binds.


;; unify t1 & t2 in the context binds.
(defun nonac-unify (t1 t2 &optional binds)
  (if* (eq binds *empty-sub*) (setq binds nil))
  (let ((ans1 (decompose-terms t1 t2 binds 'unify)))
    (if* (eq ans1 'fail) nil
      (if* ans1 (normal-form-sub ans1 nil) *empty-sub*))))

;; these calls the way RRL uses.

(defun match (t1 t2 &optional sigma)
  (if* (eq sigma *empty-sub*) (setq sigma nil))
  (let ((ans (decompose-terms t1 t2  sigma 'match)))
    (if* (eq ans 'fail) nil (or ans *empty-sub*))))

(defun pure-match (t1 t2 &optional sigma) 
  (if* (eq sigma *empty-sub*) (setq sigma nil))
  (let ((ans (decompose-terms t1 t2  sigma 'match)))
    (if* (eq ans 'fail) nil (or ans *empty-sub*))))
;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

;;
;; NON-AC match & unify are now in  uni-match.lsp -- Siva.
;;
;; this contains only AC-match, Bool-match and some top-level calls. 
;;                           - dec 1989

;#+franz (include "datamacs.l")
;#-franz (in-package "USER")


;;; had to change a lot of eq to = for comparing numbers.
;;; seems to be a problem in common lisp compile vs interpreted. -- siva.

; Normalization routines  should only use the function
; applies with arguments (lhs rule) and the term to be rewritten
; applies will return nil or a sigma .

;-- This file has matching functions for non-ac , ac and commutative matching.
;-- No Franz/Zeta problems here as only common functions are used.
;-- The only function in this file that other files really need is
;-- applies though now match , cmatch etc are used in normalization.

#+franz
(declare (special $inter-range $eq-length))

(setq $inter-range nil ; if $inter-range is on, then compute
		       ; the intersection of the ranges of the same variable.
      $eq-length nil) ; if $eq-length is on and the partten and objects have
		      ; the same length, then process them first.

(defmacro poly-sigma (sigma) `(if* poly (cdr ,sigma) ,sigma))
(defmacro insert-poly-sigma (new sigma)
  `(if* poly 
       (if* (car ,sigma)
	   (nconc (list (car ,sigma) ,new) (cdr ,sigma))
	   (nconc (list *empty-sub* ,new) (cdr ,sigma)))
       (cons ,new ,sigma)))

(defmacro good-luck-condi (sigma condi)
  `(if* (or (null ,condi) 
	   (sloop for va in (car ,condi) thereis (not (assq va ,sigma))))
       then t 
       elseif $polynomial
       then (poly-cycle-luck (applysubst sigma (cadr condi)) (caddr condi))
       else (premises-are-true (subst-premises sigma (cdr ,condi)))))

(defun applies (t1 t2 &optional condi sigma)
  (if* (eq condi 'fail) then nil
      elseif (or $ac $commutative condi)
      then (and (match-poss t1 t2)
		(ac-match (ncons (list t1 t2 (null $ac))) sigma condi))
      else (match t1 t2 sigma))
  )

(defmacro acm-variable (triples)
  ; the first term of triple is a variable.
  `(if* (assq first (poly-sigma sigma))
       then (if* (equal second (cdr (assq first (poly-sigma sigma))))
		then (ac-match ,triples sigma condi poly)
		else nil)
       else 
       (ac-match ,triples (insert-poly-sigma (cons first second) sigma) condi poly)))
  
(defmacro acm-and-eq (triples)
  ; Similar to acm-no-arg and acm-ac-root.
  (let ((pi1 (gensym)))
    `(let (,pi1)
       ; t1 and t2 are "and"-rooted or "eq"-rooted terms.
       (if* (null (args-of first)) 
	then (if* (null (args-of second)) 
		 then (ac-match ,triples sigma condi poly)
		 else
		 (ac-match ,triples
			   (insert-poly-sigma 
			     (cons (if* (eq (op-of first) 'eq)
				       then '*eq-rest-args
				       else '*and-rest-args)
				   (args-of second))
			     sigma)
			   condi poly))
	else 
	(setq ,pi1 (second first))
	; plausibility comes here.
	(sloop with ans = nil
	      for sj in (args-of second)
	      if (match-poss ,pi1 sj)
		do (if* (setq ans
			     (ac-match (cons (list ,pi1 sj t)
					     (cons (list (remove0 ,pi1 first 1)
							 (remove0 sj second 1) nil)
						   ,triples)) 
				       sigma condi poly))
		       (return ans)) 
	      finally (return nil))))))
  
(defmacro acm-one-var (triples)
  ; the first term in triple is of form f(x), where f is ac and x is 
  ; free in sigma and the third element of triple is t.
  `(ac-match ,triples
	     (insert-poly-sigma 
	       (cons (first-arg first) (if* (cddr second) second (first-arg second)))
	       sigma)
	     condi poly))

(defmacro acm-poly-* (triples)
  `(poly-match-* first second sigma condi ,triples))

(defmacro acm-poly-one-to-many (triples)
  `(poly-match-one-to-* first second sigma condi ,triples))

(defmacro acm-nonac (triples)
  ; Non-ac operator terms in triple.
  `(if* (match-poss first second) 
       (ac-match (nconc (sloop for xa in (args-of first)
			      as ya in (args-of second) 
			      collect (list xa ya t))
			 ,triples)
		 (if* (or (null poly) (car sigma))
		     sigma
		     (cons *empty-sub* (cdr sigma)))
		 condi poly)))

(defmacro acm-no-arg (triples)
  ; the first term in triple has no arguments.
  `(if* (null (args-of (second triple))) 
       then (ac-match ,triples sigma condi poly)
       elseif (third triple) then nil 
       else
       (ac-match ,triples (insert-poly-sigma (cons '$extra (second triple)) sigma)
		 condi poly)))

(defmacro acm-ac-root (triples)
  (let ((full (gensym)) (fast-match (gensym))
	(pi1 (gensym)) (occ (gensym)) (ans (gensym)))
    `(let ((,full (third triple)) ,fast-match ,pi1 ,occ ,ans)
       ; first and second are rooted by the same ac-op.
       ; if first has too many arguments, then using efficient and incomplete 
       ; matching algorithm.
       (setq ,fast-match (> (length (args-of first)) $many-args)
	     ,pi1 (pick-an-arg (args-of first) (poly-sigma sigma))
	     ,occ (occur-num ,pi1 first))
       (if* (and (variablep ,pi1) (assq ,pi1 (poly-sigma sigma)))
	   then (setq second (elim-bin ,pi1 (poly-sigma sigma) ,occ second))
	   (if* second (ac-match (cons (list (remove0 ,pi1 first ,occ) second ,full) ,triples)
				sigma condi poly))
	   elseif ,fast-match 
	   then
	   (sloop for sj in (args-of second)
		 if (and (match-poss ,pi1 sj)
			 (>= (occur-num sj second) ,occ)
			 (setq ,ans (ac-match (ncons (list ,pi1 sj t)) sigma condi poly)))
		   return
		     (ac-match (cons (list (remove0 ,pi1 first ,occ)
					   (remove0 sj second ,occ) ,full) ,triples)
			       ,ans condi poly))
	   else ; plausibility and canonicalization come here
	   (sloop for sj in (args-of second)
		 if (and (match-poss ,pi1 sj)
			 (>= (occur-num sj second) ,occ)
			 (setq ,ans (ac-match 
				      (append (list (list ,pi1 sj t)
						    (list (remove0 ,pi1 first ,occ)
							  (remove0 sj second ,occ) ,full))
					      ,triples)
				      sigma condi poly)))
		   return ,ans
		 finally (return nil))))))

(defun ac-match (triples sigma condi &optional poly)
  ; Match T1 with T2, return a sigma when T1 and T2 are matchable.
  ; Called by applies when some operators are ac or commutative.
  ; When no commutative operators, the same as match, however less efficient.
  ;
  ;    triples = {<pattern subject full>} 
  ; If full is nil then partial-match + $extra, else full-match.
  ; Non-variable subterms are given priority when they are arguments of 
  ; an ac operator.  
  ;
  (if* (eq sigma *empty-sub*) (setq sigma nil))
  (if* (null triples) 
      then (and (or (null condi)
		    (good-luck-condi sigma condi))
		(or sigma *empty-sub*))
      else
      (sloop for triple in triples do
	    (let ((first (first triple))
	          (second (second triple)))
	    (if* (variablep first) then
	      (return (acm-variable (remq triple triples 1)))
	    elseif (variablep second) then
		   (return nil)
	    elseif (not (same-op first second)) then
		   (return (if* (and poly (eq (op-of second) '*))
			      (acm-poly-one-to-many (remq triple triples 1))))
	    elseif (memq (op-of first) '(eq and)) then
		   (return (acm-and-eq (remq triple triples 1)))
	    elseif (not (ac-c-root first))
		   then (return
		     (if* (and poly (eq '* (op-of first)))
			 (acm-poly-* (remq triple triples 1))
			 (acm-nonac (remq triple triples 1))))
	    elseif (> (length first) (length second))
		   then (return nil)
	    elseif (null (args-of first))
		   then (return (acm-no-arg (remq triple triples 1)))
	    elseif (and $eq-length (= (length first) (length second)))
		   ; if $eq-length is on and the partten and objects have
		   ; the same length, then process them first.
		   then (return (acm-ac-root (remq triple triples 1)))
	    elseif (sloop for arg in (args-of first)
			  thereis (or (nonvarp arg) (assq arg (poly-sigma sigma))))
		   then (return (acm-ac-root (remq triple triples 1)))
	    elseif (and (third triple) (= (length first) 2))
		   then (return (acm-one-var (remq triple triples 1)))))
	    finally (return (vars-only triples sigma condi poly)))))

(defun match-poss (t1 t2)
    (cond ((variablep t1) t)
	  ((variablep t2) nil)
	  ((same-op t1 t2) 
	   (cond ((ac-root t1) (<= (length (cdr t1)) (length (cdr t2))))
		 ((and $polynomial (eq (op-of t1) '*))
		  (<= (length (cdr t1)) (length (cdr t2))))
		 ((memq (op-of t1) '(eq and)) t)
		 ((memq (op-of t1) $commutative)
		  (or (and (match-poss (first-arg t1) (first-arg t2))
		           (match-poss (second-arg t1) (second-arg t2)))
		      (and (match-poss (first-arg t1) (second-arg t2))
		           (match-poss (second-arg t1) (first-arg t2)))))
		 (t (sloop for xa in (args-of t1)
			as ya in (args-of t2) always (match-poss xa ya)))))
	  (t (and $polynomial (neq (op-of t1) '+) (eq (op-of t2) '*)))))

(defun pick-an-arg (args1 sigma)
  ; Pick a non-variable pattern, since that is most likely to 
  ; cause failure.
  (sloop for arg in args1
	if (nonvarp arg) return arg
	else if (assq arg sigma) return arg
	finally (return (first args1)))) ; In this case, |args1| = |args2| .

(defun vars-only (triples sigma condi poly &aux l1 op var range occ)
   ; for each triple in triples, the first element of triple
   ; is of form f(x1, x2, ..., xn) where f is ac and xi are free 
   ; in sigma.
   (setq l1 (first triples)
	 op (op-of (first l1)) 
	 var (first-arg (first l1))
	 occ (occur-num var (first l1))
	 range (divided-by (args-of (second l1)) occ)
	 l1 (1+ (quotient (diff (length (second l1))
				  (length (first l1))) occ)))
    (if* $inter-range then
	; If var is non-linear, then computing the ranges of 
 	; var at other occurrences and taking the intersection
	; of those ranges as the range of var.
	; If var is linear, then get-intersection-range has no effect.
	(setq range (get-intersection-range op var range l1 (cdr triples))
	      l1 (pop range)))

    ; now for one var we know what all is possible. just step through these,
    ; plausibility and canonicalization come here.
    (if* range then
	(sloop with prev-choice = '(0) 
	      with ans = nil 
	      with term
	      with prev-term = nil
	      for result = (next-choice range l1 prev-choice op)
	      if result 
		do 
		  (setq prev-choice (first result)
			term (second result))
		  (if* (nequal term prev-term) then
		      (setq prev-term term
			    ans (insert-poly-sigma (cons var term) sigma))
		      (if* (setq ans (ac-match triples ans condi poly))
			  then (return ans)))
	      else return nil)))
		   
(defun get-intersection-range (op var range max-size triples)
  ; If var is non-linear, then compute the ranges of 
  ; var at other occurrences and return the intersection
  ; of those ranges as the range of var.
  ; If var is linear, then get-intersection-range has no effect.
   (sloop with tmp = nil 
	for triple in (cdr triples) 
	as pat = (first triple)
	as subj = (second triple) 
	if (memq var pat) do
      (if* (neq op (op-of pat))
	then (setq max-size 1
		   range (sloop for arg in (args-of subj)
				if (or (member0 arg range)
				       (and (nonvarp arg) 
					    (eq op (op-of arg)))) 
			  	collect arg ))
	elseif (lessp (setq tmp (diff (length subj) (length pat)))
		      max-size)
	then (setq max-size (1+ tmp)))
      (if* (null (setq range (sloop for term in range 
			if (member0 term (args-of subj)) 
			collect term))) 
	(return nil))
	finally (return (cons max-size range))))
	      
(defun next-choice (range max-size prev-choice op)
    (let ((n (length range)) ans)
	 (setq ans (increment-pos prev-choice max-size n))
	 (if* ans then
	    (list ans
	          (if* (= 1 (length ans))
			then (nthelem (car ans) range)
			else (cons op (sloop for term in range as i from 1
					  if (memq i ans) collect term)))))))

(defun increment-pos (pos max choices)
  (sloop for p in pos
        as res on pos 
	as j from 1
	as i downfrom choices to 1
	if (< p i) return (append (con1-nums j p) (cdr res))
	finally (return (if* (< (length pos) max)
			  then (sloop for i downfrom (1+ (length pos)) to 1
				     collect i)))))

(defun divided-by (lis n)
  (if* (= n 1) then lis else 
     (sloop for m in (mult-form lis) append 
		(sloop for xa from 1 to (quotient (cdr m) n) 
			collect (car m)))))

(defun occur-num (xa lis)
  ; return # of xa in lis.
  (sloop with n = 0 for xb in lis if (equal xb xa) 
	do (setq n (1+ n))
	finally (return n)))

(defun elim-bin (var sigma num term)
  ; removes sigma(var) from term.
  ; If sigma(var) has the same ac-root as term, then only arguments of
  ; sigma(var) are removed.  
  ; If no sigma(var) in term, return nil, otherwise return term - sigma(var).
  (let ((bin (cdr (assq var sigma))))
    (if* (nonvarp bin) 
	then (if* (and (ac-root bin) (same-op bin term))
		then (rem-args (args-of bin) term num)
		elseif (>= (occur-num bin term) num)
		then (remove0 bin term num))
	elseif (>= (occur-num bin term) num)
	then (remq bin term num))))

(defun rem-args (args term num)
  ; return "term" - n times "args" if n times "args" are in "term".
  (sloop for arg in args
	 if (>= (occur-num arg (args-of term)) num)
	 do (setq term (remove0 arg term num))
	 else return nil
	 finally (return term)))
    
(defun member-term (term terms)
   (sloop for xa in terms thereis (and (match xa term) (match term xa))))

(defun is-an-instance (t1 lis)
   ; Returns "true" iff t1 is an instance of a term of "lis".
   (sloop for xa in lis thereis (applies xa t1)))


;; Following are functions used in normbool.l

(defun match-set (t1 t2 &optional fast-flag condi)
  (if* (or $ac $commutative)
      then (match-set-ac t1 t2 condi)
      else (match-set-nonac (args-of t1) (args-of t2) fast-flag condi)))

(defun match-set-ac (t1 t2 condi &aux sigma rest)
  ; Here t1 = and(ARGS1) and t2 = and(ARGS2). 
  ; Find a subset of ARGS1 say ARGS11 that matches ARGS2. 
  ; Return ((ARGS1 - ARGS11) . substition) if the matching exists.
  ; Return NIL otherwise. 
  ; AC-match are used since some operators are already commutative.
  (if* (setq sigma (ac-match (ncons (list t1 t2 nil)) nil condi)) then 
	  (setq rest (assq (caseq (op-of t1)
				(eq '*eq-rest-args)
				(and '*and-rest-args)) sigma))
	  (if* rest then (setq sigma (delete0 rest sigma)
			      rest (cdr rest)))
	  (cons rest sigma)))

(defun match-set-nonac (args1 args2 fast-flag condi &optional bind)
   ; Find a subset of ARGS1 say ARGS11 that matches ARGS2. 
   ; Return ((ARGS1 - ARGS11) . substition) if the matching exists.
   ; Return NIL otherwise.
   (prog ((t1 (pop args1)) t2 newbind result args22)
        loop-here
        (sloop while t do
	    (if* (null (setq t2 (pop args2))) 
		then (return nil)
	        elseif (and $false-rhs (nonvarp t1) (eq (op-of t1) 'eq)
			    (setq newbind (eq-match t1 t2 bind condi)))
		then (return nil)
	        elseif (setq newbind (match t1 t2 bind))
		then (return nil)
	        else (setq args22 (append args22 (ncons t2)))))
        (if* (null t2) then (return nil)
	    elseif (null args1)
	    then (return (cons (append args22 args2) newbind))
	    elseif (setq result 
			  (match-set-nonac 
			    args1 
			    (if* fast-flag then args2 else (append args22 args2))
			    fast-flag condi newbind))
	    then (if* fast-flag then
		     (rplaca result (append args22 (car result))))
      	         (return result)
	    else (setq args22 (append args22 (ncons t2)))
	 	 (go loop-here))))

(defun match-bool-xor (args1 args2 &optional fast-flag bind rest condi)
   ; Return (rest-of-xor-args rest-of-and-args . substitution) if the matching exists.
   ; Return NIL otherwise.
   (prog ((t1 (pop args1)) t2 newbind
	  newrest not-as-rest rest-collection
	  result args22 old-args2 match-bool-res continue-with-current-t2)
        loop-here
        (sloop while t do
	    (if* (null (setq old-args2 args2
			    t2 (pop args2))) 
		then (return nil)
	        elseif (setq match-bool-res
			     (match-bool-new (half-canonicalize t1)
					     (half-canonicalize t2)
					     fast-flag bind rest not-as-rest
					     condi))
		;; match-bool-new returns a list of the form:
		;; (rest-of-args . subst)
		then (setq newrest (pop match-bool-res)
			   rest-collection (insert1 newrest rest-collection)
			   newbind match-bool-res)
		     (if* (null newrest) (setq newrest '(nil)))
		     (setq continue-with-current-t2 t)
		     (return nil)
		else (setq continue-with-current-t2 nil
			   args22 (append args22 (ncons t2)))))

        (if* (null t2) then (return nil)
	    elseif (null args1)
	    then (return (cons (append args22 args2) (cons rest newbind)))
	    elseif (setq result 
			  (match-bool-xor args1 
		  	       (if* fast-flag then args2
					     else (append args22 args2))
			        fast-flag newbind (or rest newrest)
				condi))
	    then (if* fast-flag then
		     (rplaca result (append args22 (car result))))
      	         (return result)
	    elseif continue-with-current-t2
	    then (setq args2 old-args2
		       not-as-rest rest-collection)	        
	         (go loop-here)
	    else (setq args22 (append args22 (ncons t2)))
	 	 (go loop-here))))

(defun match-bool-new (args1 args2 
			&optional fast-flag bind rest not-as-rest condi)
   ; Find a subset of ARGS1 say ARGS11 that matches ARGS2. 
   ; Return ((ARGS1 - ARGS11) . substition) if the matching exists.
   ; Return NIL otherwise.
   (prog ((t1 (pop args1)) t2 newbind result args22)
	 (if* rest
	     (if* (or (and (not (equal rest '(nil)))
			  (not (sloop for r in rest do
				 (if* (member0 r args2)
				     then (setq args2 (remonce r args2))
				     else (return nil))
				     finally (return t))))
		     (nequal (1+ (length args1)) (length args2)))
		 (return nil)))
        loop-here
        (sloop while t do
	    (if* (null (setq t2 (pop args2)))
		then (return nil)
	        elseif (setq newbind (match t1 t2 bind))
		then (return nil)
	        else (setq args22 (nconc args22 (ncons t2)))))
        (if* (null t2) then (return nil)
	    elseif (null args1)
	    then (return (and (not (member0 (setq args22 (append args22 args2)) not-as-rest))
			      (or (null rest) (null args22))
			      (cons args22 newbind)))
	    elseif (setq result 
			  (match-bool-new args1 
		  	       (if* fast-flag then args2
					     else (append args22 args2))
			        fast-flag newbind nil
				(sloop for r in not-as-rest
				      collect (remonce t2 r)) 
				condi))
	    then (if* fast-flag then
		     (rplaca result (append args22 (car result))))
      	         (return result)
	    else (setq args22 (append args22 (ncons t2)))
	 	 (go loop-here))))

; this function cannot be written as macro for symbolics.
(defun ac-c-root (term) (or (ac-root term) (comm-root term)))
(defun ctx-bad-luck (var sub sigma vars condi)
  (and condi
       (memq var vars)
       (sloop for va in vars always (or (eq va var) (assq va sigma)))
       (not (premises-are-true (subst-premises (cons (cons var sub) sigma) condi)))))

(defun eq-match (first second &optional sigma condi &aux poly)
  (if* (same-op first second) (acm-and-eq nil)))

; >>>>>>>>> 1/9/89
(defun match-premises (pres1 pres2 sigma)
  (if pres1 
      (sloop with first = (car pres1)
	     with new = nil
	     for pre in pres2
	     if (and (setq sigma (match-premise first pre sigma))
		     (setq new (match-premises (cdr pres1)
					       (remove0 pre pres2 1)
					       sigma)))
	     return new
	     finally (return nil))
    *empty-sub*))

(defun match-premise (pre1 pre2 &optional (sigma *empty-sub*))
  (and (setq sigma (match (car pre1) (car pre2) sigma))
       (if (cadr pre1)
	   (match (cadr pre1) (cadr pre2) sigma)
	 (truep (cadr pre2)))))
  