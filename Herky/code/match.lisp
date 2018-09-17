(in-package "USER")

; Normalization routines  should only use the function
; applies with arguments (lhs rule) and the term to be rewritten
; applies will return nil or a sigma .

;-- This file has matching functions for non-ac , ac and commutative matching.
;-- No Franz/Zeta problems here as only common functions are used.
;-- The only function in this file that other files really need is
;-- applies though now match , cmatch etc are used in normalization.

(defmacro c-match (t1 t2) `(c-match1 (ncons ,t1) (ncons ,t2)))
(defmacro one-arg (term) `(null (cddr ,term)))
(defmacro single(list) `(null (cdr ,list)))

;(defvar $inter-range nil)
;; if $inter-range is on, then compute
;; the intersection of the ranges of the same variable.

;(defvar $eq-length nil) 
;; if $eq-length is on and the partten and objects have
;; the same length, then process them first.

(defmacro poly-sigma (sigma) `(if poly (cdr ,sigma) ,sigma))
(defmacro insert-poly-sigma (new sigma)
  `(if poly 
       (if (car ,sigma)
	   (cons (car ,sigma) (cons ,new (cdr ,sigma)))
	 (cons nil (cons ,new (cdr ,sigma))))
       (cons ,new ,sigma)))

#|
(defmacro good-luck-condi (sigma condi)
  `(if* (or (null ,condi) 
	   (sloop for va in (car ,condi) thereis (not (assq va ,sigma))))
       then t 
       elseif $polynomial
       then (poly-cycle-luck (applysubst sigma (cadr condi)) (caddr condi))
       else (premises-are-true (subst-premises sigma (cdr ,condi)))))
|#

(defun applies (t1 t2 &optional condi &aux sigma)
  (if* (eq condi 'fail) then nil
      elseif (or $ac $commutative)
      then (and (match-poss t1 t2)
		(ac-match (ncons (list t1 t2 (null $ac))) nil condi))
      else (and (setq sigma (match t1 t2 nil condi))
;		(or (null condi) 
;		    (premises-are-true (subst-premises sigma (cdr condi))))
		sigma)))

(defun match (t1 t2 &optional sigma condi)
  (if (empty-sub sigma) (setq sigma nil))
  (if* (variablep t1) 
      then
      ; add (t1 . t2) in sigma if that doesn't make sigma inconsistent.  
      (if* (assq t1 sigma) 
	  then (if* (equal t2 (cdr (assq t1 sigma))) then sigma else nil)
	  else (cons (cons t1 t2) sigma))
      elseif (not (variablep t2)) 
      then
      (if* (and (same-root t1 t2) (equal (length t1) (length t2))) then
	  (sloop with ans = sigma 
                for xa in (args-of t1)
		as ya in (args-of t2)
		if (setq ans (match xa ya ans condi)) do nil
		else return nil
		finally (return (or ans *empty-sub*))))))

(defun pure-match (t1 t2 &optional sigma)
  (if (empty-sub sigma) (setq sigma nil))
  (if* (variablep t1) 
      then
      ; add (t1 . t2) in sigma if that doesn't make sigma inconsistent.  
      (if* (assq t1 sigma) 
	  then (if* (equal t2 (cdr (assq t1 sigma))) then sigma else nil)
	  else (cons (cons t1 t2) sigma))
      elseif (not (variablep t2)) 
      then
      (if* (and (same-root t1 t2) (equal (length t1) (length t2))) then
	  (sloop with ans = sigma 
                for xa in (args-of t1)
		as ya in (args-of t2)
		if (setq ans (pure-match xa ya ans)) do nil
		else return nil
		finally (return (or ans *empty-sub*))))))

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
  ;; t1 and t2 are "and"-rooted or "eq"-rooted terms.
  `(if* (null (args-of first)) 
       then (if* (null (args-of second)) 
		 then (ac-match ,triples sigma condi poly)
		 else
		 (ac-match ,triples
			   (insert-poly-sigma 
			     (cons (if* (eq (op-of first) *eq*)
					then '*eq-rest-args
					else '*and-rest-args)
				   (args-of second))
			     sigma)
			   condi poly))
       else 
       ;; plausibility comes here.
       (sloop with ans = nil
	      with ri = (second first)
	      for sj in (args-of second)
	      if (match-poss ri sj)
		do (if* (setq ans
			     (ac-match
			       (cons (list ri sj t)
				      (cons (list (removen ri first 1)
						    (removen sj second 1) nil)
					     ,triples)) 
			       sigma condi poly))
			(return ans)) 
		finally (return nil))))
  
(defmacro acm-one-var (triples)
  ; the first term in triple is of form f(x), where f is ac and x is 
  ; free in sigma and the third element of triple is t.
  `(ac-match ,triples
	     (insert-poly-sigma 
	       (cons (first-arg first) (if (cddr second) second (first-arg second)))
	       sigma)
	     condi poly))

(defmacro acm-poly-* (triples)
  `(poly-match-* first second sigma condi ,triples))

(defmacro acm-poly-one-to-many (triples)
  `(poly-match-one-to-* first second sigma condi ,triples))

(defmacro acm-nonac (triples)
  ; Non-ac operator terms in triple.
  `(if (match-poss first second) 
       (ac-match (nconc (sloop for xa in (args-of first)
			       as ya in (args-of second) 
			       collect (list xa ya t))
			,triples)
		 (if (or (null poly) (car sigma))
		     sigma
		     (cons '(nil) (cdr sigma)))
		 condi poly)))

(defmacro acm-no-arg (triples)
  ; the first term in triple has no arguments.
  `(if* (null (args-of second)) 
       then (ac-match ,triples sigma condi poly)
       elseif (third triple) then nil 
       else
       (ac-match ,triples (insert-poly-sigma 
			   (cons '$extra second) sigma)
		 condi poly)))

(defmacro acm-ac-root (triples)
  (let ((full (gentemp)) (fast-match (gentemp)) (ri (gentemp)) (occ (gentemp))
	(ans (gentemp)))
    `(let ((,full (third triple)) ,fast-match ,ri ,occ ,ans)
       ; first and second are rooted by the same ac-op.
       ; if first has too many arguments, then using efficient and incomplete 
       ; matching algorithm.
       (setq ,fast-match (> (length (args-of first)) $many-args)
	     ,ri (pick-an-arg (args-of first) (poly-sigma sigma))
	     ,occ (occur-num ,ri first))
       (if* (and (variablep ,ri) (assq ,ri (poly-sigma sigma)))
	   then 
	   (setq second (elim-bin (cdr (assq ,ri (poly-sigma sigma))) ,occ second))
	   (if second (ac-match (cons (list (removen ,ri first ,occ) second ,full)
				      ,triples)
				sigma condi poly))
	   elseif ,fast-match 
	   then
	   (sloop for sj in (args-of second)
		 if (and (match-poss ,ri sj)
			 (>= (occur-num sj second) ,occ)
			 (setq ,ans (ac-match (ncons (list ,ri sj t)) sigma condi poly)))
		   return
		     (ac-match (cons (list (removen ,ri first ,occ)
					   (removen sj second ,occ) ,full) ,triples)
			       ,ans condi poly))
	   else ; plausibility and canonicalization come here
	   (sloop for sj in (args-of second)
		 if (and (match-poss ,ri sj)
			 (>= (occur-num sj second) ,occ)
			 (setq ,ans (ac-match 
				      (append (list (list ,ri sj t)
						    (list (removen ,ri first ,occ)
							  (removen sj second ,occ) ,full))
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
  (if (empty-sub sigma) (setq sigma nil))
  (if* (null triples) 
      then (or sigma *empty-sub*)
	    ; (or (null condi) (good-luck-condi sigma condi))
      else
      (sloop for triple in triples do
	    (let ((first (first triple))
	          (second (second triple)))
	 (if* (variablep first) 
 	    then (return (acm-variable (removen triple triples 1)))
	    elseif (variablep second) then
	    (return nil)
	    elseif (not (same-root first second)) then
	    (return (if (and poly (eq (op-of second) $*$))
			(acm-poly-one-to-many (removen triple triples 1))))
	    elseif (memq (op-of first) (list *eq* *and*)) then
	    (return (acm-and-eq (removen triple triples 1)))
	    elseif (not (ac-c-root first))
	    then (return
		   (if (and poly (eq $*$ (op-of first)))
		       (acm-poly-* (removen triple triples 1))
		       (acm-nonac (removen triple triples 1))))
	    elseif (> (length first) (length second))
	    then (return nil)
	    elseif (null (args-of first))
	    then (return (acm-no-arg (removen triple triples 1)))
	    elseif (and $eq-length (equal (length first) (length second)))
		   ; if $eq-length is on and the partten and objects have
		   ; the same length, then process them first.
	    then (return (acm-ac-root (removen triple triples 1)))
	    elseif (sloop for arg in (args-of first)
			  thereis (or (nonvarp arg) (assq arg (poly-sigma sigma))))
	    then (return (acm-ac-root (removen triple triples 1)))
            elseif (and (third triple) (null (cddr first)))
	    then (return (acm-one-var (removen triple triples 1)))))
	    finally (return (vars-only triples sigma condi poly)))))

(defun match-poss (t1 t2)
    (cond ((variablep t1) t)
	  ((variablep t2) nil)
	  ((same-root t1 t2) 
	   (cond ((ac-root t1) (<= (length (cdr t1)) (length (cdr t2))))
		 ((and $polynomial (eq (op-of t1) $*$))
		  (<= (length (cdr t1)) (length (cdr t2))))
		 ((memq (op-of t1) (list *eq* *and*)) t)
		 ((memq (op-of t1) $commutative)
		  (or (and (match-poss (first-arg t1) (first-arg t2))
		           (match-poss (second-arg t1) (second-arg t2)))
		      (and (match-poss (first-arg t1) (second-arg t2))
		           (match-poss (second-arg t1) (first-arg t2)))))
		 (t (sloop for xa in (args-of t1)
			   as ya in (args-of t2) always (match-poss xa ya)))))
	  (t (and $polynomial (neq (op-of t1) *+*) (eq (op-of t2) $*$)))))

(defun pick-an-arg (args1 sigma)
  ; Pick a non-variable pattern, since that is most likely to 
  ; cause failure.
  (sloop for arg in args1
	if (nonvarp arg) return arg
	else if (assq arg sigma) return arg
	finally (return (first args1)))) ; In this case, |args1| = |args2| .

(defun vars-only (triples sigma condi poly)
   ; for each triple in triples, the first element of triple
   ; is of form f(x1, x2, ..., xn) where f is ac and xi are free 
   ; in sigma.
  (if (and (null (cdr triples)) 
	   (null (cddr (first (car triples)))))
      ;; there is only one triple and the first part of the triple has
      ;; only one variable.
      (let* ((triple (car triples))
	     (first (first triple))
	     (second (second triple)))
	(acm-one-var nil))
      (let (l1 op var range occ)
	(setq l1 (first triples)
	      op (op-of (first l1)) 
	      var (first-arg (first l1))
	      occ (occur-num var (first l1))
	      range (divided-by (args-of (second l1)) occ)
	      l1 (add1 (quotient (diff (length (second l1))
				       (length (first l1))) occ)))
	(if* $inter-range then
	     ;; If var is non-linear, then computing the ranges of 
	     ;; var at other occurrences and taking the intersection
	     ;; of those ranges as the range of var.
	     ;; If var is linear, then get-intersection-range has no effect.
	     (setq range (get-intersection-range op var range l1 (cdr triples))
		   l1 (pop range)))
	
	;; now for one var we know what all is possible. just step through these,
	;; plausibility and canonicalization come here.
	(when range 
	  (sloop with prev-choice = nil
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
      ))
      
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
	then (setq max-size (add1 tmp)))
      (if (null (setq range (sloop for term in range 
			if (member0 term (args-of subj)) 
			collect term))) 
	(return nil))
	finally (return (cons max-size range))))
	      
(defun next-choice (range max-size prev-choice op &aux ans)
  (when (setq ans (increment-pos prev-choice max-size (length range)))
    (list ans
	  (if (cdr ans)
	      (cons op (sloop for xa in (reverse ans)
			      collect (nth xa range)))
	      (nth (car ans) range)))))

(defun increment-pos (pos max choices)
  (sloop for res on pos 
	 for p = (car res)
	 for j from 1
	 for i downfrom (1- choices) to 0
	 if (< p i) return (nconc (rev-con-nums (1+ p) (+ j p)) (cdr res))
	 finally (return (when (< (setq res (length pos)) max) 
			   (rev-con-nums 0 res)))))

(defun divided-by (lis n)
  (if (eq n 1) lis 
      (sloop for m in (mult-form lis) append 
	     (ntimes (quotient (cdr m) n) (car m)))))

(defun occur-num (xa lis)
  ; return # of xa in lis.
  (sloop with n = 0 for xb in lis if (equal xb xa) 
	do (setq n (add1 n))
	finally (return n)))

(defun elim-bin (bin num term)
  ; removes bin from term.
  ; If bin has the same ac-root as term, then only arguments of
  ; bin are removed.  
  ; If no bin in term, return nil, otherwise return term - bin.
  (if (nonvarp bin) 
      (if (same-root bin term)
	  (sloop for arg in (args-of bin)
		 if term
		 do (setq term (remove2 arg term num))
		 else return nil
		 finally (return term))
	  (remove2 bin term num))
      (remove2 bin term num)))
    
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
  (when (setq sigma (ac-match (ncons (list t1 t2 nil)) nil condi)) 
    (setq rest (assq (cond
		      ((eq (op-of t1) *eq*) '*eq-rest-args)
		      ((eq (op-of t1) *and*) '*and-rest-args)) 
		     sigma))
    (when rest
      (setq sigma (delete0 rest sigma)
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
	        elseif (and $false-rhs (nonvarp t1) (eq (op-of t1) *eq*)
			    (setq newbind (eq-match t1 t2 bind condi)))
		then (return nil)
	        elseif (setq newbind (match t1 t2 bind condi))
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
   ; Return (rest-of-xor-args rest-of-and-args . substitution)
   ; if the matching exists.
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
		     (neq (add1 (length args1)) (length args2)))
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

#|
(defun ctx-bad-luck (var sub sigma vars condi)
  (and condi
       (memq var vars)
       (sloop for va in vars always (or (eq va var) (assq va sigma)))
       (not (premises-are-true (subst-premises 
				(cons (cons var sub) sigma) condi)))))
|#

(defun eq-match (first second &optional sigma condi &aux poly)
  (if* (same-root first second) (acm-and-eq nil)))

; >>>>>>>>> 1/9/89
(defun match-premises (pres1 pres2 sigma)
  (if* pres1 
      (sloop with first = (car pres1)
	    for pre in pres2
	    if (and (setq sigma (match-premise first pre sigma))
		    (match-premises (cdr pres1)
				    (removen pre pres2 1)
				    sigma))
	    return t
	    finally (return nil))
    t))

(defun match-premise (pre1 pre2 &optional (sigma t))
  (and (setq sigma (match (car pre1) (car pre2) sigma))
       (match (cdr pre1) (cdr pre2) sigma)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The following functions come from distree.lisp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun init-var-bindings ()			
  ;; Make all variables unbound.  
  (setq $num-of-bound-vars 0)
  (sloop for i from 0 below *max-vars-all*
	 do (setf (aref (the (array t) $var-bindings) i) nil)))

#|
(defmacro var-binding (var)
  ;; Retrieve the binding of var.
  `(aref (the (array t) $var-bindings) (the fixnum ,var)))

(defmacro unbound-var? (var)
  ;; Is var an unbound var?
  `(null (var-binding ,var)))

(defmacro bound-var? (var)
  ;; Is var a bound var?
  `(var-binding ,var))

(defmacro set-binding (var term)
  ;; Set the binding of the variable represented by var to term.
  `(setf (var-binding ,var) ,term))

(defmacro set-var-binding (var term)
  ;; Set the binding of the variable represented by var to term.
  ;; and remember the var name.
  `(progn
     (setf (aref $bound-vars $num-of-bound-vars) ,var)
     (incf $num-of-bound-vars)
     (setf (var-binding ,var) ,term)))

(defmacro make-unbound-vars ()
  ;; Unlind all the bound vars. Return nil.
  `(while (> $num-of-bound-vars 0)
	  (decf $num-of-bound-vars)
	  (setf (aref $var-bindings
		      (aref $bound-vars $num-of-bound-vars))
		nil)))

(defmacro make-unbound-var (var)
  ;; Unbind a variable.
  `(setf (var-binding ,var) nil))

(defun var-match (t1 t2)
  ;; Match t1 and t2, assuming that indexing has already found their
  ;; structure compatible.
  (if (variablep t1) 
      (if (bound-var? t1) 
	  (if (equal t2 (var-binding t1)) 
	      t 
	    (make-unbound-vars))
	(set-var-binding t1 t2))
    (sloop for xa in (args-of t1)
	   as ya in (args-of t2)
	   if (not (var-match xa ya))
	   return (make-unbound-vars)
	   finally (return t))))

(defun distree-applysigma (term)
  (prog1
      (instantiate-term term)
    (make-unbound-vars)))

(defun instantiate-term (term)
  (cond ((variablep term) (var-binding term))
	((args-of term) 
	 (make-term (op-of term) 
		    (mapcar #'instantiate-term (args-of term))))
	(t term)))
|#

(defun clash-free-match (t1 t2 &optional sigma)
  ;; Assume the operators are compatible.
  (if (empty-sub sigma) (setq sigma nil))
  (if (variablep t1) 
      ; add (t1 . t2) in sigma if that doesn't make sigma inconsistent.  
      (if (assq t1 sigma) 
	  (if (equal t2 (cdr (assq t1 sigma))) sigma nil)
	  (cons (cons t1 t2) sigma))
    (sloop for xa in (args-of t1)
	   as ya in (args-of t2)
	   if (setq sigma (clash-free-match xa ya sigma)) do nil
	   else return nil
	   finally (return (or sigma *empty-sub*)))
    ))

(defmacro linear-clash-free-match (t1 t2)
  `(or (linear-clash-free-match-aux ,t1 ,t2) *empty-sub*))

(defun linear-clash-free-match-aux (t1 t2)
  ;; Assume the operators are compatible (i.e., clash-free)
  ;; and t1 is linear.
  (if (variablep t1) 
      (ncons (cons t1 t2))
    (sloop for xa in  (args-of t1)
	       as ya in (args-of t2)
	       nconc (linear-clash-free-match-aux xa ya))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; from substitution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains functions formerly in unify.
; These functions manipulate substitutions, mostly used in ac unification.

(defmacro cur-val (var a-list) `(or (cdr (assq ,var ,a-list)) ,var))

(defun size-flat-sigma (uni) 
  (if (empty-sub uni)
      (cons 0 uni)
      (sloop with sum = 0 with max = 0 with sigma = nil with y
	     for x in uni do
	     (setq y (make-flat (cdr x))
		   sigma (cons (cons (car x) y) sigma)
		   y (size y)
		   sum (+ sum y)
		   max (max max y))
	     finally (return (cons (+ sum max) sigma)))
      ))

(defmacro empty-sub (sub) `(eq ,sub *empty-sub*))

(defun compose (sub1 sub2)
  ; form the composition of the two substitutions, sub1(sub2)
  (if* (or (null sub1) (null sub2)) nil
      (if* (empty-sub sub2) sub1
	  (if* (empty-sub sub1) sub2
			  (nconc
			    (sloop for sub in sub2 collecting
				 (cons (car sub) (applysigma sub1 (cdr sub))))
			    sub1)))))

(defun compose1 (sub1 sub2)
  (sloop for xa in sub1
	if (not (assoc (car xa) sub2)) 
	do (setq sub2 (cons (cons (car xa) (applysigma sub2 (cdr xa))) sub2))
	finally (return sub2)))

; domain(sub1) intersect domain(sub2) == empty
; and sub1 and sub2 are valid. returns normal form of
; sub1 wrt sub2 .

(defun norm-sub (sub1 sub2)
  (sloop with bin for xb in sub1
	if (occurs-in (car xb) (setq bin (applysigma sub2 (cdr xb))))
	  return nil
	else collect (cons (car xb) bin) into new
        finally (return new)))

; domains non-intersecting as above returns composition
(defun comp1 (sub1 sub2)
  (sloop for sub in sub2
	if (and (setq sub (norm-sub (ncons sub) sub1))
		(setq sub1 (norm-sub sub1 sub))) 
	  do (nconc sub1 sub)
	else return nil
	finally (return sub1)))

; resolves 2 substitutions sigma1 and sigma2 . Returns
; all possible most-general sigma such that
;  sigma = sigma1 o phi1  and sigma = sigma2 o phi2

(defun resolve (sub1 sub2)
  (let ((l1 nil) (int nil) (d1 nil) (d2 nil))
    (setq l1 (sloop for sub in sub1
		   if (assoc (car sub) sub2) collect (car sub) into i1
		   else collect sub into i2
		   finally(return (cons i1 i2))))
    (setq d1 (cdr l1) int (car l1))
    (if* int then
	(setq d2 (sloop for sub in sub2
		       if (not (memq (car sub) int)) collect sub))
	(if* (and d1 d2) (setq d1 (comp1 d1 d2))
	    (setq d1 (or d1 d2)))
	(if* d1 then
	    (setq l1 (unicompound 
		       (sloop for x in int collect 
			      (applysigma d1 (cdr (assoc x sub1))))
		       (sloop for x in int collect 
			      (applysigma d1 (cdr (assoc x sub2))))))
	    (if* l1 
		(sloop with ans = nil
		      for sub in l1 
		      do (nconc sub
				(sloop for x in int 
				      collect (cons x (applysigma
							sub
							(cdr (assoc x sub1)) 
							))))
			 (setq ans (cons (compose sub d1) ans))
		      finally (return ans)))
	    else
	    (setq l1 (unicompound (sloop for x in int 
					collect (cdr (assoc x sub1)))
				  (sloop for x in int 
					collect (cdr (assoc x sub2)))))
	    (sloop for sub in l1
		  collect (nconc sub
				 (sloop for x in int 
				       collect
					 (cons x (applysigma 
						   sub (cdr (assoc x sub1))
						   ))))))
	else (ncons (comp1 sub1 sub2)))))

(defun compose2 (sub sublis)
  (if* sub (sloop for s1 in sublis
		collect (compose s1 sub)) sublis))

(defun apply-to2 (term sigma)
  ; takes flattened term, returns flattened substitued term
  ; sigma is already flattened.
  (cond
    ((variablep term) (or (cdr (assoc term sigma)) term))
    ((null (args-of term)) term)
    (t (let ((args (sloop for arg in (args-of term) 
			  collect (applysigma sigma arg))))
	 (compress-flat (op-of term) args)))))

(defun subst-eqnq (old new eqn)
  (setf (lhs eqn) (replace-term new old (lhs eqn))
	(rhs eqn) (replace-term new old (rhs eqn)))
  eqn)

(defun subst-eqn (old new eqn &optional (parents (eqn-source eqn))
		      &aux lhs rhs ctx) 
  (setq lhs (flat-term (replace-term new old (lhs eqn)))
	rhs (flat-term (replace-term new old (rhs eqn))))
  ;(setq ctx (replace-term new old (ctx eqn)))
  ;(if (nequal ctx (ctx eqn)) (setq ctx (remake-premises ctx)))
  (make-eqn lhs rhs ctx parents))

(defun applysubst-eqn (sigma eqn)
  (if (or $ac $commutative)
      (let ((lhs (flat-applysigma sigma (lhs eqn)))
	    (rhs (flat-applysigma sigma (rhs eqn)))
	    (ctx (flat-applysigma sigma (ctx eqn))))
	(make-eqn lhs rhs ctx (eqn-source eqn)))
      (let ((lhs (applysigma sigma (lhs eqn)))
	    (rhs (applysigma sigma (rhs eqn)))
	    (ctx (applysigma sigma (ctx eqn))))
	(make-eqn lhs rhs ctx (eqn-source eqn)))))

(defmacro applysubst-rule (sigma rule) `(applysubst-eqn ,sigma ,rule))



