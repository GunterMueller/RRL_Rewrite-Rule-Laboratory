(in-package "USER")

;  This file contains various functions for representing terms and
;  useful operations on terms. The basic data-structure for a term is
;  just a list of 2 elements of the form (operator arguments) where
;  arguments may themselves be terms. We distinguish between variables
;  and non-variable terms as follows. A variable is an atom whose print-name
;  starts with u-z . A non-variable term, even of 0-arity is a list.
;  A non variable term is represented as (OP . ARGS).
;
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
;       operator:       operator of non-variable terms.
;       arguments:      arguments of terms.
;       variablep:      t if a variable term, otherwise nil.
;       nthsubt:        nth subterm of a non-variable term.
;       make-term:      make a term when given operator and arguments.
;       make-terms:     a list of terms made of given operator and given 
;                       arguments list.
;       nargs:          arity of root operator of a term.
;       applysubst:     substitute variables in a term.

(defmacro make-term (op arg) `(cons ,op ,arg))
(defmacro make-term-2arg (op arg1 arg2) `(list ,op ,arg1 ,arg2))
(defmacro op-of (term) `(car ,term))
(defmacro args-of (term) `(cdr ,term))
(defmacro variablep (term) `(numberp ,term))
(defmacro nonvarp (term) `(consp ,term))
(defmacro first-arg (term) `(cadr ,term))
(defmacro second-arg (term) `(caddr ,term))
(defmacro same-root (t1 t2) `(equal (car ,t1) (car ,t2)))
(defmacro nthsubt (n term) `(nth ,n ,term))
(defmacro make-terms (op args-list)
  `(sloop for args in ,args-list collect (make-term ,op args)))
(defmacro is-bool-root (term) `(and (listp ,term) (is-bool-op (op-of ,term))))
(defmacro is-rooted-+ (term) `(and (listp ,term) (equal (car ,term) *+*)))
(defmacro is-rooted-* (term) `(and (listp ,term) (equal (car ,term) $*$)))
(defmacro is-rooted-minus (term) `(and (listp ,term) (equal (car ,term) *-*)))

(defmacro falsep (ctx) `(equal *falseterm* ,ctx))
(defmacro not-falsep (ctx) `(not (falsep ,ctx)))
(defmacro truep (ctx) `(or (null ,ctx) (equal *trueterm* ,ctx)))

(defmacro applysubst (sigma term) 
  `(if (empty-sub ,sigma) ,term (sublis ,sigma ,term)))
(defmacro applysigma (sigma term) 
  `(if (empty-sub ,sigma) ,term (sublis ,sigma ,term)))

(defmacro ac-root (term) `(ac-op-p (op-of ,term)))
(defmacro ac-mt? (term) 
  `(and (nonvarp ,term) (ac-op-p (op-of ,term)) (equal (cadr ,term) 'm)))
(defmacro args-of-mt (term) `(cddr ,term))

(defmacro comm-root (term) `(comm-op-p (op-of ,term)))

;  Below we define various functions on terms:

;       op-list:        Returns the operator set of a term.
;       var-list:       Returns the variable set of a term.
;       var1-list:      Returns all variables (with duplicate) in a term.
;       size:           number of symbols in a term.

;       subtat:         subterm at specified position in a term.
;       replace-nth-arg:
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
;       is-constructor-term:   Returns t iff a term does not contain any 
;			non-constructor operators.
;       subs-are-constructor-term: 
;			Returns t iff the subterms of a term are constructor-term.
;	is-linear:	Returns t iff each variable in a term has only one
;			occurrence.
;	non-linear-vars: Returns all variables having more than once 
;			occurrence in a term.
;       crplnthsubt:    replaces nth top-level subterm by each  term in CLIST.

;  Returns the set of the operators in TERM.
(defun op-list (term &aux ops) 
  (cond ((variablep term) nil)
	((args-of term)
	 (setq ops (op-list (first-arg term)))
	 (dolist (xa (cddr term))
	   (dolist (op (op-list xa))
	     (unless (member op ops) (setq ops (cons op ops)))))
	 (if (member (op-of term) ops)
	     ops
	     (cons (op-of term) ops)))
	(t term)))

(defun all-ops-of (term)
  ; Returns a list of all variables (with duplicates) in TERM.
  (cond ((variablep term) nil)
	((args-of term)
	 (cons (op-of term) (mapcan #'all-ops-of (args-of term))))
	(t (ncons (op-of term)))))     


;  Returns a list of variables in TERM.
(defun var-list (term) (rem-dups (all-vars-of term)))

(defun all-vars-of (term)
  ; Returns a list of all variables (with duplicates) in TERM.
  (cond ((variablep term) (ncons term))
	((args-of term)
	 (mapcan #'all-vars-of (args-of term)))
	(t nil)))

#|
(defun var-list (term &aux stack vars)
  (cond ((variablep term) (ncons term))
	(t (setq stack (args-of term))
	   (while stack
	     (setq term (pop stack))
	     (if (variablep term) 
		 (query-insert term vars)
	       (if (args-of term)
		   (setq stack (append (args-of term) stack)))
	       ))
	   vars)))
|#

(defun all-vars2-of (term &aux stack vars)
  (cond ((variablep term) (ncons term))
	(t (setq stack (args-of term))
	   (while stack
	     (setq term (pop stack))
	     (if (variablep term) 
		 (push term vars)
	       (if (args-of term)
		   (setq stack (append (args-of term) stack)))
	       ))
	   vars)))

(defun vars2-list (term)
  (setq term (all-vars2-of term))
  (sloop for vars on term 
	 for i from 0 do
	 (sloop for j from (1+ i)
		for xj in (cdr vars)
		if (eq xj (car vars))
		return (setf (car vars) j)))
  term
  )

#|
(defun vars2-list (term)
  (setq term (all-vars2-of term))
  (sloop for xa in (cdr term) 
	 for i from 1 do
	 (sloop for j from 0 below i 
		if (eq xa (nth j term))
		return (setf (nth i term) j)))
  term
  )
|#

(defun is-ground (term)
  ; Returns a list of all variables (with duplicates) in TERM.
  (cond ((variablep term) nil)
	((args-of term) 
	 (every #'is-ground (args-of term)))
	(t t)))

(defun one-symbol-term (term op)
  ; return t iff the only nonconstant function symbol in term is op.
  (cond ((variablep term) t)
	((args-of term)
	 (and (eq (op-of term) op)
	      (sloop for arg in (args-of term)
		     always (one-symbol-term arg op))))
	(t t)))

(defun size (term)
  ; Returns the number of symbols in TERM (the size of TERM).
  (cond ((null term) 0)
	((variablep term) 1)
	(t (add1 (sum-up (mapcar 'size (args-of term)))))))

(defun w-size (term &aux l1)
  ; Returns the weighted size of TERM.
  (cond ;; ((null term) 0)
	((variablep term) 1)
	((null (args-of term)) 1)
	((is-skolem-op (op-of term)) 1)
	(t (setq l1 (assoc (op-of term) $f-weights))
	   (+ (if* l1 (cdr l1) 1)
	      (sum-up (mapcar 'w-size (args-of term)))))))

(defun kbo-size (term &aux l1)
  ; Returns the weighted size of TERM.
  (cond ((variablep term) 1)
	(t (setq l1 (assoc (op-of term) $f-weights))
	   (if (args-of term)
	       (+ (if l1 (cdr l1) 1)
		  (sum-up (mapcar 'kbo-size (args-of term))))
	     (if l1 (cdr l1) 1))
	   )))

(defun term-size-order (t1 t2) (not (greaterp (size t1) (size t2))))

(defun free-vars (term)
   ; Figure out what the free variables of a term are.
   (cond ((variablep term) (ncons term))
	 ((memq (op-of term) *exist*all*)
	  (delete0 (first-arg term) (free-vars (second-arg term))))
         ((args-of term) (rem-dups (mapcan #'free-vars (args-of term))))
	 (t nil)))

(defun subtat (pos term)
  ; Returns a subterm at position POS of term TERM.
  ; POS is a list of integers.
  ; Example: let T = F(G(X,Y), X)  (subtat (1 2) T) returns Y
  (when pos (sloop for i in pos do (setq term (nthsubt i term))))
  term)

(defun replace-nth-arg (n term arg)
  ;;  Replaces then Nth top-level subterm of TERM by T1.
  ;;; >>>>>>>>>>>>>>>>>>>>>>>>>.
  (when (or $ac $fopc) (setq term (copylist term)))
  (setf (nth n term) arg) 
  term)

(defun rplat-in-by (pos term t1)
  ;  Replaces the subterm at position POS in term TERM by T1.
  (when pos
    (setq term (copylist term)) ;; This copylist cannot be dropped.
    (setf (nth (car pos) term)
	  (rplat-in-by (cdr pos) (nth (car pos) term) t1))
    (setq t1 term))
  t1)
 
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
		    collect (make-term (op-of t1) 
				       (append args1 (ncons xa) args2)))))))

(defmacro order-vars (var1 var2)
  ;; Returns t if var1 is less or equal to var2.
  `(< ,var1 ,var2))

(defun rename-x-to-y (term)
  (cond ((variablep term) (rename-var-x-to-y term))
	((null (args-of term)) term)
	(t (make-term (op-of term) 
		      (mapcar #'rename-x-to-y (args-of term))))))

(defmacro nrename-x-to-y (term) `(change-var-in-term ,term (- *max-vars*)))
(defmacro nrename-y-to-x (term) `(change-var-in-term ,term *max-vars*))

(defun change-var-in-term (term delta)
  ;; Add delta to each variable in term. The input term is destroyed.
  (cond ((variablep term) (+ term delta))
	(t (sloop for arg in (args-of term)
		  for i from 1
		  do (setf (nth i term) (change-var-in-term arg delta)))
	   term)))

(defun new-vars (vars1 vars2)
  ;; Checking each v1 in VARS1, if v1 is also in vars2, then
  ;; replace x by a new variable which is not in VARS1 or in VARS2.
  (sloop for x in vars1 
	 if (memq x vars2)
	 collect (cons x (sloop for i from (upto-var 0)
				if (not (or (memq i vars1) (memq i vars2)))
				return i))))
(defun op-occur-in (op term)
  (cond ((variablep term) nil)
	((eq op (op-of term)) t)
	((sloop for arg in (args-of term)
		thereis (op-occur-in op arg)))))

(defun is-subt (t1 t2)
  ;  Returns t if T1 is a subterm of T2; otherwise, nil.
  (if (equal t1 t2) 
      t
     (sloop for arg in (args-of t2) thereis (is-subterm t1 arg))))
       
(defun is-subterm (t1 t2)
  ;  Returns t if T1 is a subterm of T2; otherwise, nil.
  (if* (equal t1 t2) then t
    elseif (or (variablep t2) (null (args-of t2))) then nil
    elseif (and (nonvarp t1) (same-root t1 t2) (ac-c-root t1) (is-subset t1 t2)) then t
    else (sloop for arg in (args-of t2) thereis (is-subterm t1 arg))))

(defun occurs-in (var term)
  (if (eq var term) t
      (if (variablep term)
	  nil
	  (sloop for arg in (args-of term) thereis (occurs-in var arg)))))

(defun is-sub-nonvar-term (t1 t2)
  ; return T iff t1 is a subterm of t2 without considering variables.
  (if* (variablep t2) then nil
      elseif (variablep t1) then t
      elseif (same-root t1 t2)
      then (if* (args-of t2) then
	       (sloop for arg1 in (set-diff (args-of t1) (args-of t2))
		     always (sloop for arg2 in (set-diff (args-of t2) (args-of t1))
				  thereis (is-sub-nonvar-term arg1 arg2))))
      else (sloop for arg2 in (args-of t2) thereis (sub-or-eq-term t1 arg2))))

(defun sub-or-eq-term (t1 t2)
  ; return T iff t1 is a subterm of t2 or equal to t2 without considering variables.
  (if* (variablep t1) then t
      elseif (variablep t2) then nil
      elseif (same-root t1 t2)
      then (sloop for arg1 in (args-of t1) 
		 always (sloop for arg2 in (args-of t2) 
			      thereis (sub-or-eq-term arg1 arg2)))
      else (sloop for arg2 in (args-of t2)
		     thereis (sub-or-eq-term t1 arg2))))

(defun depth (t1)
  ;  Returns the depth of "t1"
  (cond ((variablep t1) 0)
	((null (args-of t1)) 1)
        (t (add1 (apply 'max (mapcar 'depth (args-of t1)))))))

(defun is-limited (t1)
  ;  Returns "t" iff "t1" does not contain any non-contructor operator.
  (cond ((variablep t1) t)
        ((not (member (op-of t1) $limited-ops)) nil)
        ((args-of t1) (every #'is-limited (args-of t1)))
        (t t)))

(defmacro is-constructor-term (t1)
  `(progn (setq $limited-ops $constructors) (is-limited ,t1)))

(defun is-equal-limited (t1)
  (cond ((variablep t1) t)
        ((member (op-of t1) $limited-ops)
	 (deleten (op-of t1) $limited-ops 1)
         (every #'is-equal-limited (args-of t1)))
	(t nil)))

(defmacro has-same-ops (ops term)
  `(progn
     (setq $limited-ops ,ops)
     (and (is-equal-limited ,term) (null $limited-ops))))

(defun has-limited (t1)
  (cond ((variablep t1) nil)
        ((member (op-of t1) $limited-ops) t)
        ((args-of t1) (some #'has-limited (args-of t1)))
        (t nil)))

(defmacro has-limited-ops (ops t1) 
  `(progn (setq $limited-ops ,ops) (has-limited ,t1)))

(defmacro has-quantifier (t1) 
  `(progn (setq $limited-ops *exist*all*) (has-limited ,t1)))

(defmacro has-acop (t1) 
  `(progn (setq $limited-ops $ac) (has-limited ,t1)))

(defun constructor-subst (subst)
  ; Return t iff subst is a constructor substitution.
  (sloop for xa in subst always (is-constructor-term (cdr xa))))

(defun subs-are-constructor-term (t1)
  ;  Returns "t" iff the all subterms of "t1" are constructor-terms.
  (cond ((null (args-of t1)) t)
        (t (sloop for xa in (args-of t1) always (is-constructor-term xa)))))

(defun is-linear (term)
  ;  returns "t" iff  there is all variables have at least occurrence
  ;         once in "term".
  (null (non-linear-vars term)))

(defun non-linear-vars (term &aux global)
  ;  Returns a list of all variables which have more occurrences
  ;  than once in TERM.
  (sloop for var in (all-vars-of term) 
	 if (not (query-insert var global)) collect var))

(defun smaller-size (t1 t2) (lessp (size t1) (size t2)))

(defun literal-num (term &aux (op (op-of term)))
  (cond 
   ((eq op *eq*) (1- (length (args-of term))))
   ((or (eq op *xor*) (eq op *and*))
    (apply #'+ (mapcar #'literal-num (args-of term))))
   (t 1)))

(defmacro is-constant-term (term) 
  `(and (nonvarp ,term) (null (args-of ,term)))) 

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
	nconc (if (nonvarp xb) (type-all-vars xb) (ncons (cons xa xb)))))

(defun type-var-list (term)
  ; Return a list of two lists: one for the vars in term and the other for 
  ; their types.
  (if* (variablep term) then (list '(univ) (ncons term)) 
     elseif (setq term (rem-dups (type-all-vars term)))
     then (split-alist term)))

(defmacro args-of-same-root (op args) 
  `(nreverse (args-of-same-root1 ,op ,args)))

(defun args-of-same-root1 (op args &aux res)
  ; resturn all arguments under "op".
  (dolist (arg args)
    (setq res
	  (if (or (variablep arg) (neq op (op-of arg)))
	      (cons arg res)
	      (nconc res (args-of-same-root1 op (args-of arg))))))
  res)

(defun is-sorted-under-op (op args &optional first)
  ; resturn all arguments under "op".
  (sloop for arg in args do
	 (if (or (variablep arg) (neq op (op-of arg)))
	      (if (and first (nequal first arg) (not (total-term-ordering first arg)))
		  (return nil)
		  (setq first arg))
	      (if (null (setq first (is-sorted-under-op
				      op (args-of arg) first)))
		  (return nil)))
	 finally (return first)))

;    is-premise-set: return t if (eq (car (ctx eqn)) '&&).
(defmacro is-premise-set (ctx) `(and ,ctx (equal (car ,ctx) '&&)))
;    get-premises: return a list of premises without the mark.
(defmacro get-premises (pres) `(cdr ,pres))

(defmacro replace-term (new old term) 
  `(subst ,new ,old ,term :test #'equal))

(defun subpair (varlist termlist term)
  (if (not (equal (length varlist) (length termlist)))
      (break "Illegal args to subpair"))
  (sloop for v in varlist
	 as tm in termlist do
	 (setq term (replace-term tm v term))
	 finally (return term)))

(defun new-term (varl varr auto)
  ; Return a new term whose root symbol is new one and
  ; its arguments are the intersection of VARL and VARR.
  (setq varr (intersection varl varr)
	varl (create-new-operator (or $automatic auto) (length varr)))

  (if $automatic ;; new operator is less than any but constants.
      (sloop for op from *first-user-op* below $num-ops
	     if (and (not (is-prec-related op varl))
		     (or (is-constant-op varl) (not (is-constant-op op))))
	     do (add-sugg op varl)))

;  (if $automatic ;; new operator is less than any but constants.
;      (sloop for op from *first-user-op* below $num-ops
;	     if (not (is-prec-related op varl))
;	     do (if (is-constant-op op)
;		    (add-sugg varl op)
;		  (add-sugg op varl))))

  (make-term varl varr))

(defmacro is-ground3-term (term)
  ;; return t iff term is f(a, b) where a and b are constants and 
  ;; are not skolem-constants. 
  `(and
	(= (get-arity (op-of ,term)) 2)
	(is-constant-term (first-arg ,term))
	(not (member (op-of (first-arg ,term)) $skolem-ops))
	(is-constant-term (second-arg ,term))
	(not (member (op-of (second-arg ,term)) $skolem-ops))
	))

(defmacro all-ground3-terms (term)
  `(rem-dups (all-ground3-terms2 ,term)))

(defun all-ground3-terms2 (term)
  (if (variablep term) nil
    (if (is-ground3-term term) (ncons term)
      (mapcan #'all-ground3-terms2 (args-of term)))))
