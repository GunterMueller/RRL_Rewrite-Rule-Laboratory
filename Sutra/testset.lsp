;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "RRL")

#+franz (declare (special $possi-num $irredu-num))

(defun flatten-testset (flatten eqn)
  ; flatten each term in $testset. If two terms are unifiable after 
  ; flatten, then an inconsistency was found.
  (setq $testset (mapcar flatten $testset))
  (loop for terms on $testset do
    (loop with first = (car terms) 
	  for term in (cdr terms) 
	  if (unifier term first)
	    return (inconsistent-eqn eqn))))

(defun get-testset (ops &aux ops2)
  ; If OPS = $cons-of-ts, then the test set has been computed, we don't
  ; need to re-compute it. Otherwise, compute it and save OPS in
  ; $cons-of-ts.
  (if (nequal ops $cons-of-ts) then 
     (setq ops2 (remove 'true (remove 'false ops))
	   $testset (if (eq $prove-method 'q) 
			then (get-testset-quasi ops2)
			else (get-testset2 ops2))
           $testset (append '((true) (false)) $testset)
	   $type-testset (partition-term-by-type $testset)
	   $cons-of-ts ops)))

(defun get-testset2 (ops &aux time basic-terms l1 l2)
  ; Compute at first all schemes of OPS relative to the current
  ; rule set and the basic terms, then remove all quasi-reducible terms.
  (setq time #+franz (set-timer)
	     #-franz 0)
  (setq basic-terms (get-basic-type-terms ops))

  ; Compute the schemes of OPS and partition them into ground and non-ground
  ; sets L1 and L2.
  (loop for op in ops do
       (loop for term in (get-schemes op basic-terms) do
   	   (cond ((is-ground term) (push term l1))
		 (t (push term l2)))))

  (if (null l1)
     then ; No constant operators in the system. We put all L2 into test set.
	  (if (= $trace_flag 3) then (trace-add-testset l2 time)) l2
     else (if (= $trace_flag 3) then (terpri)
	   (princ (uconcat "Number of Candidates = " 
		 	   (+ (length l1) (length l2)))) (terpri))
	  (quasi-check l1 l2 t time)))

(defun get-schemes (op type-bases)
  ; Returns all schemes of OP. A term t is a schema of OP relative
  ; to the current system and the base operater F0 iff
  ;    1. The outermost operator of t is OP;
  ;    2. t is irreducible in the current system;
  ;    3. The variable-occurences of t are all out of the defining domain
  ;       of t while the non-variable-occurrence of t are inside of the
  ;       defining domain of OP.
  ;    4. The subterms of t are in T(F0, X).
  (let ((current (basic-term op))
	(def-domain (get-def-domain op)))
     (if (null (cdr def-domain))
	 then ;; No definition for OP, i.e., OP is free.
	      (ncons current)
	 else (extend-schemes current def-domain type-bases))))

(defun extend-schemes (current def-domain type-bases)
  ; Extend "current" as large as possible, according to "def-domain".
  ; An extension of a term is the term obtained by replacing a variable
  ; of the term by one element of "type-bases".
  ; Return all irreducible extended terms.
  (let ((candicates (ncons current)) schemes l1)
    (loop while candicates do
	(setq current candicates
	      candicates nil)
	(loop for xa in current 
	    if (not (reducible-time xa)) do
	       (if (setq l1 (get-down xa def-domain type-bases)) 
	          then (setq candicates (append candicates l1))
  	          else (push xa schemes))))
  (reverse schemes)))

(defun c-get-schemes (op type-bases)
  ; Returns all schemes with its complement condition of OP. 
  ; A term t is a schema of OP relative the current system and the 
  ; base operater F0 iff
  ;    1. The outermost operator of t is OP;
  ;    2. t is irreducible in the current system;
  ;    3. The variable-occurences of t are all out of the defining domain
  ;       of t while the non-variable-occurrence of t are inside of the
  ;       defining domain of OP.
  ;    4. The subterms of t are in T(F0, X).
  (let ((current (basic-term op))
	(def-domain (get-def-domain op)))
     (if (null (cdr def-domain)) 
	then (ncons current)
	else (c-extend-schemes current def-domain type-bases))))
     
(defun c-extend-schemes (current def-domain type-bases &aux ct)
  ; Extend "current" as large as possible, according to "def-domain".
  ; An extension of a term is the term obtained by replacing a variable
  ; of the term by a term in "type-bases".
  ; Return all irreducible extended terms.
  (let (schemes l1 (candicates (ncons current)))
    (loop while candicates do
      (setq current candicates
	    candicates nil)
      (loop for xa in current 
	    if (setq ct (not-cover-reducible xa))
	    do (if (setq l1 (get-down xa def-domain type-bases)) 
	        then (setq candicates (nconc candicates l1))
 		else (push (make-cterm xa ct) schemes))))
    (reverse schemes)))

(defun get-defining-domains (&aux l2 l3)
  ; Return a list of the defining domains for all operators of $operlist.
  (if (equal $constructors $cons-of-ts) 
      then $def-domains ; The defining domain does not changed.
      else
	(setq l2 (loop for op in $operlist
		       if (not (or (memq op $free-constructors)
				   (memq op $bool-ops)
				   (null (get-arity2 op))))
			 collect (cons op (defining-domain op))))

	; For efficiency, we take care of the immediate subterms
	; of the left hand sides only. That is ok for most cases.
	(loop for rule in $rule-set do
	    (loop for arg in (args-of (lhs rule)) if (nonvarp arg) do
		(setq l3 (cdr (assq (op-of arg) l2)))
		(setf l3
		      (extend-def-domain arg l3 (non-linear-vars arg)))))
	l2))

(defun defining-domain (op)
  ; Returns the defining domain of the operator OP.
  (let ((def-domain (ncons (ncons op))))
     (loop for xa in (rules-with-op op $op_rules)
	   as t1 = (lhs xa) do 
        (if (subs-are-primitive t1) then
        ; if it contains only one non-constructors as root, then ...
  	    (setq def-domain
		 (extend-def-domain t1 def-domain (non-linear-vars t1)))))
     def-domain))

(defun extend-def-domain (t1 s2 nl-vars)
  ; Extending "s2" as large as "t1".
  (cond ((variablep t1)
	 (if (memq t1 nl-vars) 
	     then (make-term $constructors (args-of s2))
	     else s2))
        ((null s2) (def-domain-points t1 nl-vars))
        (t (make-term (ins-lis (op-of t1) (op-of s2))
		      (extend-dom-args (args-of t1) (args-of s2) nl-vars)))))

(defun def-domain-points (t1 nl-vars)
  ; Returns a superterm s2 such that:
  ;   1. Occ(s2) = Occ(t1)
  ;   2. for all u in Occ(s2), s2(u) = nil if t1(u) is
  ;      a linear variable in t1, s2(u) = (t1(u)) if t1(u) is operator,
  ;  s2(u) = $constructors, otherwise.
  (cond ((variablep t1)
	 (if (member t1 nl-vars) then (make-term $constructors nil) else nil))
        (t (make-term (ncons (op-of t1)) 
	 	      (loop for xa in (args-of t1) collect
			 (def-domain-points xa nl-vars))))))

(defun extend-dom-args (l1 l2 nl-vars)
  ; For each term t1 in l1 and each term s2 in l2,
  ; apply "extend-def-domain" on t1 and s2.
  (let ((n1 (length l1)) (n2 (length l2)))
     (nconc (loop for xa in l1 
		  for ya in l2 
		  collect (extend-def-domain xa ya nl-vars))
            (cond ((= n1 n2) nil)
 	   	  ((< n1 n2) (nthcdr n1 l2))
	          (t (loop for xa in (nthcdr n2 l1) 
			     collect (def-domain-points xa nl-vars)))))))

(defun one-extensible-point (t1 def-domain)
  ; Returns a variable occurrence of "t1" if this occurrence
  ; is a defining point in def-domain.
  (delete 0 (one-extensible t1 def-domain)))

(defun one-extensible (t1 def-domain)
  ; Auxiliary function of "one-extensible-point".
  (cond ((null def-domain) nil)
	((variablep t1) (list 0))
        ((memq (op-of t1) (op-of def-domain))
	 (loop for a1 in (args-of t1)
               for a2 in (args-of def-domain) as i from 1 
			if (setq a1 (one-extensible a1 a2)) 
			return (cons i a1)
			finally (return nil)))))

(defun one-extensible-type-point (t1 def-domain)
  ; Returns a variable occurrence of "t1" if this occurrence
  ; is a defining point in def-domain.
  (if (and (memq (op-of t1) (op-of def-domain))
	   (or (not (ac-root t1)) (= (length t1) (length def-domain)))) then
     (loop for a1 in (args-of t1)
           for a2 in (args-of def-domain)
	   for a3 in (get-codomain-types (op-of t1))
	  	  as i from 1 do
	     (cond ((null a2) nil)
	 	   ((variablep a1) (return (list a3 i)))
		   ((setq a1 (one-extensible-type-point a1 a2)) 
		    (return (cons (car a1) (cons i (cdr a1))))))
	   finally (return nil))))

(defun superterm-cover (def-domain t1)
  ; Return T iff the superterm "def-domain" covers the term "t1".
  (cond	((variablep t1) t)
	((null def-domain) nil)
        ((memq (op-of t1) (op-of def-domain))
	 (if (or (ac-root t1) (comm-root t1)) then 
	     (loop for arg in (args-of t1) always
		   (loop for arg2 in (args-of def-domain)
			 thereis (superterm-cover arg2 arg)))
	     else
	     (loop for a1 in (args-of t1)
		   for s2 in (args-of def-domain)
		   always (superterm-cover s2 a1))))
	(t nil)))

(defun get-skeleton (t1 def-domain)
  ; Return the skeleton of T1 relative to "def-domain".
  (initsym 'x)
  (get-skeleton2 t1 def-domain))

(defun get-skeleton2 (t1 def-domain)
  ; Auxiliary function of get-skeleton.
  (cond ((null def-domain) (newsym 'x))
        ((variablep t1) (newsym 'x))
        ((memq (op-of t1) (op-of def-domain))
	 (make-term (op-of t1)
  	    (nconc (mapcar 'get-skeleton2 (args-of t1) (args-of def-domain))
		   (let ((n (- (length (args-of t1)) 
			       (length (args-of def-domain)))))
		      (if (> n 0) then 
			 (loop for xa from 0 to n collect (newsym 'x)))))))
	(t (newsym 'x))))

(defun get-down (t1 def-domain type-bases &aux p l1)
  ; If t1 is extensible, that is, there exists a variable occurrence both 
  ; in T1 and in DEF-TREE, then returns the terms obtained by replacing that
  ; variable by the corresponding typed terms in BASE-TERMS.
  (setq p (one-extensible-type-point t1 def-domain)
	l1 (var-list t1))
  (if p then
      (setq l1 (rpl-by-terms (cdr p) t1
			     (loop for bs in (cdr (assoc (car p) type-bases)) 
				   collect (rename-vars bs)))
	    l1 (mapcar 'flat-term-func l1))
      
      (if (= $trace_flag 3) then
	  (terpri)
	  (princ "The schemes of the term") (terpri) 
	  (princ "    ") (write-term t1) (terpri)
	  (princ "    are") (terpri)
	  (loop for t2 in l1 do (princ "    ") (write-term t2) (terpri)))
      l1))

;(defun not-cover-reducible (t1)
   ; Compute the contextuel normal forms of T1, if the disjuction
   ; of contexts of the normal forms are equal to TRUE, then return
   ; NIL; Otherwise, return the complement of the disjuction.
   ; The time spent for reduction is accumulated in $reduce_time.
;   (let ((temp (set-timer)) 
; 	  (cterms (norm-cterm1 (make-cterm t1 nil)))
;	  ct first)
;    (cond ((null (cdr cterms)) 
;	   (setq first (car cterms))
;	   (cond ((equal (t-cterm first) t1) ;; T1 is in normal form.
;		  (setq ct '(true))) 
;		 ((null-ctx (c-cterm first)) (setq ct nil))
;		 (t (setq ct (norm-ctx (not-arg (c-cterm first)))))))
;	  (t (setq first (pop cterms)
;		   ct (not-arg (c-cterm first)))
;	     (loop for xa in cterms do
;		(setq ct (norm-ctx-and ct (not-arg (c-cterm xa))))
;	        (if (falsep ct) then (return (setq ct nil))))))
;    (setq $reduce_time (+ $reduce_time (get-time temp)))
;    ct))

(defun trace-testset (news)   
   ; Print info about new members of testset.
   (terpri)
   (princ " --- Getting down one position ---") (terpri)
   (princ (uconcat "There are " $possi-num " terms made out.")) (terpri)
   (princ (uconcat "Among them, there are " $irredu-num 
		" terms irreducible.")) (terpri)
   (setq $possi-num 0 $irredu-num 0)
   (princ (uconcat "Following " (length news) 
		" new terms are added in testset:")) (terpri)
   (loop for t1 in news do (princ "    ") (write-term t1) (terpri)))
 
(defun trace-add-testset (l2 time)
   ; Print info about new members of testset and the time used.
   (loop for current in l2 do 
	(terpri) (princ "Adding to testset: ") (write-term current) (terpri))
   (terpri)
#+franz
   (format t "Time spent in computing TestSet  =  ~f sec" (get-time time))
   (terpri))

(defun destroyable (term terms)
  ; Returns a term t1 in TERMS such that TERM matches t1 or one
  ; of variable occurrences of t1 is an operator occurrence of TERM.
  (if (or (truep term) (falsep term)) then term
   elseif (is-primitive term) 
   then (loop for t1 in terms if (applies term t1) return t1)))

(defun rule-destroyable (term &aux l2 def-dom ts type-bases)
  ; "term" is the left-hand side of a rule. 
  ; If that rule extends the defining domain of the root operaotor of "term",
  ; then re-compute the defining domain and the corresponsding test set.
  ; Return the term in $testset such that "term" matches that term.
  (if (is-primitive term) then
     (if (not (superterm-cover (get-def-domain (op-of term)) term)) then
	; we need re-compute the test set $testset,
	(setq def-dom (get-def-domain (op-of term)))
	(setf def-dom (extend-def-domain term def-dom
					      (non-linear-vars term)))
	(setq ts $testset 
	      $testset nil
	      type-bases (get-basic-type-terms $constructors))
	(loop for xa in ts do
	    (if (not (same-op xa term)) 
		then (push xa $testset) 
	      elseif (one-extensible-point xa def-dom)
		then (setq l2 (nconc l2
				 (extend-schemes xa def-dom type-bases)))
		else (push xa $testset)))
	(if l2 then (setq $testset (quasi-check l2 $testset)))
	(setq $type-testset (partition-term-by-type $testset)))
     (loop for t1 in $testset 
	   if (applies term t1) 
	     do (terpri)
		(princ "    Deleting the term ")
		(write-term t1) 
		(princ " in the test set.")
		(terpri)		
		(return t1))))

(defun partition-term-by-type (terms &aux output) 
  ; partition "terms" by their type.
  (loop for tt in terms do
        (add-associate-list (get-domain-type (op-of tt)) tt output))
  (loop for ty-terms in output do
     (loop for subtype in (get-subtypes (car ty-terms)) do
       (if (assoc subtype output) then
	   (rplacd ty-terms (union (cdr ty-terms) (cdr (assoc subtype output)))))))
  output)


(defun partition-ops-by-type (ops &aux output) 
  ; partition "ops" by their domain type.
  (loop for op in ops do
        (add-associate-list (get-domain-type op) op output)
	finally (return output)))

(defun get-basic-type-terms (ops &aux output) 
  ; Return a list basic terms partitioned by their domain type.
  (setq output (loop for ty-op in (partition-ops-by-type ops) collect
		     (cons (car ty-op) (mapcar 'basic-term (cdr ty-op)))))
  (loop for ty-terms in output do
     (loop for subtype in (get-subtypes (car ty-terms)) do
       (if (assoc subtype output) then
	   (rplacd ty-terms (union (cdr ty-terms) (cdr (assoc subtype output)))))))
  output)

(defun basic-term (op)
  ; Returns a term in form of "op(x1, x2, ..., xn)" 
  ; where arity(op) = n and x1, x2, ... xn are not in $basic-vars.
  (let ((arity (get-arity op)))
     (cond ((= arity 0) (ncons op))
	   (t (make-term op 
			 (loop for xa = 0 then (1+ xa) until (= arity xa) 
			       collect (make-new-variable 'x)))))))

;;;; functions for computing testset using Kounalis & Zhang's method.

(defun get-testset-quasi (cons-ops)
  ; Returns the testset with the depth "$base-depth".
  (let (l1 dup tops new-tops testset non-constant news 
	    (time (set-timer))
            (base-depth (base-depth)))
         (setq $possi-num 0 
	       $irredu-num 0
	       news (mapcar 'ncons (get-constants cons-ops))
	       non-constant (non-constants cons-ops))
         (loop for xa = 0 then (1+ xa) until (= base-depth xa) do
            (setq l1 (add-one-depth non-constant news testset nil)
		  testset (nconc testset (mapcar 'rename-vars news)))
	    (if (= $trace_flag 3) then (trace-testset news))
            (if l1 then (setq news l1) else (return nil)))

         (if l1 then
	   (setq dup (copylist testset))
	   (loop while t do
	     (setq new-tops (new-top-terms news base-depth))
	     (if new-tops 
	      then (setq tops (append tops new-tops))
		   (nconc testset (mapcar 'rename-vars new-tops))
     	      else (return testset))
	     (setq l1 (add-one-depth non-constant news dup tops))
 	     (if (= $trace_flag 3) then (trace-testset new-tops))
	     (nconc dup news)
	     (setq news l1)))
	 (if (= $trace_flag 3) then (terpri)
#+franz	      (format t "Time spent in computing TestSet  =  ~f sec"  
			(get-time time)) (terpri))
	 testset))

(defun add-one-depth (ops news terms tops)
  (let ((l1 (loop for op in ops nconc
              (loop for t1 in 
		(make-terms op (new-args (get-arity op) 
					 (get-codomain-types op) news terms)) 
                if (not (or (is-an-instance (setq t1 (flat-term t1)) tops) 
			    (reducible-time t1))) collect t1))))
   (setq $irredu-num (+ $irredu-num (length (setq l1 (rem-dups l1)))))
   l1))

(defun new-args (n types news olds)
  (let ((l1 (loop for x1 in (n-tuples n (append news olds)) 
 	          if (and (loop for t1 in x1 for ty in types 
				always (type-cohere (type-of t1) ty))
			  (have-common x1 news))
		  collect x1)))
   (setq $possi-num (+ $possi-num (length l1)))
   l1))

(defun new-top-terms (news dep)
  ; For each term in "news",  returns its top without duplicate.
  (loop with tops 
	for xa in news 
	if (not (is-an-instance xa tops))
	  do (push (top-term xa dep) tops)
	     finally (return tops)))

(defun top-term (term depth)
  ; Return the top part of a term at a given depth.
  (cond ((variablep term) term)
        ((null (args-of term)) term)
        (t (cond ((< depth 2) (basic-term (op-of term)))
		 ((ac-root term) 
		  (flat-term (if (lessp depth (length term))
				 then (make-term (op-of term)
						 (cons (make-new-variable 'x)
						       (loop for i from 1 to depth
							     for xa in (args-of term)
							     collect xa)))
				 else (make-term (op-of term) 
						 (loop for xa in (args-of term) 
						       collect (top-term xa 
									 (sub1 depth)))))))
	         (t (make-term (op-of term) 
			       (loop for xa in (args-of term) 
				collect (top-term xa (sub1 depth)))))))))

(defun base-depth ()
  ; Returns the maximal depth of the left hand sides of the equations
  ; between contructors.
  (let ((dep 0))
    (loop for op in $constructors do
      (loop for r1 in (rules-with-op op $op_rules) do
         (if (subs-are-primitive (lhs r1))
            then (setq dep (max (depth (lhs r1)) dep)))))
    dep))

(defun make-tuples (n testset)
  ; Return an N-tuple which contains at least once (car "testset"), the
  ; rest elements are in "testset".
  (let ((new (car testset)))
    (loop for xa in (n-tuples n testset) if (member new xa) collect xa)))

