(in-package "USER")

(defun poly1-knuth-bendix (&aux xa)
  (while $del-eqns (poly1-process-equation (cdr (pop $del-eqns))))
  (while $eqn-set (poly1-process-equation (pop $eqn-set)))

  (if (setq xa (pick-unmarked-rule))
      (reset-kb (critpairs xa))
    (empty-post-set)
    ))

(defun poly2-knuth-bendix (&aux xa)
  ; The main body of knuth-bendix completion procedure.
  (while $del-eqns (poly2-process-equation (cdr (pop $del-eqns))))
  (while $eqn-set (poly2-process-equation (pop $eqn-set)))

  (if (setq xa (pick-unmarked-rule))
      (reset-kb (critpairs xa))
    (empty-post-set)
    ))

(defun poly1-process-equation (eqn)
  (trace-message 4 "Processing " (write-eqn eqn))
  (setq eqn (add-time $norm-time (ac-normal-eqn eqn)))
  (if eqn (orient-an-eqn eqn)))

(defun poly2-process-equation (eqn)
  (trace-message 4 "Processing " (write-eqn eqn))
  (setq eqn (add-time $norm-time (poly-normal-eqn eqn)))
  (if eqn (make-rule-from-poly-minus eqn)))

(defun poly-add-rule (rule)
  (if (is-reduction rule)
      (poly-add-rule-complete rule)
    (add-crit-rule rule))

  (if (is-multi-1p-rule rule) (poly-add-multi-1p-rules rule))

  (if $instant (make-rule-instances rule))
  (if (equal (car (eqn-source rule)) 'distr)
      (super-with-ground-rules rule))
  )

(defun poly-add-rule-complete (rule)
  ; Adds RULE to existing rule set.
  (trace-message 2 "Add Rule: " (write-rule rule))

  (if (not (is-nilpotent-rule rule t))
      (if (is-rooted-+ (lhs rule))
	  (setq $poly-rules (append1 $poly-rules rule t))
	(setq $op-rules (warning-add-rule rule $op-rules))))

  (push-end rule $rule-set)

  (if $prove-eqns (check-witness rule))

  (if (> $reduce-system 0) (reduce-other-rules rule))

  (when (not (is-scheme-rule rule))
	(add-pairs (rule-x-to-y rule) rule)
	(add-all-pairs (rule-x-to-y rule)))
  )

;;; Group Three: Superposition with built-in distribution law and associativity law.

(defmacro is-poly (term) `(and $polynomial (nonvarp ,term) (eq (car ,term) *+*)))
(defmacro change-mono-sign (num mset)
  `(sloop for xa in ,mset collect (cons (car xa) (- ,num (cdr xa)))))
(defmacro minus-mono-sign (mset)
  `(sloop for xa in ,mset 
	 collect (cons (car xa) (- (cdr xa)))))

(defun poly-add-pairs (rule1 rule2)
  (let* ((lhs1 (lhs rule1))
	 (lhs2 (lhs rule2))
	 (psize (add (lhsize rule1) (lhsize rule2))) 
	 x1 x2)
    (setq x1 (is-rooted-+ lhs1)
	  x2 (is-rooted-+ lhs2))
    (if (not x1) (psetq x1 x2 x1 x2 rule1 rule2 rule2 rule1))

    (cond 
     ;; none of them is AC-root.
     ((not x1) 
      (add-pair (list psize rule1 rule2 0))
      (if (eq (ruleno rule1) (ruleno rule2)) 
	  (add-pair (list (+ 2 psize) rule1 rule2 3)))
      )

      ;; Same rule.
      ((eq (ruleno rule1) (ruleno rule2))
       (if (not (is-nilpotent-rule rule2))
	   (add-pair (list (+ 5 psize) rule1 rule2 3)))

       (if *-*
	   (add-pair (list (+ -2 psize) rule1 rule2 4))
	 (add-pair (list (times 5 psize) rule1 rule2 2)))
       )

      ;; same ac-root.
      ((same-root lhs1 lhs2)
       (cond
	((or (is-nilpotent-rule rule1) (is-nilpotent-rule rule2))
	 (add-pair (list (add -1000 psize) rule1 rule2 2)))
	((and (is-multi-1p-term lhs1) (is-multi-1p-term lhs2))
	 (if* (< (length (cdr lhs1)) (length (cdr lhs2)))
	      then (add-pair (list (- psize 1000) rule1 rule2 1) )
	      elseif (> (length (cdr lhs1)) (length (cdr lhs2)))
	      then (add-pair (list (- psize 1000) rule2 rule1 1)))
	 )
	(*-* (add-pair (list (+ -2 psize) rule1 rule2 4)))
	(t (add-pair (list (times 3 psize) rule1 rule2 0))
	   (add-pair (list (times 5 psize) rule1 rule2 2)))
	))
	  
      ;; Different root. Rule1 is ac-root.
      ((and (is-rooted-+ lhs1) 
	    (eq (op-of lhs2) $*$) 
	    (memq $*$ $associative)
	    )
       (add-pair (list psize rule1 rule2 0))
       ;; ASSOCIATIVE * ONLY
       (add-pair (list (+ $ex1 psize) rule1 rule2 1))
       )

      ;; Different root. Rule2 may be ac-root.
      (t (add-pair (list psize rule1 rule2 0))
;	 (add-pair (list (times 2 psize) rule1 rule2 1))
	 (if x2 (add-pair (list (times 10 psize) rule2 rule1 1)))
	 )
      )))

(defun poly-superposition (r1 r2 flag)
  (setq $superposed-subs nil)
  (if $symmetry-check
      (setq $symmetry-terms 
	    (or (ref-symmetry-terms r1) (ref-symmetry-terms r2))))

  (if* (eq flag 3) 
       then (poly-super-distribution r1)
       elseif (eq flag 4) 
       then (poly-super-at-+ r1 r2)
       elseif (eq (ruleno r1) (ruleno r2))
       then (ac-sup-term r2 r1 (lhs r1) (lhs r1) 3 0)
       elseif (is-rooted-+ (lhs r1))
       then (cond
	     ((is-rooted-+ (lhs r2))
	      (poly-super-at-+ r1 r2)) ; same as flag = 4.
	     ((is-rooted-* (lhs r2))
	      (if (eq flag 1)
		  (poly-super-+-*-1 r1 r2)
		(poly-super-+-*-0 r1 r2)))
	     ((eq flag 1)
	      (ac-sup-term r1 r2 (lhs r2) (lhs r2) 3 flag))
	     (t (ac-sup-term r2 r1 (lhs r1) (lhs r1) 3 0))
	     )
       elseif (is-rooted-* (lhs r1))
       then (cond 
	     ((is-rooted-+ (lhs r2))
	      (if (eq flag 1)
		  (poly-super-+-*-1 r2 r1)
		(poly-super-+-*-0 r2 r1)))
	     ((is-rooted-* (lhs r2))
	      (poly-super-at-* r1 r2))
	     ((eq flag 0)
	      (ac-sup-term r2 r1 (lhs r1) (lhs r1) 3 0))
	     )
       elseif (eq flag 1)
       then (ac-sup-term r2 r1 (lhs r1) (lhs r1) 3 0)
       else (ac-sup-term r1 r2 (lhs r2) (lhs r2) 3 0)
       ))

(defun poly-super-at-* (r1 r2)
  ;; both r1 and r2 are *-rooted.
  (ac-sup-term r2 r1 (lhs r1) (lhs r1) 3 0)
  (ac-sup-term r1 r2 (lhs r2) (lhs r2) 3 0)
  )

(defun poly-super-+-*-0 (r1 r2)
  ;; r1 is +-rooted; r2 is *-rooted.
  (sloop with source = (list (ruleno r2) (ruleno r1))
	 for sub in (args-of (lhs r1))
	 for pos from 1 
	 ; if (is-rooted-* sub)
	 ;; It's strange that the following line does not work
	 ;; on file moufang2.cmd.
	 if (and (is-rooted-* sub) (not (is-superposed-sub sub)))
	 do
	 ; (ac-sup-term r2 r1 (lhs r1) sub (ncons pos) 0)	
	 (poly-super-at-*-0 r2 r1 (lhs r1) sub (ncons pos) source)
	 ))

(defun poly-super-+-*-2 (r1 r2)
  ;; r1 is +-rooted; r2 is *-rooted.
  (sloop with source = (list (ruleno r2) (ruleno r1))
	 for sub in (args-of (lhs r1))
	 for pos from 1 
	 if (is-rooted-* sub) do
	 (poly-super-at-*-0 r2 r1 (lhs r1) sub (ncons pos) source)
	 ))

(defmacro poly-super-at-*-0-aux ()
  `(sloop with d1 = (product-degree (lhs r1))
	  with d2 = (product-degree (lhs r2))
	  for i downfrom n2 to 2
	  for args on (args-of sub) 
	  as first-n = (first-n-elements args n1)
	  if (and (not (is-deleted-rule r1))
		  (not (is-deleted-rule r2))
		  (>= i n1))
	    do					
	    (setq sigma (unifier lhs1 (make-term $*$ first-n)))
	    (when (and sigma
		       (is-degree-qualified sigma d1 (ref-lhs-vars r1))
		       (is-degree-qualified sigma d2 (ref-lhs-vars r2)))

		  (setq $superposed-sub (make-term $*$ first-n))
		  (trace-message 4 "" 
				 (trace-superpose (ruleno r1) (ruleno r2)
						  (make-term $*$ first-n) sigma))

		  (setq res (rest-elements args n1))
		  (setq res (if (or left-args res) 
				(make-term $*$ (append left-args (ncons rhs1) res))
			      rhs1)
			res (make-eqn
			     (make-flat (applysigma 
					 sigma (rplat-in-by pos lhs2 res)))
			     (flat-applysigma sigma (rhs r2))
			     nil
			     source)
			$ncritpr (add1 $ncritpr))		      
		  (if-well-typed-eqn res (process-critpair res)))
	    (push-end (car args) left-args)
	  else return nil))

(defun poly-super-at-*-0 (r1 r2 lhs2 sub pos source)
  (let* ((lhs1 (lhs r1))
	 (rhs1 (rhs r1))
	 (n1 (length (cdr lhs1)))
	 (n2 (length (cdr sub))) 
	 left-args res sigma)

    ;;(mark "r1-r2" source)

;    (poly-super-+-into-* r1 r2 lhs1 sub source)
    (poly-super-at-*-0-aux)
    ))

(defun poly-super-+-into-* (r1 r2 lhs1 sub2 source &aux sigma t1)
  ;; r1 is *-rooted, r2 is +-rooted.  lhs1 is the lhs of r1.
  (when (member0 sub2 (args-of (lhs r2)))
	(cond ((variablep (first-arg lhs1))
	       (when (and (setq sigma (unifier (second-arg lhs1) sub2))
			  (is-degree-qualified sigma (product-degree (lhs r1)) (ref-lhs-vars r1))
			  (is-degree-qualified sigma (product-degree (lhs r2)) (ref-lhs-vars r2)))

		     (setq t1 (removen sub2 (args-of (lhs r2)) 1)
			   t1 (sloop for arg in t1 collect
				     (make-term $*$ (list (first-arg lhs1) arg)))
			   t1 (cons (rhs r1) t1)
			   t1 (make-term *+* t1)
			   t1 (make-eqn
			       (flat-applysigma sigma t1)
			       (flat-applysigma sigma (make-term $*$ (list (first-arg lhs1)
									   (rhs r2))))
			       nil
			       source)
			   $ncritpr (add1 $ncritpr))
		     (if-well-typed-eqn t1 (process-critpair t1)))
	       )

	      ((variablep (second-arg lhs1))
	       (when (and (setq sigma (unifier (first-arg lhs1) sub2))
			  (is-degree-qualified sigma (product-degree (lhs r1)) (ref-lhs-vars r1)))

		     (setq t1 (removen sub2 (args-of (lhs r2)) 1)
			   t1 (sloop for arg in t1 collect
				     (make-term $*$ (list arg (second-arg lhs1))))
			   t1 (cons (rhs r1) t1)
			   t1 (make-term *+* t1)
			   t1 (make-eqn
			       (flat-applysigma sigma t1)
			       (flat-applysigma sigma (make-term $*$ (list (rhs r2) (second-arg lhs1))))
			       nil
			       source)
			   $ncritpr (add1 $ncritpr))
		     (if-well-typed-eqn t1 (process-critpair t1)))
	       )
	      )))

(defun poly-super-+-*-1 (r1 r2)
  ;; r1 is +-rooted; r2 is *-rooted.
  (sloop with source = (list (ruleno r2) (ruleno r1))
	 for sub in (args-of (lhs r1))
	 for pos from 1 
	 if (and (is-rooted-* sub)
		 (not (is-superposed-sub sub))) do
	 (poly-super-at-*-1 r2 r1 (lhs r1) sub (ncons pos) source)
	 ))

(defun poly-super-at-*-1 (r1 r2 lhs2 sub pos source)
  (let* ((lhs1 (lhs r1))
	 (rhs1 (rhs r1))
	 (n1 (length (cdr lhs1)))
	 (n2 (length (cdr sub))) 
	 left-args res sigma
	 (last-arg (car (last sub))))

    (when (variablep last-arg)
;     (and (variablep last-arg) (not (member0 last-arg $superposed-subs)))
	  (sloop for vars in (ref-symmetry-vars r2)
		 if (memq last-arg vars) 
		 return (setq $superposed-subs (append $superposed-subs vars))
		 finally (push last-arg $superposed-subs))

	  (sloop with d1 = (product-degree (lhs r1))
		 with d2 = (product-degree (lhs r2))
		 for i downfrom n2 to 2
		 for args on (args-of sub) 
		 if (and (not (is-deleted-rule r1)) (not (is-deleted-rule r2)))
		 do					
		 (if* (> n1 i) then
		      (when (and (setq sigma (unifier (compact-last-elements lhs1 i)
						      (make-term $*$ args)))
				 (is-degree-qualified sigma d1 (ref-lhs-vars r1))
				 (is-degree-qualified sigma d2 (ref-lhs-vars r2)))
			    
			    (setq $superposed-sub (make-term $*$ args))
			    (trace-message 4 "" 
					   (trace-superpose (ruleno r1) (ruleno r2)
							    (make-term $*$ args) sigma))

			    (setq res (if (or left-args res) 
					  (make-term $*$ (append left-args
								 (ncons rhs1)))
					rhs1)
				  res (make-eqn
				       (flat-applysigma 
					sigma (rplat-in-by pos lhs2 res))
				       (flat-applysigma sigma (rhs r2))
				       nil
				       (delq 'ext1 source))
				  $ncritpr (add1 $ncritpr))		      
			    (if-well-typed-eqn res (process-critpair res)))
		      (return nil))
		 (push-end (car args) left-args)
		 else return nil))))
	     
(defun compact-last-elements (term n &aux op new)
  ; term is of form: f(t1, t2, ..., tk), 
  ; return a term of form: f(t1, t2, ..., f(tj, .., tk)).
  (setq op (car term) term (cdr term))
  (dotimes (i (1- n))
    (setq new (cons (car term) new)
	  term (cdr term)))
  (make-term op (append1 (nreverse new) (make-term op term))))

(defun poly-super-distribution (rule)
  (sloop with eqn with rhs
	 for xa in (one-presentative (nonlinear-vars-under-* (lhs rule))
				     (ref-symmetry-vars rule))
	 as new = (list *+* (make-new-variable) (make-new-variable))
	 if (not (is-deleted-rule rule))
	 do
	 (setq $superposed-sub (list $*$ xa xa))
	 (trace-message 4 "" 
			(trace-superpose "DISTR" (ruleno rule)
					 (list $*$ xa xa) (list (cons xa new))))
	 (setq eqn (list *+*
			 (replace-term new xa (lhs rule))
			 (list *-* (replace-term (first-arg new) xa (lhs rule)))
			 (list *-* (replace-term (second-arg new) xa (lhs rule)))
			 )
	       rhs (list *+*
			 (replace-term new xa (rhs rule))
			 (list *-* (replace-term (first-arg new) xa (rhs rule)))
			 (list *-* (replace-term (second-arg new) xa (rhs rule)))
			 )
	       eqn (make-eqn eqn rhs nil (list 'distr (ruleno rule)))
	       eqn (flatten-eqn eqn)
	       $ncritpr (add1 $ncritpr))

	 (process-critpair eqn)
	 ))

(defun nonlinear-vars-under-* (term)
  (if (variablep term) 
      nil
      (rem-dups 
	(cond
	  ((eq (op-of term) $*$) 
	   (eles-more-than-1 
	     (sloop for xa in (args-of-same-root $*$ (args-of term))
		    if (variablep xa) collect xa)))
	  (t (mapcan 'nonlinear-vars-under-* (args-of term)))))))

(defun eles-more-than-1 (lis)
  ; return a set of elements of lis that have more than one copy.
  (sloop with l2 for xa in lis
	if (memq xa l1) do (query-insert xa l2)
	else collect xa into l1
	finally (return l2)))

(defun nonvar-unique-monos (rule &optional more
				 &aux (res (ref-symmetry-terms rule)))
  (if res 
      (sloop for xl in res 
	     if (and (nonvarp (car xl)) (have-common xl (args-of (lhs rule))))
	     collect (car xl))
    (if more 
	(rem-dups (sloop for xa in (args-of (lhs rule)) 
			 if (nonvarp xa) collect xa))
      )))

(defmacro poly-subt-crossfire (monos1 monos2 r1 r2 source)
  `(sloop for a1 in ,monos1 do
	  (setq b1 (if (eq (op-of a1) *-*) (first-arg a1) a1))
	  (when (eq (op-of b1) $*$)
		(if (and (variablep (first-arg b1))
			 (not (is-superposed-sub (second-arg b1))))
		    (poly-crossfire (second-arg b1) 
				    a1 ,r1 ,monos2 ,r2 ,source 1 (first-arg b1)))

		(if (and (variablep (second-arg b1))
			 (not (is-superposed-sub (first-arg b1))))
		    (poly-crossfire (first-arg b1) 
				    a1 ,r1 ,monos2 ,r2 ,source 2 (second-arg b1))))))

(defun poly-super-at-+ (r1 r2 &aux monos1 monos2 source b1)
  ;; the lhss of r1 and r2 are rooted by the same ac operator.
  ;; New trick to avoid extensions.
  (setq monos1 (nonvar-unique-monos r1 t))
  (setq monos2 (nonvar-unique-monos r2 t))
  (setq source (list (ruleno r1) (ruleno r2) 'ext2))

  (sloop for a1 in monos1 do
	 (if (eq (op-of a1) *-*)
	     (poly-crossfire (first-arg a1) a1 r1 monos2 r2 source 0)
	   (poly-crossfire a1 a1 r1 monos2 r2 source 0)))

  (when (and (not (member $*$ $associative))
	     (< (product-degree (lhs r2)) $discard-eqn-max-degree))
	;(mark source "r1-r2")	
	(poly-subt-crossfire monos1 monos2 r1 r2 source))

  (when (and (not (member $*$ $associative))
	     (< (product-degree (lhs r1)) $discard-eqn-max-degree))
	;(mark source "R1-R2")	
	(poly-subt-crossfire monos2 monos1 r2 r1 source))
  )

(defmacro term-by-flag (flag t1 t2)
  `(case ,flag
	 (0 ,t1)
	 (1 (make-term-2arg $*$ ,t2 ,t1))
	 (2 (make-term-2arg $*$ ,t1 ,t2))
	 ))

(defun poly-crossfire (t1 a1 r1 monos2 r2 source flag &optional t2 &aux b2)
  (sloop with d1 = (product-degree (lhs r1))
	 with d2 = (product-degree (lhs r2))
	 for a2 in monos2
	 if (and (not (is-deleted-rule r1))
		 (not (is-deleted-rule r2)))
	 do
	 (setq b2 (if (eq (op-of a2) *-*) (first-arg a2) a2))

	 (sloop for sigma in (unifiers t1 b2 0 t) do
		(when (and
		       (is-degree-qualified sigma d1 (ref-lhs-vars r1))
		       (is-degree-qualified sigma d2 (ref-lhs-vars r2)))

	        (setq $superposed-sub a2)
		(trace-message 4 "" 
			       (trace-superpose 
				(ruleno r1) (ruleno r2) a2 sigma))
		(let ((l1 (removen a1 (lhs r1) 1))
		      (l2 (term-by-flag flag (removen a2 (lhs r2) 1) t2))
		      (l3 (rhs r1))
		      (l4 (term-by-flag flag (rhs r2) t2)))
		  (if (eq (op-of a1) *-*)
		      (setq l1 (list *-* l1)
			    l3 (list *-* l3)))
		  (if (eq (op-of a2) *-*)
		      (setq l2 (list *-* l2)
			    l4 (list *-* l4)))
		  (poly-process-cp l1 l2 l3 l4 source sigma))))
	 ))

(defun poly-process-cp (lhs1 lhs2 rhs1 rhs2 source sigma)
  (setq $ncritpr (add1 $ncritpr)
	lhs1 (flat-term (list *+* (applysigma sigma lhs1) (applysigma sigma rhs2)))
	rhs1 (flat-term (list *+* (applysigma sigma lhs2) (applysigma sigma rhs1))))
;  (mark lhs1 "LHS")
;  (mark rhs1 "RHS")
  (if (nequal lhs1 rhs1)
      (process-critpair (make-eqn lhs1 rhs1 nil source)))
  )

;;;; Group Four: Utility functions

(defun move-eqn-lhs-args (eqn &aux l1)
  (when (and (nonvarp (lhs eqn))
	     (has-nilpotent-rule (op-of (lhs eqn)))
	     (poly-lrpo (lhs eqn) (rhs eqn))
	     (cdr (setq l1 (mult-form (args-of (lhs eqn)))))) 

    ;; At first, partition l1 into big and small two sets.
    (setq l1 (sloop with small with xa with t1
		    for i from 1 to (length l1) do
		    (setq xa (pop l1)
			  t1 (car xa))
		    (if (sloop for ya in l1 thereis (poly-lrpo (car ya) t1))
			(push xa small)
			(append1 l1 xa t))
		    finally (return small)))

    (when l1
      (let (lhs ruleno c)
	(setq ruleno (has-nilpotent-rule (op-of (lhs eqn)))
	      c (cadr ruleno)
	      ruleno (car ruleno)
	      lhs (args-of (lhs eqn)))
	(sloop for xa in l1 do (setq lhs (remove0 (car xa) lhs)))
	(setq lhs (if (cdr lhs) (make-term (op-of (lhs eqn)) lhs) (car lhs))
	      c (nconc (list (op-of (lhs eqn)) (rhs eqn))
		       (sloop for xa in l1
			      append (ntimes (- c (cdr xa)) (car xa))))
	      $ncritpr (add1 $ncritpr)
	      c (norm-term (flat-term c)))
	(setq eqn (make-dummy-rule eqn)
	      c (make-new-rule (make-eqn lhs c (ctx eqn)
					 (list ruleno (ruleno eqn) 'ext2))))
	(add-rule-time c)
	t))))

(defun super-with-ground-rules (rule &aux mlhs char)
  (when (and $instant
	     (equal (op-of (lhs rule)) *+*)
	     (not (is-ground-rule rule))
	     (cdr (setq mlhs (mult-form (args-of (lhs rule)))))
	     (or (setq char (has-nilpotent-rule *+*)) (get-op-id "-")))

	    (sloop with ruleno = (ruleno rule)
		   for grule in $rule-set 
		   if (or (is-deleted-rule grule) (> (ruleno grule) ruleno))
		   return nil
		   else if (is-ground-rule grule) do
		   (super-with-one-ground-rule rule grule mlhs char))
	  ))

(defun super-with-one-ground-rule (rule grule mlhs char &aux sigma eqn)
  (when $instant
  (sloop for seed in (if (equal (op-of (lhs grule)) *eq*)
			 (nconc (+-canonicalize (first-arg (lhs grule)))
				(+-canonicalize (second-arg (lhs grule))))
			 (+-canonicalize (lhs grule)))
	 do
	 (if (is-rooted-minus seed) (setq seed (first-arg seed)))

	 (sloop for narg in mlhs
		for arg = (car narg)
		do
		(if (is-rooted-minus arg) (setq arg (first-arg arg)))

		(when (setq sigma (applies arg seed))
		  (setq eqn (make-eqn (flat-applysigma sigma (lhs rule))
				      (flat-applysigma sigma (rhs rule))
				      nil
				      (list (ruleno rule) (ruleno grule))))
		(trace-message 
		 2 ""
		 (format t "Making an instance of Rule [~d], and " 
			 (ruleno rule))
		 (princ "simplifying it by Polynomial machine:")
		 (terpri) (princ "    ") 
		 (write-eqn eqn)
		 (princ "    with the substitution: ") 
		 (write-sigma sigma) (terpri)
		 )
		(if *-* (move-monos-minus eqn)
		  (if char (move-monos-char eqn (cadr char))))
	 )))))

(defun make-rule-instances (rule &aux vars eqn char)
  (if (and $instant
	   (equal (op-of (lhs rule)) *+*)
	   (setq vars (get-lhs-vars rule))
	   (not (is-multi-1p-rule rule)))

      ;; If there are different monomials in lhs, then do the following ...
      (if (or (setq char (has-nilpotent-rule *+*)) (get-op-id "-"))
	  (sloop for terms in (get-instance-terms (length vars)) do
		 (sloop for sigma in (compose-sigmas terms vars
						     (ref-symmetry-vars rule))
			do
			(setq eqn (make-eqn (lhs rule) (rhs rule) nil
					    (list 'insta (ruleno rule)))
			      eqn (applysubst-eqn sigma eqn))
			(trace-message 
			 2 ""
			 (format t "Making an instance of Rule [~d], and " 
				 (ruleno rule))
			 (princ "simplifying it by Polynomial machine:")
			 (terpri) (princ "    ") 
			 (write-eqn eqn)
			 (princ "    with the substitution: ") 
			 (write-sigma sigma) (terpri)
			 )
			(if *-* (move-monos-minus eqn)
			  (if char (move-monos-char eqn (cadr char))))
			)))))

(defun compose-sigmas (terms vars symm-vars &aux (vars1 vars) used)
  ;; return |vars| different substitutions made from (vars X terms).
  ;; discard some of them by symmetry relation given in symm-vars.
  (sloop for var in vars 
	 if (not (memq var used))
	 collect (prog1
		   (pairlis vars1 terms)
		   (sloop for sym in symm-vars do
			  (if (member var sym)
			      (return (setq used (append sym used))))
			  finally (push var used))
		   (setq vars1 (append1 (cdr vars1) (car vars1))))))

(defmacro wash-mult-monos (lhs)
  `(sloop for xa in ,lhs 
	  if (and (neq (cdr xa) 0) (not (equal (car xa) *0term*)))
	  collect xa))

(defmacro adjust-by-char (lhs)
  `(sloop with mod = (second char)
	  with half = (/ (second char) 2)
	  for xa in ,lhs do
	  (if (> (cdr xa) 0)
	      (if (> (cdr xa) half)
		  (setf (cdr xa) (- (cdr xa) mod)))
	    (if (>= (abs (cdr xa)) half)
		(setf (cdr xa) (+ mod (cdr xa)))))))

(defmacro adjust-by-char2 (lhs)
  `(sloop with mod = (second char)
	  for xa in ,lhs do
	  (if (< (cdr xa) 0)
	      (setf (cdr xa) (+ mod (cdr xa))))))

(defmacro separate-monos-by-lrpo ()
  `(sloop for i from 1 to (length lhs) do
	  (if (sloop with t1 = (caar lhs)
		     for ya in lhs thereis (poly-lrpo (car ya) t1))
	      (setq rhs (cons (car lhs) rhs) 
		    lhs (cdr lhs)) 
	    (setq lhs (append1 (cdr lhs) (car lhs))))))

(defun move-monos-minus (eqn &optional +-at-lhs)
  ; At first, turn rhs into a mult-set form and merge lhs and rhs into one by 
  ; deleting the common part and change the sign of mons in rhs.
  (let ((lhs (lhs eqn))
	(char (has-nilpotent-rule *+*)))

    ;(mark lhs "lhs1")

    (setq lhs (mult-form-minus (nconc (+-canonicalize lhs)
				      (+-canonicalize-minus (rhs eqn))))
	  lhs (wash-mult-monos lhs))

    (when char (adjust-by-char2 lhs))

    ;(mark lhs "lhs2")
    (norm-lhs-monos eqn lhs +-at-lhs)))

(defun norm-lhs-monos (eqn lhs +-at-lhs)
  (setq lhs (norm-mult-monos lhs)
	lhs (wash-mult-monos lhs))

  (when lhs
;	(mark lhs "lhs3")
	(separate-monos eqn lhs +-at-lhs)))

(defun separate-monos (eqn lhs +-at-lhs &aux lhs2 lhs3 rhs
			   (char (has-nilpotent-rule *+*)))
			
  ;; Partition lhs into big and small two sets.
  (add-time $ord-time (separate-monos-by-lrpo))

;  (mark lhs "lhs4")
;  (mark rhs "rhs4")

  (if (and (null rhs) (setq rhs (is-p-commut-poly lhs eqn)))
      (if (eq rhs t) nil (make-p-commut-rule rhs))

  (when (or +-at-lhs (and rhs (null (cdr lhs))))
	
	(setq lhs2 (cdr lhs))

	(if* (< (cdr (car lhs)) 0) 
	     then
	     (setq lhs (minus-mono-sign lhs))
	     (when char (adjust-by-char2 lhs))
	     else
	     (setq rhs (minus-mono-sign rhs))
	     (when char (adjust-by-char rhs))
	     )

	(setq lhs3 (demult-form-minus lhs))
	(if* (cdr lhs3)
	     then
	     (setq lhs3 (flat-term (make-term *+* lhs3)))
	     (if lhs2 (setq lhs2 (poly-reduce-+-term lhs3)))
	     else
	     (setq lhs3 (car lhs3)))

	(if* (null lhs2) 
	     ;; lhs is in normal form.
	     then
	     (rule-from-monos eqn lhs rhs +-at-lhs lhs3)
	     else
	     ;; lhs2 is the lhs reduced once.
	     (norm-lhs-monos eqn
			     (wash-mult-monos 
			      (mult-sort-merge
			       (mult-form-minus (+-canonicalize lhs2))
			       (minus-mono-sign rhs)))

			     t)
	))))

(defun rule-from-monos (eqn lhs rhs no-rule &optional lhs3)
  (if (null lhs3)
      (setq lhs (demult-form-minus lhs)
	    lhs (if (cdr lhs) (flat-term (make-term *+* lhs)) (car lhs)))
    (setq lhs lhs3))

  (if rhs
      (setq rhs (demult-form-minus rhs)
	    rhs (if (cdr rhs) (flat-term (make-term *+* rhs)) (car rhs)))
    (setq rhs *0term*))

  (change-lhs-rhs eqn lhs rhs)
  (update-used-rules eqn)

  (if no-rule 
      eqn
    (make-rule-from-poly-minus eqn)
    ))

(defun make-rule-from-poly-minus (eqn)
  (setq eqn (make-new-rule eqn)
	$ncritpr (add1 $ncritpr))
  (add-rule-time eqn))

(defun move-monos-char (eqn char)
  ; At first, turn rhs into a mult-set form and merge lhs and rhs into one by 
  ; deleting the common part and change the sign of mons in rhs.
  (let ((lhs (lhs eqn)) (rhs (rhs eqn)) small)
    (setq lhs (norm-mult-monos (mult-form (+-canonicalize lhs)))
	  rhs (norm-mult-monos (mult-form (+-canonicalize rhs))))
    
    (setq small (mult-diff2 lhs rhs)
	  rhs (mult-diff2 rhs lhs)
	  lhs (nconc small (change-mono-sign char rhs))
	  small nil
	  lhs (sloop for xa in lhs for rem = (remainder (cdr xa) char) 
		    if (neq rem 0) collect (cons (car xa) rem)))
    
    ; Next, partition lhs into big and small two sets.
    (sloop for xa in lhs as t1 = (car xa) do
      (pop lhs)
      (if (sloop for ya in lhs thereis (poly-lrpo (car ya) t1))
	  (push xa small)
	(setq lhs (append1 lhs xa))))
    
    (if* (and small (null (cdr lhs))) then
      (setq lhs (car lhs))

      (if* (and (thereis-p-commut-rule *+* (op-of (car lhs)))
	       (not (is-sorted (args-of (car lhs)) 'total-term-ordering))) then
	(setq small (gcd-with-p-commut-rule char lhs small)
	      lhs (car small)
	      small (cdr small))
	elseif (< (times 2 (cdr lhs)) char) then
	(setq small (norm-sign-changed-monos char small))
	else
	(setq lhs (cons (car lhs) (- char (cdr lhs)))))
      
      (setq lhs (ntimes (cdr lhs) (car lhs))
	    lhs (if (cdr lhs) (make-term *+* lhs) (car lhs))
	    rhs (demult-form small)
	    rhs (if (cdr rhs) (make-term *+* rhs) (car rhs)))
      (change-lhs-rhs eqn (flat-term lhs) (flat-term rhs))
      (update-used-rules eqn) 
      (when (setq rhs (cancellation rhs))
	    (setq rhs (make-new-rule rhs)
		  $ncritpr (add1 $ncritpr))
	    (add-rule-time rhs)))))

(defun gcd-with-p-commut-rule (char lhs small) 
  (let* ((pval (thereis-p-commut-rule *+* (op-of (car lhs))))
	 (gcd (gcd (cadddr pval) (cdr lhs))) k1)
    (if* (eq gcd (cdr lhs)) then
      (setq small (norm-sign-changed-monos char small))
      else
      (setq k1 (solve-gcd-puzzle (- char (cdr lhs)) (cadddr pval) gcd))
      (if* (neq k1 1) then
	(remember-used-rule-num (car pval))
	(setq small (sloop for xa in small 
			  collect (cons (car xa) (* k1 (cdr xa))))))
      (setq k1 (- (* k1 (- char (cdr lhs))) gcd))
      (setq small (mult-insert (cons (sort-op-args (car lhs)) k1) small))
      (setq small (sloop for xa in small
			for rem = (remainder (cdr xa) char) 
			if (neq rem 0) collect (cons (car xa) rem)))
      (setq lhs (cons (car lhs) gcd)))
    (cons lhs small)))

(defun solve-gcd-puzzle	(n1 n2 gcd)
  ;; return k1 such that k1 n1 - k2 n2 = gcd for some k2.
  (sloop for k1 from 1 to 24
	if (equal (remainder (- (* k1 n1) gcd) n2) 0)
	return k1
	finally (return 1)))

(defun poly-lrpo-minus (m1 m2)
  (if* (variablep m1) then nil
      elseif (variablep m2) then t
      elseif (eq (op-of m1) *-*)
      then (if (eq (op-of m2) *-*) 
	       (poly-lrpo (cadr m1) (cadr m2))
	       (poly-lrpo (cadr m1) m2))
      elseif (eq (op-of m2) *-*)
      then (poly-lrpo m1 (cadr m2))
      else (poly-lrpo m1 m2)))

(defun poly-lrpo (m1 m2)
  (if* (not $polynomial) then (lrpo m1 m2)
      elseif (variablep m1) then nil
      elseif (variablep m2) then t
      elseif (and (eq (op-of m1) $*$) (same-root m1 m2))
      then (let ((l1 (length m1)) (l2 (length m2)))
	     (if* (eq l1 l2) then
;	       (sloop for xa in (cdr m1) 
;		      for xb in (cdr m2) 
;		      if (not (poly-lrpo-equal xa xb)) 
	       (sloop for xa in (reverse (cdr m1))
		      for xb in (reverse (cdr m2))
		      if (not (equal xa xb)) 
		      return (poly-lrpo xa xb)
		      finally (return nil))
	       else (> l1 l2)))
      elseif (lrpo> m1 m2) then t
      else nil))

(defun poly-lrpo-equal (m1 m2)
  ;; return t iff they have the same structure, except 
  ;; the variables.
  (cond ((variablep m1) (variablep m2))
	((variablep m2) nil)
	((same-root m1 m2)
	 (and (eq (length (cdr m1)) (length (cdr m2)))
	      (sloop for ya in (args-of m1)
		     for yb in (args-of m2)
		     always (poly-lrpo-equal ya yb)))
	 )
	(t nil)))

(defun is-nilpotent-rule (rule &optional test)
  ; a rule is a nilpotent rule if it is of form 
  ;       x+x+x+ ... +x ---> 0
  ; where + is ac and 0 is the unit of +. Its abrev. form is
  ;       nx ---> 0
  ; where n is a natural number, called as the nilpotentistics
  (if (or $polynomial $symmetry-check) 
      (let ((ruleno (ruleno rule)) (lhs (lhs rule)))
	(if* (assoc ruleno $nilpotent-rules) 
	    then (assoc ruleno $nilpotent-rules)
	    elseif (and test 
			(ac-root lhs)
			(variablep (first-arg lhs))
			(null (remove0 (first-arg lhs) (cddr lhs)))
			(is-constant-term (rhs rule)))
	    then
	    (push rule $theory-rules)
	    (push (setq rule (list ruleno (length (args-of lhs)) 
				   (op-of lhs) (rhs rule)))
		  $nilpotent-rules)
	    rule))
    nil))

(defun has-nilpotent-rule (op)
  (sloop for xa in $nilpotent-rules
	if (equal op (caddr xa)) 
	return xa
	finally (return nil)))

(defun poly-size (term &aux l1)
  (if (variablep term) 1
      (cond
	((eq (op-of term) *+*) 
	 (add1 (apply '+ (mapcar 'poly-size (args-of term)))))
	((eq (op-of term) $*$)
	 (add (max 0 (times 10 (- (length (args-of term)) $xnx)))
	      (apply '+ (mapcar 'w-size (args-of term)))))
	(t (add (if (setq l1 (assoc (op-of term) $f-weights)) (cdr l1) 1)
		(apply '+ (mapcar 'poly-size (args-of term))))))))

(defun de-init-poly ()
  (setq *0* nil *0term* nil *-* nil *+* nil $*$ nil))

(defun poly-initialize ()
  (setq *0* (enter-op "0" 0))
  (setq *0term* (make-term *0* nil))

  (setq *+* (enter-op "+" 2))
  (set-infix *+*)
  (query-insert *+* $ac)
  (init-ac-arrays)

  (setq $*$ (enter-op "*" 2))
  (set-infix $*$)
  (set-op-status $*$ 'lr)

  (if (and (not (memq $*$ $ac)) (not (memq $*$ $associative))
	   (ok-to-continue "Is `*' associative ? "))
      (push $*$ $associative))

  (setq *-* (get-op-id "-"))
  (if (and (null *-*)
	   (ok-to-continue "Is `-' presented ? "))
      (setq *-* (enter-op "-" 1)))

  (if (null *-*) (query-insert (list *+* nil *0*) $divisible))

  (setq $reduce-system 2)
  (terpri) (princ "Polynomial machine is running ...")
  (terpri))

(defun mult-form-minus (list &aux mlis negative)
  ; Returns the multiset-form of list LIS.
  (sloop for xa in list do
	 (if (is-rooted-minus xa)
	     (setq negative t 
		   xa (cadr xa))
	     (setq negative nil))
	 (unless (sloop for l in mlis
			if (equal (car l) xa)
			return (rplacd l (if negative
					     (1- (cdr l)) (1+ (cdr l))))
			finally (return nil))
	   (push (cons xa (if negative -1 1)) mlis))
	 finally (return (nreverse mlis))))

(defun demult-form-minus (mlist)
  (demult-form (sloop for xa in mlist 
		      collect (if (< (cdr xa) 0)
				  (cons (negate-by-minus (car xa))
					(- (cdr xa)))
				  xa))))

(defun rest-elements (args-2 n1)
  ; return the last |args-2| - n1 elements of args-2 in order.
  (sloop for i from 1 to n1 do (setq args-2 (cdr args-2))
	finally (return args-2)))

(defun first-n-elements (args n1)
  ; return the first n1 elements of args in order.
  (sloop for i from 1 to n1 for xa in args collect xa))

(defun is-degree-qualified (sigma d1 vars)
  (or (= $discard-eqn-max-degree 0)
      (< d1 $discard-eqn-max-degree)
      (sloop for x in vars always (not (is-rooted-* (cdr (assoc x sigma)))))))
