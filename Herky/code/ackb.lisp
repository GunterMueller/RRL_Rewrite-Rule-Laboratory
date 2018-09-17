(in-package "USER")

(defun ac-knuth-bendix (&aux xa)
  ; The main body of knuth-bendix completion procedure.
  (while $del-eqns (ac-process-equation (cdr (pop $del-eqns))))
  (while $eqn-set (ac-process-equation (pop $eqn-set)))

  (if (setq xa (pick-unmarked-rule))
      (reset-kb (if $ac (ac-critical-pairs xa) (critpairs xa)))
    (empty-post-set)
    ))

(defun ac-add-rule (rule)
  (if $ac-distree 
      (ac-insert-rule-to-distree rule)
    ;;(ac-insert-whole-rule-to-distree rule)
    )
  (add-rule-complete rule)
  )

(defun ac-process-equation (eqn)
  (trace-message 4 "Processing " (write-eqn eqn))
  (setq eqn (add-time $norm-time (ac-normal-eqn eqn)))
  (if eqn (orient-an-eqn eqn)))

(defun ac-normal-eqn (eqn &aux lhs rhs)
  (if $ac-distree
      (setq $reduce-times $reduce-max
	    lhs (ac-distree-norm-term (lhs eqn))
	    $reduce-times $reduce-max
	    rhs (ac-distree-norm-term (rhs eqn))
	    )
    (setq $reduce-times $reduce-max
	  lhs (norm-ac-term (lhs eqn))
	  $reduce-times $reduce-max
	  rhs (norm-ac-term (rhs eqn))
	  ))
  (check-normalized-lhs-rhs)
  )

(defun norm-ac-term (old &aux new)
  ;; Ensure that the returned term is flattened.
  (if* (variablep old) then old 
      else
      (setq new (make-flat (norm-outermost old)))
      (if* (equal new old)
	   old
	   (norm-ac-term new))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Functions for flattening
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro first-ac-flat (term)
  `(if $mt (mt-first-ac-flat ,term) (flatten-term ,term)))

(defmacro mt-sort-args (args) 
  `(sort ,args #'(lambda (mt1 mt2) (total-term-ordering (car mt1) (car mt2)))))

(defun mt-first-ac-flat (term)
  ;; Transform all ac arguments into multisets of terms.
  (cond ((variablep term) term)
	((ac-root term) 
	 (let ((op (op-of term)))
	   (setq term (mult-form (args-of-same-root op (args-of term))))
	   (dolist (xa term) (setf (car xa) (first-ac-flat (car xa))))
	   (make-term op (cons 'm (mt-sort-args term)))))
	(t (make-term (op-of term) (mapcar 'first-ac-flat (args-of term))))))

(defmacro flatten-term (term)
  ;; this macro is called only by flat-term.
  `(if* $polynomial 
	then (poly-simplify ,term)
	elseif $ac then (if $mt (make-mt-flat ,term) (make-flat ,term))
	elseif $commutative 
	then (c-permutation ,term)
	else ,term))

(defmacro flat-term (term2) 
  ; Make sure every term in the system is flattend and brted.
  (let ((term (gensym)))
    `(let ((,term ,term2))
       (if (or (variablep ,term) (is-constant-term ,term))
	   ,term 
	   (add-time $brt-time
		     (if $fopc
			 (brt (flatten-term ,term))
			 (flatten-term ,term)))))))

(defun flatten-rule (rule)
  (change-lhs-rhs rule (flat-term (lhs rule)) (flat-term (rhs rule))))

(defun flatten-eqn (eqn)
  (change-lhs-rhs eqn (flat-term (lhs eqn)) (flat-term (rhs eqn)))
  ;(when (ctx eqn) (change-ctx eqn (flatten-premises (ctx eqn))))
  ;eqn
  )

#|
(defun flatten-premises (ctx)
  (if (eq (car ctx) '&&) 
      (cons '&& 
	    (sloop for pre in (cdr ctx) 
		  collect (make-pre (flat-term (first pre)) 
				    (flat-term (second pre))
				    (cddr pre))))
      (flat-term ctx)))
|#

(defun make-mt-flat (term)
  (cond ((variablep term) term)
	((null (args-of term)) term)
	((ac-root term) 
	 (dolist (xa (args-of-mt term)) 
	   (setf (car xa) (make-mt-flat (car xa))))
	 (make-term (op-of term)
		    (cons 'm (sort-merge-mt-args 
			       (op-of term) (args-of-mt term)))))
	(t (compress-flat (op-of term)
			 (mapcar 'make-mt-flat (args-of term))))))

(defun sort-merge-mt-args (op args &aux ans)
  (dolist (arg args)
    (setq ans (if (and (nonvarp arg) (eq op (op-of arg))) 
		  (merge-mt-list (args-of arg) ans)
		  (insert-mt-list arg ans))))
  ans)

(defmacro merge-mt-list (l1 l2)
  `(dolist (xa ,l1) (setq ,l2 (insert-mt-list xa ,l2))))

(defun insert-mt-list (ele lst2 &aux l1)
  (sloop for xa on lst2 
	 for xb = (car xa) do 
	 (cond ((equal (car ele) (car xb))
		(setf (car xa) (cons (car xb) (+ (cdr xb) (cdr ele))))
		(return lst2))
	       ((total-term-ordering (car ele) (car xb))
		(return (nconc l1 (cons ele xa))))
	       (t (setq l1 (cons (car xa) l1))))
	 finally (return (append1 lst2 ele t))))

(defmacro compress-flat (op args)
  `(if (ac-op-p ,op) 
       (flat-sort-args ,op ,args)
       (make-term ,op (if (comm-op-p ,op) (commu-exchange ,args) ,args))))

(defun make-flat (term)
  (cond ((variablep term) term)
	((null (args-of term)) term)
	(t (compress-flat (op-of term) (mapcar 'make-flat (args-of term))))))

(defun flat-sort-args (op args &optional ans)
  (dolist (arg args)
    (setq ans (if (and (nonvarp arg) (eq op (op-of arg))) 
		  (merge-list (args-of arg) ans 'total-term-ordering)
		  (insert-list arg ans 'total-term-ordering))))
  (make-term op ans))

(defmacro flat-applysigma (sigma term)
  `(let ((c ,term))
     (if $polynomial 
	 (poly-simplify (applysubst ,sigma c))
       (or (flat-subst-term ,sigma c) c))))

(defun flat-subst-term (sigma term)
  ;; return the flattened sigma(term).
  ;; return nil if sigma(term) = term.
  (cond ((variablep term) (cdr (assoc term sigma)))
	((null (args-of term)) nil)
	((ac-root term) 
	 (sloop with new = nil
		for arg in (args-of term) 
		if (setq new (flat-subst-term sigma arg))
		collect new into news
		else collect arg into olds
		finally (return (if news
				    (flat-sort-args
				      (op-of term) news olds)))))
	((comm-op-p (op-of term))
	 (let ((t1 (flat-subst-term sigma (first-arg term)))
	       (t2 (flat-subst-term sigma (second-arg term))))
	   (when (or t1 t2)
	     (if (null t1) (setq t1 (first-arg term)))
	     (if (null t2) (setq t2 (second-arg term)))
	     (if (total-term-ordering t1 t2)
		 (make-term (op-of term) (list t1 t2))
		 (make-term (op-of term) (list t2 t1))))))
	(t (sloop with new with done 
		  for arg in (args-of term) 
		  collect (if (setq new (flat-subst-term sigma arg))
			      (progn (setq done t) new) arg)
		  into news
		  finally (return (if done (make-term (op-of term) news)))
		  ))))

(defmacro is-assoc-under-c (t1 t2)
  `(and	(comm-op-p (op-of ,t1))
	(is-assoc-pair ,t1 ,t2)))

(defun is-assoc-pair (t2 t1)
   ; Return T iff T1 is of form "f(f(x, y), z)" and T2 of form
   ; "f(x, f(y, z))" or vice versa, where "f" is commutative.
  (and (nonvarp t1) 
       (not (assoc-op-p (op-of t1)))
       (nonvarp t2)
       (same-root t1 t2)
       (equal (length (args-of t1)) 2)
       (if (variablep (first-arg t1))
	   (and (assoc-pair-first-var t1)
		(if (comm-op-p (op-of t1))
		    (assoc-pair-first-var t2)
		    (assoc-pair-second-var t2)))
	   (and (assoc-pair-second-var t1)
		(if (comm-op-p (op-of t1))
		    (assoc-pair-second-var t2)
		    (assoc-pair-first-var t2))))))

(defun assoc-pair-first-var (t1 &aux (arg2 (second-arg t1)))
  (and (variablep (first-arg t1))
       (nonvarp arg2)
       (same-root t1 arg2)
       (variablep (first-arg arg2))
       (variablep (second-arg arg2))
       (not (equal (first-arg t1) (first-arg arg2)))
       (not (equal (first-arg t1) (second-arg arg2)))
       (not (equal (first-arg arg2) (second-arg arg2)))))

(defun assoc-pair-second-var (t1 &aux (arg1 (first-arg t1)))
  (and (variablep (second-arg t1))
       (nonvarp arg1)
       (same-root t1 arg1)
       (variablep (first-arg arg1))
       (variablep (second-arg arg1))
       (not (equal (second-arg t1) (first-arg arg1)))
       (not (equal (second-arg t1) (second-arg arg1)))
       (not (equal (first-arg arg1) (second-arg arg1)))))

(defun make-ass-com-op (op eqn ac-flag &aux ops)
  ;(if $has-history (start-push-history eqn))
  (if ac-flag 
      (format $out-port
	      "~%The operator ~s is associative & commutative (AC).~%"
	      (op-name op))
    (format $out-port
	    "~%The operator ~s is commutative.~%" (op-name op))
    )
  (setq eqn (make-dummy-rule eqn))
  (push eqn $theory-rules)

  (if (op-has-status op) (cancel-status op))

  (if* ac-flag
       then 
       (push op $ac) 
       (setq $commutative (deleten op $commutative 1))
       else
       (set-commutative op))

  (setq ac-flag (if ac-flag 'make-flat 'c-permutation))
      
  (setq ops (flatten-everything op ac-flag (ruleno eqn)))
  (if* (and ops (neq 'make-flat ac-flag)) (wash-def-rules ops))

  (reset-kb '*changekb*))

(defun flatten-everything (op &optional (flatten 'make-flat)
			      ruleno &aux def-rule-ops)
  ; Flatten the equations and rules in the current system.
  ; Delete the rules which have "op".
  ; If the ac is the first time introduced, then changeing the
  ; critical pair computing strategies.
  ; >>>>> 1/29/89
  (if $prove-eqns (flatten-witness ruleno))
  ; >>>>> 4/29/89
  (setq $p-commut-rules 
	(sloop for rule in $p-commut-rules 
	       if (not (member op rule)) collect rule))

  (setq $free-constructors (delq op $free-constructors))
  (if $post-ass-set (flatten-post-ass flatten))
  (setq def-rule-ops (flatten-rules2 op flatten ruleno))

  (setq $eqn-set (mapcar 'flatten-eqn $eqn-set)
	$post-set (mapcar 'flatten-eqn $post-set))

  ; If this is the first AC operator, then change the strategy of
  ; computing critical pairs.
  (when (and (eq flatten 'make-flat) (null (cdr $ac))) 
    (setq $block-cps 0
	  $norm-str 'o 
	  $pair-set nil
	  $pure nil)
    (init-ac-arrays)
    (dolist (xa $rule-set)
      (when (crit-unmarked xa)
	(setq xa (rule-x-to-y xa))
	(add-all-pairs xa))))
  def-rule-ops)

(defun flatten-rules2 (op flatten ruleno &aux l2 neweq def-rule-ops
			  (type (if (eq flatten 'c-permutation)
				    'commutative 'ac)))
  ; Auxillary function of "faltten-rules".
  (sloop for xa in $rule-set 
	 if (and (not (is-deleted-rule xa))
		 (op-occur-in op (lhs xa))) do
	 (trace-message 3 "  Delete "
			(trace-ac-in-rule xa op type))
	(if* (and $condi (equal (car (rule-source xa)) 'def)) 
	     then
	     (if* (eq flatten 'c-permutation)
		  (insert1 (op-of (lhs xa)) def-rule-ops))
	     else
	  (clean-rule xa) ; removes from op-list and if ac corr. pairs.
	  (setq l2 (make-eqn (lhs xa) (rhs xa) (ctx xa) 
			     (list 'deleted (ruleno xa) ruleno)))
	  (push l2 neweq)))

  (sloop for xa in $rule-set 
	 if (not (is-deleted-rule xa)) do
	 (set-rhs-vars xa '(nil nil nil))

	 (if* (op-occur-in op (rhs xa)) then
	      (trace-message 3 "  Simplifying the RHS of "
			     (trace-ac-in-rule xa op type))
	      (setq l2 (norm-term (funcall flatten (rhs xa))))
	      (change-rhs xa l2))

;	 (if* (ctx xa) (change-ctx xa (flatten-premises (ctx xa))))
	 )

  (setq $eqn-set (nreconc neweq $eqn-set))
  def-rule-ops)

(defun flatten-post-ass (flatten &aux l2)
   (setq l2 $post-ass-set
	 $post-ass-set nil)
   (sloop with xb for xa in l2 do
	  (setq xb (funcall flatten (cddr xa)))
	  (if* (not (equal (cddr xa) xb))
	       then
	       (if* (eq $kb '*ply*)
		    then
		    (process-ply-simple xb (cadr xa))
		    else
		    (trace-message 4 "Process proposition: "
				   (write-assertion (cadr xa) (cddr xa)))
		    (process-ass-simple xb (cadr xa)))
	       else 
	       (setq $post-ass-set (nconc $post-ass-set (ncons xa))))))

(defun elimcom (argsx argsy)
  (sloop for x in argsx
	 if (sloop for terms on argsy
		   as y = (car terms)
		   if (equal y x)
		   return (let ()
			    (setq argsy (nconc new-argsy (cdr terms)))
			    nil)
		   else collect y into new-argsy
		   finally (return t))
	 collect x into new-argsx
	 finally (return (cons new-argsx argsy))))

(defun multi-com (args)
  (sloop for term in args
	 if (and (variablep term)
		 (sloop for l in vars-argsx
			if (equal (car l) term)
			return (rplacd l (add1 (cdr l)))
			finally (return nil)))
	 do nil
	 else if (and (nonvarp term)
		      (sloop for l in non-vars-argsx
			     if (equal (car l) term)
			     return (rplacd l (add1 (cdr l)))
			     finally (return nil)))
	 do nil
	 else if (variablep term)
	 collect (cons term 1) into vars-argsx
	 else collect (cons term 1) into non-vars-argsx 
	 finally (return (cons vars-argsx non-vars-argsx))))

(defun wash-def-rules (ops)
  ; "ops" are operators of which the definition rules
  ; containing a newly commutative operators. 
  ; If their definition can be simplified, then save their old
  ; definition structure (or cover-set) in $non-comm-cover-sets
  ; and delete them from $cover-sets.
  (sloop with del for op in ops do
    (setq del nil)
    (sloop with result with rul3
	   for rul1 in (cdr (assoc op $op-rules)) 
	   if (equal (car (rule-source rul1)) 'def) do
	   (setq rul3 (flatten-eqn rul1))
	   (if* (sloop for rul2 in result thereis (similar-eqn rul3 rul2))
		then (clean-rule rul1) (setq del t)
		else (push rul3 result)))
;    (if* del then
;	(setq del (assoc op $cover-sets))
;	(push del $non-comm-cover-sets ))
    ))

(defun trace-ac-in-rule (xa op flatten)
  (format t "Rule [~d], because it contains the ~s ~s.~%"
	  (ruleno xa) flatten (op-name op))
  (trace-message 3  "" (write-rule xa))
  )

;; Functions from commutative.lisp
;; (in-package "USER")

(defmacro c-permu (term)
   `(if $commutative (c-permutation ,term) ,term))

(defun c-permutation (term)
  ; Return the standard form of TERM r.p.t. commutative theory.
  (cond	((variablep term) term)
	((comm-op-p (op-of term))
	 (make-term (op-of term) 
		    (commu-exchange (mapcar 'c-permutation (args-of term)))))
	(t (make-term (op-of term) 
		      (mapcar 'c-permutation (args-of term))))))

;;; Handle pseudo-commutativity.

(defun is-p-commut-pair (t1 t2)
  (and $symmetry-check
       (ac-root t1)
       (same-root t1 t2)
       (equal (length (cdr t1)) (length (cdr t2)))
       (null (remove0 (cadr t1) (cddr t1)))
       (null (remove0 (cadr t2) (cddr t2)))
       (is-commut-pair (cadr t1) (cadr t2))))

(defun p-commut-qualified-coef (c1 c2)
  (or (eq (setq c1 (+ c1 c2)) 0)
      (and (setq c2 (has-nilpotent-rule *+*))
	   (eq c1 (second c2)))))

(defun is-p-commut-poly (poly eqn &aux num)
  (when (and  $symmetry-check
	      ;; (eq (length poly) 2) gives an error in akcl.
	      (equal (length poly) 2)
	      (p-commut-qualified-coef (cdar poly) (cdadr poly))
	      (is-commut-pair (caar poly) (caadr poly)))

	(if* (or (eq (cdar poly) 1) (eq (cdadr poly) 1))
	    then
	    (setf (lhs eqn) (caar poly)
		  (rhs eqn) (caadr poly))
	    (make-ass-com-op (op-of (lhs eqn)) eqn
			     (assoc-op-p (op-of (lhs eqn))))
	    t
	    else
	    (setf num (min (abs (cdar poly)) (abs (cdadr poly)))
		  (lhs eqn) (make-term *+* (demult-form-minus
					    (ncons (cons (caar poly) num))))
		  (rhs eqn) (make-term *+* (demult-form-minus
					    (ncons (cons (caadr poly) num)))))
	    eqn)))

(defun sort-op-args (term &aux (op (op-of term)))
  ; Sort the arguments of op in term.
  (setq term (sort (if (memq op $associative)
		       (args-of-same-root op (args-of term))
		     (args-of term))
		   'total-term-ordering))
  (if $polynomial
      (make-term op term)
      (recover-op op term)))

(defun recover-op (op args)
  (if (cddr args)
      (if (op-has-lr-status op)
	  (progn
	    (setq args (reverse args))
	    (sloop with t1 = (list op (cadr args) (car args))
		   for arg in (cddr args) do
		   (setq t1 (list op arg t1))
		   finally (return t1)))
	  (sloop with t1 = (list op (car args) (cadr args))
		 for arg in (cddr args) do
		 (setq t1 (list op t1 arg))
		 finally (return t1)))
      (make-term op args)))

(defun p-commut-reduce-others (rule &aux l2)
  ;; rule is of form (ruleno op1 op2 num-of-args-of-op1)
  (sloop with rnum = (car rule)
	 for xa in $rule-set 
	 if (and (not (is-deleted-rule xa))
		 (not (eq rnum (ruleno xa)))
		 (neq (car (rule-source xa)) 'def)) do
    (if* (setq l2 (reduce-by-p-commut rule (lhs xa)))
	 then
	 (trace-message 3 "  Delete rule:" (write-rule xa))
	 (clean-rule xa) ; removes from op-rules and if ac corr. pairs.
	 (setq l2 (make-eqn l2 (rhs xa) (ctx xa) 
			    (list 'deleted (ruleno xa) rnum)))
	 (process-del-rule l2 xa)
	 elseif (and (> $reduce-system 2)
		     (nonvarp (rhs xa))
		     (setq l2 (reduce-by-p-commut rule (rhs xa))))
	 then
	 (trace-message 3 "  The right hand side is reducible:"
			(terpri) (princ "    ") (write-rule xa))
	 (setq l2 (if* (variablep l2) then l2
;		      elseif $condi
;		      then (condi-norm-rhs l2)
		      else (norm-term l2)))
	 (change-rhs xa l2))))

;;;; Handle REAL commutativity.

(defun is-commut-pair (t1 t2)
    (and (nonvarp t1)
	 (nonvarp t2)
	 (same-root t1 t2) 
	 (equal (length (args-of t1)) 2)
	 (variablep (first-arg t1))
	 (variablep (second-arg t1))
	 (equal (length (args-of t2)) 2)
	 (eq (first-arg t1) (second-arg t2))
	 (eq (first-arg t2) (second-arg t1))
	 (if (ac-c-root t1) 
	     (break "Commutative operator found again: is-commut-pair")
	   t)
    ))

(defun commune-terms (term)
  ;  Return the equivalent term class of TERM in the commutative theory. 
  (if* (variablep term) then (ncons term) 
      elseif (and (eq (op-of term) *=*) (null (cdddr term)))
      then (sloop for xa in (if $commutative
			       (commune-terms2 term) 
			       (ncons term))
		 append (list xa (list (op-of xa) 
				       (second-arg xa)
				       (first-arg xa))))
      elseif $commutative 
      then (commune-terms2 term) 
      else (ncons term)))

(defun commune-terms2 (term)
  (if (variablep term)
      (ncons term)
      (let ((op (op-of term)) (args (args-of term)))
	(cond ((null args) (ncons term))
	      ((member op $commutative) 
               (rem-dups
		   (sloop for xa in (commune-terms2 (car args)) nconc
		       (sloop for xb in (commune-terms2 (cadr args)) nconc
			  (list (make-term op (list xa xb))
				(make-term op (list xb xa)))))))
	      (t (rem-dups (sloop for args1 in 
			     (product-lists (mapcar 'commune-terms2 args))
		           collect (make-term op args1))))))))

;;;; functions used to be in pcmisc.l

(defun commu-exchange (args)
   (if (total-term-ordering (first args) (second args))
       args
       (reverse args)))

(defun thereis-p-commut-rule (op1 op2)
  (sloop for xa in $p-commut-rules
	if (and (equal op1 (cadr xa)) (equal op2 (caddr xa)))
	return xa
	finally (return nil)))
