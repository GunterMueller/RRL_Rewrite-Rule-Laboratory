(in-package "USER")

(defmacro distree-norm-term (term)
  ;  Apply mixed-strategy normalization on TERM.
  ;;  `(distree-norm-outermost ,term ,term0)
  `(or (distree-norm-with-sigma ,term nil) ,term))

(defmacro distree-rwonce-outermost (term)
  ; Rewrites TERM once at the first possible leftmost-outermost position.
  `(cond ((distree-rewrite-at-root ,term))
	 ((distree-outermost-rewrite-args ,term))))

(defun distree-knuth-bendix (&aux xa)
  ; The main body of distree knuth-bendix completion procedure.
  (while $del-eqns (distree-process-equation (cdr (pop $del-eqns))))
  (while $eqn-set (distree-process-equation (pop $eqn-set)))

  (if (setq xa (pick-unmarked-rule))
      (reset-kb (pure-critical-pairs xa))
    (empty-post-set)
    ))

(defmacro distree-norm-term-sigma (term sigma)
  `(cond
    ($block-cps (or (distree-norm-with-sigma ,term ,sigma) ,term))
    (t (setq ,term (applysigma ,sigma ,term)) 
       (or (distree-norm-with-sigma ,term nil) ,term))
    ))

(defmacro distree-orient-an-eqn (eqn)
  `(if (or (null $divisible) (setq ,eqn (cancellation ,eqn)))
       (when (not (eqn-subsumed ,eqn $subsume-rules))
	     (consistent-check ,eqn)
	     (orient-rule-time ,eqn)
	     )))

(defun distree-handle-critical-pair (r1 r2 pos sigma)
  (let ((lhs (rplat-in-by pos (lhs r2) (rhs r1)))
	(rhs (rhs r2))
	(source (list (ruleno r1) (ruleno r2)))
	)

    (trace-message 4 "Process "
		   (trace-distree-cp 
		    (applysigma sigma lhs) 
		    (applysigma sigma rhs)
		    source))

    (setq $reduce-times $reduce-max)

    (add-time $norm-time (let ()

;    ;; Check Prime-Superposition
;    (if $prime-cps 
;	(let ((lhs1 (applysigma sigma (lhs r1))))
;	  (when (and (nonvarp lhs1)
;		     (sloop for xa in (args-of lhs1)
;			    thereis (and (nonvarp xa)
;					 (distree-reducible xa))))
;	    (return-from distree-handle-critical-pair (incf $prime-cps)))))

    ;; Check Left-Composite-Superposition.
;    (if $left-cps
;	(if (distree-reducible-at-left (setq lhs (applysigma sigma lhs)) pos)
;	    (return-from distree-handle-critical-pair (incf $left-cps))
;	  (setq lhs (or (distree-norm-term-but-left lhs pos) lhs)))
      (setq lhs (distree-norm-term-sigma lhs sigma))
;      )

    (setq rhs (distree-norm-term-sigma rhs sigma))
    ))

    (unless (equal lhs rhs)
	    (setq lhs (make-eqn lhs rhs nil source))
	    (when (not (eqn-is-too-big lhs))
;		  (trace-message 4 "Process " (write-eqn lhs))
	      (if $trace-proof (update-used-rules lhs))
	      (when (setq lhs (distree-orient-an-eqn lhs))
		    (add-time $add-time (distree-add-rule lhs))
		    (if $check-unit-conflict
			(pure-unit-conflict-test lhs))
		    ))
	    )
    (setq $used-rule-nums nil)
    ))

(defun add-new-op-rules (rule old &aux new)
  (setq new (new-term nil nil t))
  (setq new (make-eqn old new nil (list 'deleted (ruleno rule))))
  (trace-message 3 "Introduce a new operator: " (write-eqn new))
  (add-time $add-time (distree-add-rule (subst-eqnq old new rule)))
  (add-time $add-time (distree-add-rule (make-new-rule new)))
  )

(defun have-common-subterm (rule)
  ;; return a subterm of rule which occurs more than once.
  (sloop for sub in (nonvar-subs (rhs rule))
	 if (is-subterm sub (lhs rule))
	 return sub))
 
(defun nonvar-subs (term)
  (if* (variablep term) then nil
       elseif (null (args-of term)) then nil
       elseif (and (eq (get-arity (op-of term)) 2)
		   (is-constant-term (first-arg term))
		   (is-constant-term (second-arg term))
		   (not (member (op-of (second-arg term)) $newops))
		   )
       then (ncons term)
       else (mapcan 'nonvar-subs (args-of term))))

(defun distree-process-equation (eqn)
  (trace-message 4 "Process " (write-eqn eqn))
  (if (setq eqn (add-time $norm-time (distree-normal-eqn eqn)))
      (if (setq eqn (distree-orient-an-eqn eqn))
	  (add-time $add-time (distree-add-rule eqn)))))

(defun distree-add-rule (rule &aux roses)
  ;; Add rule to the distree.
  (insert-whole-rule-to-distree rule)

  (add-rule-primitive rule)

  ;; Simplify lhss of other rules.
  (cond
   ((eq (op-of (lhs rule)) *=*) 
    (push-end rule $subsume-rules))

   ((order-condition rule)
    (sloop for eqn in $subsume-rules
	   for new = (pure-reduce-by-one-rule (lhs eqn) rule)
	   if new do
	   (setq $subsume-rules (delete1 eqn $subsume-rules))
	   (trace-message 3 "" (trace-reduce-lhs eqn))
	   (distree-clean-rule eqn) 
	   (setq new (make-eqn-from-deleted-rule eqn new (ruleno rule)))
	   (process-del-rule new eqn)
	   ))

   ((and (is-reduction rule)
	 (> $reduce-system 0))
    (setq roses (find-roses-in-distree rule))
    (dolist (rose roses) 
	    (reduce-rules-in-rose rule rose)
	    (reduce-lhss-in-rose rule rose))
    ))

  ;; Simplify rhss of other rules.
  (if (is-condi-reduction rule)
      (push-end rule $subsume-rules)
    (when (and roses 
	       (> $reduce-system 2))
	  (dolist (rose roses) (reduce-rhss-in-rose rule rose))))
  )

#|
(defun distree-reduce-at-root-by-one2 (rule term &aux sigma)
  ;;(mark term "TERM")
  ;;(mark (lhs rule) "LHS")
  ;;(mark (get-lhs-vars rule) "LHSVAR")
  ;;(mark $distree-sigma "SUBS")

  (sloop for var in (get-lhs-vars rule)
	 for sub in $distree-sigma do
	 (if (is-var-id var)
	     (push (cons var sub) sigma)
	   (if (not (equal sub (nth var $distree-sigma)))
	       (return-from distree-reduce-at-root-by-one2 nil))))

  (setq $distree-sigma sigma)

  ;;(mark $distree-sigma "SIGMA")

  (or (is-reduction rule) 
      (satisfy-order-condition rule sigma))
  )
|#

(defmacro reduce-one-rule-in-rose ()
  `(when (distree-reduce-at-root-by-one rule term)
	 (trace-message 3 "" (trace-reduce-lhs xa))
	 (distree-clean-rule xa) 
	 (setq xb (applysigma $distree-sigma (rhs rule))
	       xb (replace-term xb term (lhs xa))
	       xb (make-eqn-from-deleted-rule xa xb (ruleno rule))
	       )
	 (process-del-rule xb xa)
	 ))

(defun reduce-rules-in-rose (rule rose &aux xb term)
  (dolist (xa (rose-rules rose))
	  (when (not (eq xa rule))
		(setq term (lhs xa))
		(reduce-one-rule-in-rose))))

(defun reduce-lhss-in-rose (rule rose &aux xb term)
  (dolist (xa (rose-lhs-terms rose))
	  (when (not (is-deleted-rule (cdr xa)))
		(setq term (pop xa))
		(reduce-one-rule-in-rose))))

(defun reduce-rhss-in-rose (rule rose &aux xb term sigma)
  (dolist (xa (rose-rhs-terms rose))
	  (setq term (pop xa))
	  (when (setq sigma (clash-free-match (lhs rule) term))
		(clean-rhs-roses xa)

		(setq xb (applysigma sigma (rhs rule))
		      xb (replace-term xb term (rhs xa)))
		(remember-used-rule-num (ruleno rule))

		(if (nonvarp xb) (setq xb (distree-norm-term xb)))
		(trace-message 3 "" (trace-reduce-rhs xa xb))
		(change-rhs xa xb)
		(if $trace-proof (update-used-rules xa))
		(insert-rhs-to-distree xa)
		)))

(defmacro is-empty-rose (rose)
  `(not (or (rose-rules ,rose) 
	    (rose-lhs-terms ,rose)
	    (rose-rhs-terms ,rose))))

(defun distree-clean-rule (rule &aux (rose (rule-rose rule)))
  (setq $aux-rules (delete1 rule $aux-rules))
  (incf $num-del-rules)

  (setq $rule-set (delete1 rule $rule-set))
  (if $keep-deleted-rules (push-end rule $del-rules))
  (set-deleted-mark rule)

  (when rose
	(setf (rose-rules rose) (delete1 rule (rose-rules rose)))
	(dec-rule-nums-in-distree (rose-parent rose))
	(if (is-empty-rose rose) (delete-one-rose (rose-parent rose)))
	(setf (rule-rose rule) nil))

  (clean-lhs-roses rule)
  (if (> $reduce-system 2) (clean-rhs-roses rule))
  )

(defun clean-lhs-roses (rule)
  (dolist (rose (rule-lhs-roses rule))
	  (dolist (xa (rose-lhs-terms rose))
		  (when (eq (cdr xa) rule)
			(setf (rose-lhs-terms rose) 
			      (delete1 xa (rose-lhs-terms rose)))
			(if (is-empty-rose rose) 
			    (delete-one-rose (rose-parent rose)))
			)))
  (setf (rule-lhs-roses rule) nil)
  )

(defun clean-rhs-roses (rule)
  (dolist (rose (rule-rhs-roses rule))
	  (dolist (xa (rose-rhs-terms rose))
		  (when (eq (cdr xa) rule)
			(setf (rose-rhs-terms rose) 
			      (delete1 xa (rose-rhs-terms rose)))
			(if (is-empty-rose rose) 
			    (delete-one-rose (rose-parent rose)))
			)))
  (setf (rule-rhs-roses rule) nil)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Normalization functions.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun distree-unifier (t1 t2 &optional blocked)
  (if (setq t1 (nonac-unify t1 t2)) 
      (if (or blocked 
	      (empty-sub t1)
	      (not $block-cps)
	      (sloop for xb in t1 
		     always (or (variablep (cdr xb))
				(not (distree-reducible (cdr xb))))))
	  t1
	(let ()
	  (incf $block-cps)
	  (trace-message 4 "    Unblocked substitution deleted: ["
			 (write-sigma t1) (princ "]")
			 (terpri))
	  nil))))

(defun distree-reducible (term)
  (or (find-rule-in-distree term)
      (sloop for arg in (args-of term)
	     thereis (and (nonvarp arg) (distree-reducible arg)))
      ))

(defun distree-reducible-at-left (term pos)
  ;; Return t iff term/q is reducible, where q is a left position of pos.
  (if pos
      (or (sloop for i from 1 below (car pos)
		 for arg = (nth i term)
		 thereis (and (nonvarp arg)
			      (distree-reducible arg)))
	  (distree-reducible-at-left (nth (car pos) term) (cdr pos))
	  )))

(defun distree-normal-eqn (eqn &aux lhs rhs)
  (setq $reduce-times $reduce-max
	lhs (distree-norm-term (lhs eqn)) ; (rhs eqn)
	rhs (distree-norm-term (rhs eqn))) ; lhs
  (check-normalized-lhs-rhs)
  )

(defmacro second-part-of-norm-term-with-sigma ()
  `(cond ((memq op *true*false*) nil)

	 ((eq op *=*) 
	  (if (setq op (reduce-at-eq-root term))
	      op ;; op is a term now.
	    (if reduced term)))

	 ((setq op (find-rule-in-distree term))
	  ;; op is a rule now.
	  (loop-check term) 
	  (remember-used-rule-num (ruleno op))
	  (setq term (copy (rhs op)))
	  (or (distree-norm-with-sigma term $distree-sigma) term))
	    
	 (reduced term)
	 (t nil)
	 ))

(defun distree-norm-term-but-left (term pos)
  ;; Normalize term, assuming the subterms at left positions of pos
  ;; are irreducible.
  (if (variablep term) nil
    (let ((op (op-of term)) reduced)

      ;; Normalize the arguments of term.

      (sloop with newterm
	     for arg in (args-of term) 
	     for i from 1 do
	     (cond ((or (null pos) (> i (car pos)))
		    (setq arg (distree-norm-with-sigma arg nil)))
		   ((= i (car pos))
		    (setq arg (distree-norm-term-but-left arg (cdr pos))))
		   (t (setq arg nil))
		   )
	     (when arg
		   (if (null newterm)
		       (setf newterm (copylist term)
			     reduced t))
		   (setf (nth i newterm) arg))
	     finally (if newterm (setq term newterm)))
		   
      (second-part-of-norm-term-with-sigma)
      )))

(defun distree-norm-with-sigma (term sigma)
  ;; Return nil if term is already in normal form; otherwise,
  ;; return a normal form of term.
  ;; Destroy the sturcture of term.
  (if (variablep term)
      ;; akcl cannot have (assq var t), *empty-sub* is t.
      (if (not (eq *empty-sub* sigma)) (cdr (assq term sigma)))

    (let ((op (op-of term)) reduced)

      ;; Normalize the arguments of term.

      (sloop with newterm
	     for arg in (args-of term) 
	     for i from 1 do
	     (when (setq arg (distree-norm-with-sigma arg sigma))
		   (if (null newterm)
		       (setf newterm (copylist term)
			     reduced t))
		   (setf (nth i newterm) arg))
	     finally (if newterm (setq term newterm)))
		   
      (second-part-of-norm-term-with-sigma)
      )))

(defun distree-norm-outermost (term term0 &aux term2)
  ; Does left-most outermost normalization on TERM.
  (while (and (nonvarp term)
	      (nequal term term0)
	      (setq term2 (distree-rwonce-outermost term)))
    (setq term term2))
  term)

(defun distree-outermost-rewrite-args (term)
  ; Try to rewrite the children in leftmost-outermost order.
  (cond 
    ((sloop for xa in (args-of term) for i from 1
	    if (and (nonvarp xa) (setq xa (distree-rewrite-at-root xa)))
	    return (replace-nth-arg i term xa)
	    finally (return nil)))
    ((sloop for xa in (args-of term) for i from 1
	    if (and (nonvarp xa) (setq xa (distree-outermost-rewrite-args xa)))
	    return (replace-nth-arg i term xa)
	    finally (return nil)))
    ))

(defun distree-rewrite-at-root (term &aux (xa (op-of term)))
  ; returns nil if term cant be rewritten at root else rewritten term.
  (cond	((memq xa *true*false*) nil)
	((eq xa *=*) (reduce-at-eq-root term))
	((setq xa (find-rule-in-distree term))
	 (loop-check term) 
	 (remember-used-rule-num (ruleno xa))
	 (applysigma $distree-sigma (copy (rhs xa)))
	 )))

#|
(defun distree-mixed-normalize (term &aux reduced t2)
  ; Recursive function called by norm-mixed.
  ; Return nil if TERM is in normal form.
  (when (nonvarp term) 

	;; At first, repeatedly reduce the term at the root.
	(while (and (nonvarp term)
		    (setq t2 (distree-rewrite-at-root term)))
	       (setq term t2 reduced t))

	(when (nonvarp term) 
	      ;; Reduce the arguments of term.
	      (sloop for i from 1 to (get-arity (op-of term)) 
		     for xb = (distree-outmost-normalize (nth i term)) 
		     if xb 
		     do
		     (setq t2 t)
		     (setf (nth i term) xb))
	
	      (when t2 
		    (setq reduced t)
		    (setq term (distree-norm-with-bin term)))
	      )

	(if reduced term)
	))
|#
(defvar $eqn nil)
(defun trace-distree-cp (lhs rhs source)
  (if (null $eqn) (setq $eqn (make-eqn nil nil nil source)))
  (setf (lhs $eqn) lhs
	(rhs $eqn) rhs
	(eqn-source $eqn) source)
  (write-eqn $eqn)
  )
