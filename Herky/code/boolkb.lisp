(in-package "USER")

(defun bool-knuth-bendix (&aux xa)
  ; The main body of knuth-bendix completion procedure.
  (while $del-eqns (bool-process-equation (cdr (pop $del-eqns))))
  (while $eqn-set (bool-process-equation (pop $eqn-set)))

  (if* (setq xa (pick-unmarked-rule))
	then
	(reset-kb (critpairs xa))
	elseif $post-ass-set then
	(terpri) (princ "Processing all postponed assertions ...") (terpri)
	(sloop for i from 1 
	       if (and (< i $immediate) (setq xa (pop $post-ass-set)))
	       do
	       (trace-message 4 "Process proposition: "
			      (write-assertion (cadr xa) (cddr xa)))
	       (order-ass (cddr xa) (cadr xa)) 
	       else return nil)
	(reset-kb t)
	))

(defun bool-process-equation (eqn)
  (trace-message 4 "Processing  " (write-eqn eqn))
  (setq eqn (add-time $norm-time (bool-normal-eqn eqn)))
  (if eqn (if (truep (rhs eqn))
	      (process-assertion eqn)
	    (orient-an-eqn eqn))))

(defun bool-add-rule (rule)
  (cond ((is-reduction rule)
	 (add-rule-complete rule)
	 (if $post-ass-set (reduce-post-ass rule)))
	(t (add-crit-rule rule))
	))

(defun reduce-post-ass (rule &aux l2)
  ; use "rule" to reduce the assertions in $post-ass-set. If one is get
  ; reduced, then process it immediately.
   (setq l2 $post-ass-set
	 $post-ass-set nil)
   (sloop with xb for xa in l2 do
     (if* (setq xb (reduce-by-one-rule (cddr xa) rule)) 
	then (trace-message 4 "Process proposition: "
			    (write-assertion (cadr xa) (cddr xa)))
	     (process-ass-simple xb (cadr xa))
        else (setq $post-ass-set (nconc $post-ass-set (ncons xa))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Normalize asssertions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun process-assertion (eqn &aux (lhs (lhs eqn)) (so (eqn-source eqn)))
  (if* (is-input-ass eqn) then
       (complete-well-typed lhs)
       (process-ass lhs so)
       else 
       (process-ass-simple lhs so)))

(defmacro domain-rulep (rule) `(not (predicatep (op-of (lhs ,rule)))))

(defun process-ass-simple (ass source)
  (if* ass then
       (add-time $norm-time (setq ass (norm-bool-term ass))) ; normalization
       (order-ass ass source)))

(defmacro process-ass2 (ass source) `(process-ass-simple (btp-trans ,ass) ,source))
(defmacro process-ass1 (ass source) 
      `(process-ass2 
	 (if (eq $more-break 'n) (skolemize ,ass) (break-ass ,ass ,source)) 
	 ,source))

(defun process-ass (ass source &aux (op (op-of ass)) l1)
  ; Add a new equation, doing all of the simplifications that we know how 
  ; to do. At first, try to reduce the size of ass. Then try to break ass
  ; to small sub-assertions. then try to skolemize, then boolean ring 
  ; transfomation ...
  (cond ;; 
    ((eq op *true*) nil)
    ((eq op *false*) (refuted-result source))
    ((eq op *and*) (sloop for x in (args-of ass) do (process-ass x source)))
    ((eq op *xor*) (process-ass1 ass source))
    ((memq op *exist*all*)
     (process-ass (skolemize-away-quants ass ass nil) source))
    ((eq op *or*)
     (if (and (not (eq $more-break 'n)) (greaterp (or-count ass) 3))
	 (sloop for xa in (break-at-or ass) do (process-ass xa source))
	 (process-ass1 ass source)))
    ((eq op *->*)
     (if* (equal (op-of (first-arg ass)) *or*) 
	  then 
	  (setq l1 (args-of (first-arg ass)))
	  (sloop for xa in l1 do 
		 (process-ass (list *->* xa (second-arg ass)) source))
	  elseif (equal (op-of (second-arg ass)) *and*) 
	  then
	  (setq l1 (args-of (second-arg ass)))
	  (sloop for xa in l1 do 
		 (process-ass (list *->* (first-arg ass) xa) source))
	  else (process-ass1 ass source)))
    ((eq op *equ*)
     (if* (truep (first-arg ass))
	  then  (process-ass (second-arg ass) source)
	  elseif (truep (second-arg ass))  
	  then (process-ass (first-arg ass) source)
	  elseif (has-quantifier ass)
	  then
	  (process-ass (list *->* (first-arg ass) (second-arg ass)) source)
	  (process-ass (list *->* (second-arg ass) (first-arg ass)) source)
	  else
	  (process-ass1 (make-term *xor* (cons *trueterm* (args-of ass))) source)))
    ((eq op *not*)
     (setq l1 (first-arg ass)
	   op (op-of l1))
     (cond
       ((eq op *true*) (refuted-result source))
       ((eq op *false*) nil)
       ((eq op *not*) (process-ass (first-arg l1) source))
       ((eq op *or*) (sloop for xa in (args-of l1) do
			    (process-ass (list *not* xa) source)))
       ((eq op *->*)
	(process-ass (first-arg l1) source)
	(process-ass (list *not* (second-arg l1)) source))
       ((eq op *equ*) (process-ass (make-term *xor* (args-of l1)) source))
       ((eq op *xor*) (process-ass (make-term *equ* (args-of l1)) source))
       ((memq op *exist*all*)
	(process-ass (list *not* (skolemize-away-quants l1 ass t)) source))
       (t (process-ass1 ass source))))
    ((eq op *eq*)
     (if* (equal (length ass) 3) 
	  then (push (make-eqn (first-arg ass) 
			       (second-arg ass) nil source) $eqn-set)
	  nil
	  else (process-ass-simple ass source)))
    (t (process-ass-simple ass source))))

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
      elseif (eq (op-of ass) *not*) then
	(list *not* (break-ass (first-arg ass) source flag))
      elseif (is-bool-op (op-of ass)) then
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
   (let ((func (get-new-operator $func-name)) (args (free-vars ass)))
     (setq func (enter-op func (length args)))
     (terpri) (princ "  Let") ; (display-one-arity2 func)
     (setq func (make-term func args))
     (princ " ") (write-term func) 
     (princ " stand for ") (write-term ass) (terpri)
     (if* (predicatep (op-of ass)) then
	  (set-predicate (op-of func))
	  (if (quantifierp (op-of ass)) 
	      (subst-quant-form func ass source)
	      (process-ass2 (list *equ* func ass) source))
	  else
	  (push (make-eqn ass func nil source) $eqn-set))
     func))

(defun or-count (ass)
   ; Count the number of ors on the top level of a ass.
   (if* (equal (op-of ass) *or*) 
      then (+ 1 (or-count (first-arg ass)) (or-count (second-arg ass)))
      else 0))

(defun break-at-or (ass)
   ; Substitute a predicate for ass.
   ; We call process-ass to introduce a new constraining equation,
   ; and we return a value that should be used for the variable.
   ; If flag is true, then just return ass.
   (let ((args (args-of-same-root *or* (args-of ass))) 
	 func term asses vars)
      (sloop while (> (length args) 4) do
            (setq term (pop args)
                  vars (var-list term))	  
            (sloop for i from 1 to 2 do
               (setq term (list *or* term (car args))
                     vars (intersection vars (var-list (pop args)))))
	    (setq func (get-new-operator $func-name)
		  func (enter-op func (length vars))
		  func (make-term func vars))
  	    (set-arity (op-of func) (length vars))
	    (push (list *equ* term func) asses)
   	    (push-end func args))

      (setq term (pop args))
      (sloop for arg in args do (setq term (list *or* term arg)))
      (push term asses)

      (terpri) (princ "Following assertion") (terpri) (princ "    ")
      (write-term ass) (terpri) 
      (setq asses (reverse asses))
      (princ "    is broken into") (terpri)
      (sloop for xa in asses do (princ "    ") (write-term xa) (terpri))
      (terpri)
      asses))

(defun trivial-simplify (ass &aux ass1 op)
  (if* (variablep ass) then ass else
       (setq op (op-of ass))
   (cond 
    ((eq op *equ*)
     (if* (truep (first-arg ass))
	  then (second-arg ass)
          elseif (truep (second-arg ass))  
	  then (first-arg ass)
	  else ass))
    ((eq op *not*)
     (if* (variablep (first-arg ass)) then ass else
	  (setq ass1 (first-arg ass)
		op (op-of ass1))
	  (cond 
	     ((eq op *true*) *falseterm*)
	     ((eq op *false*) *trueterm*)
 	     ((eq op *not*) (first-arg ass1))
	     ((eq op *equ*) (make-term *xor* (args-of ass1)))
	     ((eq op *xor*) (make-term *equ* (args-of ass1)))
	     (t ass))))
    (t ass))))


(defun negate-predicate (pred &aux (op (op-of pred)))
  (if (truep pred)
      *falseterm*
      (cond
	((eq op *false*) *trueterm*)
	((eq op *xor*) (negate-xor-args (args-of pred)))
	(t (m-xor-m pred *trueterm*)))
      ))

(defun negate-xor-args (args)
  (if* (member0 *trueterm* args) then
      (setq args (removen *trueterm* args 1))
      (if* (null args) then *falseterm*
	  elseif (cdr args) then (make-term *xor* args) 
	  else (car args))
      else
      (m-xor-p *trueterm* (cons *xor* args))))

;(in-package "USER")

(defun bool-normal-eqn (eqn)
  ;; If eqn is an assertion, do nothing;
  ;; if eqn is equality, call ac-normal-eqn or pure-normal-eqn.
  (cond ((and (is-assertion eqn) (equal (op-of (lhs eqn)) *=*))
	 (trace-message 4 "Transform assertion " (write-eqn eqn))
	 (let ((lhs (first-arg (lhs eqn))) (rhs (second-arg (lhs eqn))))
	   (change-lhs-rhs eqn lhs rhs))
	 (trace-message 4 "  to equation " (write-eqn eqn))
	 (if $ac (ac-normal-eqn eqn) (pure-normal-eqn eqn)))
	((is-assertion eqn) eqn)
	((is-prop-eqn eqn)
	 (change-lhs-rhs eqn (eqn2assertion eqn) nil)
	 )
	(t (if $ac (ac-normal-eqn eqn) (pure-normal-eqn eqn)))))

(defun norm-ctx-and (t1 t2)
  ; Normalize conjunction of T1 and T2 if different.
  ; Return T1 if equal, T1 is in normalized form.
  (cond ((truep t2) t1)
	((truep t1) (norm-term t2))
	((falsep t1) t1)
	((equal t1 t2) (norm-term t1))
        (t (norm-term (simp-and (list t1 t2))))))

(defun norm-bool-innermost (term)
  (setq $reduce-times $reduce-max)
  (if (or (truep term) (variablep term) (falsep term)) 
      term
      (let ((op (op-of term)) new-term)
	(cond 
	  ((eq op *xor*)
	   (setq term (norm-xor-args term)
		 new-term (bool-rewrite-at-root term)))
	  ((eq op *and*)
	   (setq term (norm-and-args term)
		 new-term (bool-rewrite-at-root term)))
	  (t (if* (and (not (well-typed3 term))
		       (is-type-predicate (op-of term)))
		  (setq term *falseterm* 
			new-term nil)
		  (setq term (norm-ac-term term)
			new-term term))))

	(if new-term
	    (if (and (nonvarp new-term)
		     (memq (op-of new-term) *xor*and*))
		(norm-bool-innermost new-term)
	      new-term)
	  term))))

(defun norm-xor-args (xor-term &aux new-args reducible)
  (setq new-args (sloop for arg in (args-of xor-term)
			as new-arg = (norm-bool-innermost arg)
			if (nequal new-arg arg) 
			do  (setq reducible t)
			collect new-arg))
  (if* reducible
       (simp-xor new-args)
       xor-term))

(defun norm-and-args (and-term &aux new-args continue reducible)
  (setq new-args
	(sloop for arg in (args-of and-term)
	       as new-arg = (norm-bool-innermost arg)
	       if (nequal new-arg arg) 
	       do (if* (eq (op-of new-arg) *xor*)
		       (setq continue t)
		       (setq reducible t))
	       collect new-arg))
  (if* continue
      then (norm-bool-innermost (simp-and new-args))
      elseif reducible then (simp-and new-args)
      else and-term))

(defun bool-rewrite-at-root (term &aux (op (op-of term)))
  ; Returns rewritten term iff term can be rewritten.
  (cond
    ((eq *xor* op) (reduce-xor-term (args-of term)))
    ((eq *and* op) (reduce-and-term term))
    (t nil)))

(defun bool-reduce-by-one-rule (term rule)
  (or (and (same-root term (lhs rule))
	   (bool-reduce-by-one-at-root term rule))
      (sloop for xa in (args-of term) for i from 1
	     if (and (nonvarp xa) (setq xa (bool-reduce-by-one-rule xa rule)))
	     return (replace-nth-arg i term xa)
	     finally (return nil))))

(defun bool-reduce-by-one-at-root (term rule &aux (op (op-of term)))
  ; return the reduced term by rule.
  (when (same-root term (lhs rule)) 
    (cond
      ((eq op *and*) (reduce-and-term term (ncons rule)))
      ((eq op *xor*) (reduce-xor-term (args-of term) (ncons rule)))
      ($polynomial (poly-reduce-by-one-at-root term rule))
      (t (ac-reduce-by-one-at-root term rule)))))

(defun reduce-xor-term (args &optional rules)
  ; This operation is not integrated with AC because its high
  ; complexicity and rare usage.
  ; lhs of most rules are not rooted by "xor".
  (sloop for rule in (or rules (rules-with-op *xor* $op-rules))
	 with rest-of-xor-args
	 with rest-of-and-args
	 with match-res
	 with new
	 do 
    (setq $false-rhs nil)
    (if* (and (null (ctx rule))
	     (setq match-res (match-bool-xor (args-of (lhs rule)) 
					     args (eq $fast-match 2))))
	then (remember-used-rule-num (ruleno rule))
	;; Structure of the value returned by match-bool-xor is
	;;    (rest-of-xor-args rest-of-and-args . substitution)
	(setq rest-of-xor-args (pop match-res)
	      rest-of-and-args (pop match-res)
	      new (applysubst match-res (rhs rule))
	      new (make-term *and* (if* (equal '(nil) rest-of-and-args)
				      then (ncons new)
				      else (cons new rest-of-and-args)))
	      new (make-term *xor* (cons new rest-of-xor-args)))
	(return new))))

(defun reduce-and-term (term &optional rules)
  ; "term" is rooted by "and". 
  ; If "term" is reducible at the root, then return the reduced term.
  ; Otherwise, nil.
  (sloop for rule in (or rules (rules-with-op *and* $op-rules))
	with rest-of-args
	with match-res
	with res
	do
    (setq $false-rhs (falsep (rhs rule)))
    (if* (and (null (ctx rule))
	     (setq match-res (match-set (lhs rule) term (eq $fast-match 2))))
	;; Structure of the value returned by match-set is
	;;    (rest-of-args . substitution)
	then (remember-used-rule-num (ruleno rule))
	     (setq rest-of-args (pop match-res)
		   res (flat-term (applysubst match-res (rhs rule))))
	     (if* (null rest-of-args) 
		 then (return res)
		 else (return (simp-and (cons res rest-of-args)))))))

