(in-package "USER")

(defun get-small-pair (t1 t2)
  ;; Return a pair of (s1 s2) such that s1 is a variable in t1
  ;; and s2 is a subterm of t2.
  (cond ((variablep t1)
	 (if (or (variablep t2) (null (args-of t2))) (list t1 t2)))
	((variablep t2) (if (args-of t1) (list t1 t2)))
	((same-root t1 t2)
	 (cond
	  ((null (args-of t1)) nil)
	  ((null (cdr (args-of t1)))
	   (get-small-pair (first-arg t1) (first-arg t2)))
	  ((op-has-rl-status (op-of t1))
	   (sloop for xa in (reverse (args-of t1))
		  as ya in (reverse (args-of t2))
		  if (not (equal xa ya))
		  return (get-small-pair xa ya)))
	  (t ; (op-has-lr-status (op-of t1))
	   (sloop for xa in (args-of t1)
		  as ya in (args-of t2) 
		  if (not (equal xa ya))
		  return (get-small-pair xa ya)))
	  ))
	(t nil)
	))

(defun get-var-condition (t1 t2)
  ;; Return a multiset of variables.
  (setq t1 (mult-diff3 (mult-form (all-vars-of t1)) 
		       (mult-form (all-vars-of t2))))
  (if (sloop for m in t1 thereis (< (cdr m) 0)) t1))

(defun set-order-condition (t1 t2 eqn &aux pair)
  ;; Return a condition under which t1 > t2.
  ;;(setq s1 (kbo-size t1) s2 (kbo-size t2))
  (cond 
   ((setq pair (get-small-pair t1 t2))
    (setf (order-condition eqn) (cons (get-var-condition t1 t2) pair)))
   ((setq pair (get-small-pair t2 t1))
    (exchange-lr eqn)
    (setf (order-condition eqn) (cons (get-var-condition t2 t1) pair))
    )
   ((and (eq $ordering 's) (eq (kbo-size t1) (kbo-size t2)))
    (setq pair (get-var-condition t1 t2))
    (when (eq (length pair) 2)
	  (setq pair (if (> (cdar pair) 0) 
			 (list (caar pair) (caadr pair))
		       (list (caadr pair) (caar pair))))
	  (setf (order-condition eqn) (cons nil pair)))
    )))

(defmacro has-order-condition (rule)
  `(and $order-condition (order-condition ,rule)))

(defmacro has-var-order-condition (rule)
  `(and $order-condition 
	(cdr (order-condition ,rule))
	(car (order-condition ,rule))))

(defun satisfy-order-condition (rule sigma &aux (size 0))
  (when (has-order-condition rule)
	(dolist (m (car (order-condition rule)))
		(incf size (* (kbo-size (applysigma sigma (car m))) (cdr m))))
	(when (or (> size 0)
		  (and (= size 0)
		       (or (null (cdr (order-condition rule)))
			   (kbo>= (applysigma sigma (cadr (order-condition rule)))
				  (applysigma sigma (caddr (order-condition rule))))
			   )))

	 ;(princ "HI: ") (write-rule rule)
	 ;(mark size "SIZE")
	 t)
	))

(defun orient-an-eqn (eqn)
  ; Try consisient checking.
  ; Try to orient EQN into rule.
  ; If possible, then add the new rule obtained into the system.
  ; Return NIL.
  (if (and eqn $divisible) (setq eqn (cancellation eqn)))
  (when (and eqn 
	     ;;(not (eqn-is-too-big eqn))
	     (not (eqn-subsumed eqn $subsume-rules)))
	(consistent-check eqn)
	(if (and (or (not $symmetry-check)
		     (not (move-eqn-lhs-args eqn)))
		 (setq eqn (orient-rule-time eqn)))
	    (add-rule-time eqn))))

(defun pure-orient-an-eqn (eqn)
  ; Try consisient checking.
  ; Try to orient EQN into rule.
  ; If possible, then add the new rule obtained into the system.
  ; Return NIL.
  (if (and eqn $divisible) (setq eqn (cancellation eqn)))
  (when (and eqn 
	     ;;(not (eqn-is-too-big eqn))
	     (not (eqn-subsumed eqn $subsume-rules)))
	(consistent-check eqn)
	(orient-rule-time eqn)))

(defun orient-eqn-to-rule (eqn)
  ; tries to orient the equation EQN as a rule.  If possible,
  ; then returns a rule.  If EQN is invalid or un-orientable, return NIL.
  ; If EQN is invalid in the sense that the variable set of either
  ; term is not contained in the other then the function INVALID-RULE
  ; is called which tries to add a new operator and form two rules.
  (if (null (rhs eqn)) (setf (rhs eqn) *trueterm*))
  (case (is-rule-candidate eqn (is-oneway eqn))
	(1 (try-to-orient eqn nil))
	(2 (exchange-lr eqn) (try-to-orient eqn nil))
	(3 (try-to-orient eqn (not (is-oneway eqn)))))
  ) 

(defmacro try-to-orient2 (t1 t2 twoway)
  `(if* (lrpo ,t1 ,t2) then 1
	elseif (lrpo ,t2 ,t1)
	then (if ,twoway
		 2
	       (progn 
		 (princ "Orient the equation from right to left? (y n) ")
		 (if (eq 'y (ask-a-choice '(y n))) 2))
	       )))

(defmacro try-to-orient3 (t1 t2 twoway eqn)
  `(if* (lrpo ,t1 ,t2) then (return (make-new-rule ,eqn))
	elseif (and ,twoway (lrpo ,t2 ,t1)) 
	then (exchange-lr ,eqn) (return (make-new-rule ,eqn))))

(defun try-to-orient (eqn twoway &aux (t1 (lhs eqn)) (t2 (rhs eqn))
			  sugg)
  ; twoway indicates if the terms T1 and T2 can be oriented only
  ; twoway (because of varsets) or they can be compared both ways.
  ; If they are not currently orderable, call functions SUGG-PREC
  ; and ASK-USER to get help from the user.  If the terms are
  ; orientable, return the rule to be added.
  (cond
   ((make-easy-new-rule eqn t1 t2 twoway))
   ((is-p-commut-pair t1 t2) (make-p-commut-rule eqn) nil)
   ((setq sugg (precedence-suggestions (op-list t1) (op-list t2) twoway))
    (ask-user eqn t1 t2 twoway sugg))
   ((and (eq $ordering 's) $order-condition (set-order-condition t1 t2 eqn))
    (make-new-rule eqn 3))
   ((or $automatic (and (= $post-posi 1) (< $old-nrules $nrules)))
    (if $hyper-superpose
	(hyper-superpose eqn)
      (trace-message 4 "  Postpone unorientable " (write-eqn eqn))
      )
    nil)
   (t (ask-user eqn t1 t2 twoway nil))
   ))

(defun kbo> (t1 t2 &optional vars (s1 (kbo-size t1)) (s2 (kbo-size t2)))
  ;; fun > var > cont.
  (cond ((variablep t1) nil)
	((variablep t2) (occurs-in t2 t1))
	((> s1 s2)
	 (or vars (is-subset (var-list t2) (var-list t1)))
	 ; t
	 )
	((= s1 s2)
	 (or (grt-prec (op-of t1) (op-of t2))
	     (and (eqops (op-of t1) (op-of t2))
		  (cond
		   ((null (args-of t1)) nil)
		   ((null (cdr (args-of t1)))
		    (kbo> (first-arg t1) (first-arg t2)))
		   ((op-has-rl-status (op-of t1))
		    (sloop for xa in (reverse (args-of t1))
			   as ya in (reverse (args-of t2))
			   if (not (equal xa ya))
			   return (kbo> xa ya)))
		   ((not (commutativep (op-of t1)))
		    ;; (op-has-lr-status (op-of t1))
		    (sloop for xa in (args-of t1)
			   as ya in (args-of t2) 
			   if (not (equal xa ya))
			   return (kbo> xa ya)))
		   ))))))

(defun kbo>= (t1 t2 &optional (s1 (kbo-size t1)) (s2 (kbo-size t2)))
  ;; fun > var > cont.
  (cond ((variablep t1) 
	 (if (variablep t2)
	     (< t1 t2) 
	   (null (args-of t2))))
	((variablep t2) (or (args-of t1) (> s1 s2)))
	(t (or (> s1 s2)
	       (and (= s1 s2)
		    (or (grt-prec (op-of t1) (op-of t2))
			(and (eqops (op-of t1) (op-of t2))
			     (cond
			      ((null (args-of t1)) nil)
			      ((null (cdr (args-of t1)))
			       (kbo>= (first-arg t1) (first-arg t2)))
			      ((op-has-rl-status (op-of t1))
			       (sloop for xa in (reverse (args-of t1))
				      as ya in (reverse (args-of t2))
				      if (not (equal xa ya))
				      return (kbo>= xa ya)))
			      ((not (commutativep (op-of t1)))
			       ;; (op-has-lr-status (op-of t1))
			       (sloop for xa in (args-of t1)
				      as ya in (args-of t2) 
				      if (not (equal xa ya))
				      return (kbo>= xa ya)))
			      ))))))))

(defun make-easy-new-rule (eqn t1 t2 twoway)
  ;; Return either a rule or nil.
  (cond ((eq $ordering 's) 
	 (let ((s1 (kbo-size t1)) (s2 (kbo-size t2)))
	   (cond ((kbo> t1 t2 t s1 s2) 
		  (cond
		   ((setq s1 (get-var-condition t1 t2))
		    (setf (order-condition eqn) (ncons s1))
		    (make-new-rule eqn 3))
		   (t (make-new-rule eqn))
		   ))
		 ((and twoway (kbo> t2 t1 t s2 s1)) 
		  (exchange-lr eqn)
		  (cond 
		   ((setq s1 (get-var-condition t2 t1))
		    (setf (order-condition eqn) (ncons s1))
		    (make-new-rule eqn 3))
		   (t (make-new-rule eqn))
		   ))
		 (t nil))))
	(t (cond ((lrpo t1 t2) (make-new-rule eqn))
		 ((and twoway (lrpo t2 t1)) 
		  (exchange-lr eqn)
		  (make-new-rule eqn))
		 (t nil)
		 ))))

(defmacro man-order-warning ()
  `(when $lrpo
	 (terpri) 
	 (princ "Orientation of equations being done manually.") (terpri) (terpri)
	 (princ "!!!!!! Warning: Rewriting may not terminate !!!!") (terpri)
	 (terpri) (terpri)
	 (if (ok-to-continue) (setq $lrpo nil) (go asktop))))

(defun ask-user (eqn t1 t2 twoway sugg)
  ; Asks the user for help when orienting rules.  It takes a
  ;	    list of possible precedence relations and prompts the user
  ;	    to either choose a list of them, add status, add new
  ;	    operators, or hand orient the rule.
  (prog (l3 cmd old-precedence old-eqop-list)
	(terpri) (princ "Trying to orient Equation: ") (terpri)
	(princ "  ") (write-eqn eqn)
    asktop
    (print-sugg-info t1 t2 sugg twoway eqn)
    (princ 
"Type Abort, Display, Drop, Equiv, Left, Lrule, Makeeq, Operator,"
)   (terpri) (princ 
"     Postpone, Quit, Right, Rrule, Status, Twoway, Undo, or Help."
)
    (terpri) (princ "HERKY>KB> ")

    (setq cmd (choose-str (setq l3 (read-atom 'none))
	      '(abort display drop equivalence help 
		      left lrule makeeq operator postpone quit
		      right rrule status twoway undo)))

;    (try-to-open-log-port cmd '(abort display help quit))

    (if (is-number-string l3) (save-cmd l3)
      (if (symbolp l3) (save-cmd-end l3)))

    (selectq cmd
      (abort (push eqn $post-set) (reset))
      (quit (push eqn $post-set)  (reset))
      (display (display-op-stats) (go asktop))
      (drop (return nil))
      (equivalence 
       (if (null old-precedence) 
	   (setq old-eqop-list (copy $eqop-list)
		 old-precedence (copy $precedence)))
       (when (ext-equivalence) 
	     (try-to-orient3 t1 t2 twoway eqn)
	     (setq sugg (remove-sugg sugg)))
       (go asktop))
      (help (help-file *help-order*) (go asktop))
      (lrule (man-order-warning) (return (make-new-rule eqn)))
      (left (add-crit-rule eqn) (return nil))
      (makeeq (return (make-eq t1 t2 eqn)))
      (operator
	 (add-operator-defn eqn (get-lhs-vars eqn) (get-rhs-vars eqn))
	 (return nil))         
      (postpone (push eqn $post-set) (return nil))
      (rrule
         (if* (not twoway) then 
	    (princ "Sorry - the relation will never be sound.") (terpri)
	    (go asktop)
           else
	   (man-order-warning)
	   (exchange-lr eqn)
	   (return (make-new-rule eqn))))
      (right (exchange-lr eqn) (add-crit-rule eqn) (return nil))
      (status
       (if (ext-status) (try-to-orient3 t1 t2 twoway eqn))
       (go asktop))
      (twoway
	(add-crit-rule eqn) 
	(setq eqn (copy eqn))
	(exchange-lr eqn)
	(add-crit-rule eqn) 
	(return nil))
      (undo
       (if old-precedence 
	   (setq $precedence old-precedence
		 $eqop-list (if old-eqop-list old-eqop-list $eqop-list)
		 old-precedence nil
		 sugg (precedence-suggestions
		       (op-list t1) (op-list t2) twoway))
	   (format t "Nothing can be undo! Please use quit.~%"))
	   (go asktop)
	   )
      (otherwise
	(when (not (is-number-string l3)) 
	  (princ "Incorrect input: ")
	  (princ l3) (terpri)
	  (go asktop))

	(if (null old-precedence) (setq old-precedence (copy $precedence)))

	(case (orient-use-new-prec t1 t2 l3 sugg twoway)
	      (1 (return (make-new-rule eqn)))
	      (2 (exchange-lr eqn) (return (make-new-rule eqn))))
	(setq sugg (remove-sugg sugg))
        (go asktop))
      )))

(defun orient-use-new-prec (t1 t2 l3 sugg twoway)
   (prog (l1 l2 good)
	; Read in suggestions and reseve old $precedence.
        (setq l1 (if (io-eoln $in-port) 
		     (ncons l3)
		     (cons l3 (read-args)))
	      l3 (copy $precedence))
	(terpri-cmd)

	; Test whether the suggestions are good.
	(sloop for i in l1 do
	    (when (and (is-number-string i) 
		       (setq l2 (nth (1- (s2n i)) sugg))) 
	      (if* (grt-prec (cadr l2) (car l2))
		   then (princ "Invalid number, try again.") (terpri)
			(setq $precedence l3)
		        (return)
		   else (add-sugg (car l2) (cadr l2))
		        (setq good t))))
	(when good 
	  ;; Orient the equation using the new precedence.
	  (if (setq l1 (try-to-orient2 t1 t2 twoway))
              (return l1)
	      (format t "~%Sorry did not work, try again.~%"))) 
        (return nil)))

(defun comp-rule (r1 r2)
  ; Returns T if r1 should be ordered before r2 in a rule-set.
  (< (lhsize r1) (lhsize r2)))
#|
  (cond ((truep (ctx r1))
         (if (truep (ctx r2))
             (<= (lhsize r1) (lhsize r2))
             t))
        ((truep (ctx r2)) nil)
        (t (<= (lhsize r1) (lhsize r2))))
|#

(defun comp-eqn (e1 e2)
  ;  Returns T if e1 should be ordered before e2 in a rule-set.
  (cond ((truep (ctx e1))
         (if* (truep (ctx e2))
             then  (lessp (size (lhs e1)) (size (lhs e2)))
             else t))
        ((truep (ctx e2)) nil)
        (t (lessp (size (lhs e1)) (size (lhs e2))))))

(defun make-eq (t1 t2 eqn)
  (setq t1 (if* $condi
	       (make-term *=* (commu-exchange (list t1 t2)))
	     (make-term *eq* (commu-exchange (list t1 t2))))
	t1 (norm-term t1))
  (if* (truep t1) then nil
      elseif (falsep t1) then (refuted-result (eqn-source eqn))
      else
      (setf (lhs eqn) t1)
      (setf (rhs eqn)  *trueterm*)
      (add-rule-time (make-new-rule eqn)))
  'm)

(defun instantiate-lhs (eqn) 
  (terpri) 
  (princ "Instantiating the equation with constants: ") (terpri)
  (princ "    ") (write-eqn eqn)
  (princ "    because its LHS of the head is a variable.")
  (terpri)
  (sloop with type = (get-op-type (op-of (rhs eqn)))
	for op from *first-user-op* below $num-ops
	if (and 
	     (is-constant-op op)
	     (type-cohere type (get-op-type op)))
	do (process-equation (subst-eqn (lhs eqn) (ncons op) eqn))))

#|
(defun condi-orient-an-eqn (eqn &optional eqn2)
  ; Try consisient checking.
  ; Try to orient EQN into rule.
  ; If possible, then add the new rule obtained into the system.
  ; Return NIL.
  (when (ctx eqn) (setq eqn (release-premises eqn)))
  (when (falsep (lhs eqn)) (refuted-result (eqn-source eqn)))

  (if (and eqn $divisible) (setq eqn (cancellation eqn)))
  (when eqn
	(consistent-check eqn)
	(if (and $symmetry-check (move-eqn-lhs-args eqn))
	    nil
	  (orient-eqn-add-rule eqn))))
|#

(defmacro pseudo-term-ordering-seq (s1 s2)
  `(sloop for xa in ,s1 for xb in ,s2 
	  if (not (equal xa xb)) return (pseudo-term-ordering xa xb)))

(defun pseudo-term-ordering (s1 s2)
  ;  Returns t if S1 is less than S2.
  (cond ((equal s1 s2) nil)
	((and (variablep s1) (variablep s2)) (< s1 s2))
	((variablep s1) t)
	((variablep s2) nil)
	((or (truep s2) (falsep s2)) nil)
	((or (truep s1) (falsep s1)) t)
	((lrpo s1 s2) nil)
	((lrpo s2 s1) t)
	((same-root s1 s2)
	 (if (equal (length s1) (length s2)) 
	      (pseudo-term-ordering-seq (args-of s1) (args-of s2))
	      (< (length s1) (length s2))))
	(t (operator-ordering (op-of s2) (op-of s1)))))

(defmacro total-term-ordering-seq (s1 s2)
  `(sloop for xa in ,s1 for xb in ,s2 
	  if (not (equal xa xb)) return (total-term-ordering xa xb)))

(defun total-term-ordering (s1 s2 &aux l1 l2)
  ; Returns t if S1 is greater than S2.
  (cond ((equal s1 s2) nil)
	((and (variablep s1) (variablep s2)) (>= s1 s2))
	((variablep s1) nil)
	((variablep s2) t)
	((or (truep s1) (falsep s1)) nil)
	((or (truep s2) (falsep s2)) t)
	((same-root s1 s2)
	 (setq l1 (length s1)) (setq l2 (length s2))
	 (if (eq l1 l2)
	     (total-term-ordering-seq (args-of s1) (args-of s2))
	   (> l1 l2)))
	(t (total-op-ordering (op-of s1) (op-of s2)))))
