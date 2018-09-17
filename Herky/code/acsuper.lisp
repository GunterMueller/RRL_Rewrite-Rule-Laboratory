(in-package "USER")

(defun ac-critical-pairs (rule &aux rule2)
  (if (eq $pick-rule-str 'm)
      (let ()
	(trace-message 3 "Computing critical pairs with: "
		       (write-rule rule))
	(setq rule2 (intro-with-rules rule)
	      rule (rule-x-to-y rule))
	(mark-superposed rule $aux-rules)
	(dolist (pair (make-pairs rule $aux-rules))
		(ac-critpairs pair))
	)
    (ac-critpairs rule)
    )
  t)

(defun ac-critpairs (pair)
  (let ((rule1 (cadr pair))
	(rule2 (caddr pair))
	(flag (cadddr pair)))
    (trace-message 4 "Computing critical pairs between "
		   (trace-ac-superposition rule1 rule2 flag))

    (if* (or (null $fopc) (is-condi-rule rule1) (is-condi-rule rule2))
	then (ac-superposition rule1 rule2 flag)
	elseif (pred-rulep rule1) 
	then (if (pred-rulep rule2) 
		 (pred-superposition rule1 rule2)
		 (pred-func-superposition rule1 rule2 flag))
	elseif (pred-rulep rule2)
	then (pred-func-superposition rule2 rule1)
	else (ac-superposition rule1 rule2 flag))))

(defun ac-superposition (r1 r2 flag) 
  ; - Tries to generate critical-pairs between the rules R1 and R2.
  ; Increase efficiency by superposing only once at the root.  If the two
  ; rules are the same, then try only one with the other after changing
  ; variables in one.  As critical-pairs are processed, stop if one of
  ; these rules gets deleted.
  ;
  (setq $superposed-subs nil)
  (if (memq $pick-rule-str '(m a)) (mark-superposed r1 r2))
  (if* (is-nilpotent-rule r1)
       then (super-with-nilpotent-rule r1 r2 flag)
       elseif (is-nilpotent-rule r2)
       then (super-with-nilpotent-rule r2 r1 flag)
       elseif $polynomial 
       then (poly-superposition r1 r2 flag)
       elseif (eq (ruleno r1) (ruleno r2)) 
       then

       (if $symmetry-check (setq $symmetry-terms (ref-symmetry-terms r1)))
       (if $top-only-var-check
	   (setq $top-only-vars (ref-top-vars r2)))
      
       (sloop for lhs1 in (commune-terms (lhs r1)) do
	      (ac-sup-term r2 r1 lhs1 lhs1 nil flag))

       else
       (if $symmetry-check
	   (setq $symmetry-terms 
		 (or (ref-symmetry-terms r1)
		     (ref-symmetry-terms r2))))
	
       (if $top-only-var-check
	   (setq $top-only-vars (ref-top-vars r1)))

       (sloop for lhs2 in (commune-terms (lhs r2)) do
	      (ac-sup-term r1 r2 lhs2 lhs2 nil flag))

       (when (and (not (is-deleted-rule r1))
		  (not (is-deleted-rule r2))
		  (eq flag 0))
	     (if $top-only-var-check
		 (setq $top-only-vars (ref-top-vars r2)))
	     (sloop for lhs1 in (commune-terms (lhs r1)) do
		    (ac-sup-term r2 r1 lhs1 lhs1 3 0)))
       ))

(defun super-with-nilpotent-rule (r1 r2 flag)
  (if (and (eq flag 2) (or (not $polynomial) (null *-*))
	   (same-root (lhs r1) (lhs r2)))
      (move-lhs-args (is-nilpotent-rule r1) r2)))

#|
(defun new-ac-super-at-roots (r1 r2)
  ;; the lhss of r1 and r2 are rooted by the same ac operator.
  ;; New trick to avoid extensions.
  (sloop for a1 in (rem-dups (args-of (lhs r1))) do
	 (sloop for a2 in (rem-dups (args-of (lhs r2))) 
		if (not (or (is-deleted-rule r1)
			    (is-deleted-rule r2)))
		do
		(if* (variablep a1) then
		     (if* (variablep a2) then
			  (process-new-ac-cp
			    r1 r2 
			    (removen a1 (lhs r1) 1) (removen a2 (lhs r2) 1)
			    (ncons (cons a1 a2)))
			  else
			  (process-new-ac-cp 
			    r1 r2
			    (removen a1 (lhs r1) 1) (removen a2 (lhs r2) 1)
			    (ncons (cons a1 a2))))
		     else
		     (if* (variablep a2) then
			  (process-new-ac-cp 
			    r2 r1
			    (removen a2 (lhs r2) 1) (removen a1 (lhs r1) 1)
			    (ncons (cons a2 a1)))
			  else
			  (sloop for sigma in (unifiers a1 a2 0 t) do
				 (process-new-ac-cp 
				   r1 r2 
				   (removen a1 (lhs r1) 1)
				   (removen a2 (lhs r2) 1)
				   sigma)))))))

(defun new-ac-super-same (r1 r2)
  ;; the lhss of r1 and r2 are rooted by the same ac operator.
  ;; New trick to avoid extensions.
  (let ((op (op-of (lhs r1))) (var (make-new-variable)))
    (sloop for a1 in (rem-dups (args-of (lhs r1))) do
      (sloop for a2 in (rem-dups (args-of (lhs r2))) 
	    if (not (or (is-deleted-rule r1)
			    (is-deleted-rule r2)))
	      do
	(if* (variablep a1) then
	    (if* (variablep a2) then
		(process-new-ac-cp 
		  r1 r2
		  (removen a1 (lhs r1) 1) (removen a2 (lhs r2) 1)
		  (ncons (list a1 op a2 var)) var)
		else
		(process-new-ac-cp
		  r1 r2
		  (removen a1 (lhs r1) 1) (removen a2 (lhs r2) 1)
		  (ncons (cons a1 a2)))
		(process-new-ac-cp 
		  r1 r2
		  (removen a1 (lhs r1) 1) (removen a2 (lhs r2) 1)
		  (ncons (list a1 op a2 var)) var))
	    elseif (not (variablep a2)) then
	    (sloop for sigma in (unifiers a1 a2 0 t) 
		  if (sloop for xa in (cdr sigma) 
			    thereis (not (variablep (cdr xa))))
		    do (process-new-ac-cp 
			 r1 r2
			 (removen a1 (lhs r1) 1) (removen a2 (lhs r2) 1)
			 sigma)))))

    (when (not (or (is-deleted-rule r1) (is-deleted-rule r2)))
      (sloop for lhs2 in (commune-terms (lhs r2)) do
	(ac-sup-term r1 r2 lhs2 lhs2 3 0)))))

(defun process-new-ac-cp (r1 r2 lhs1 lhs2 sigma &optional t2 t1)
  (let ((source (list (ruleno r1) (ruleno r2))) common l1 l2)
    (setq $ncritpr (add1 $ncritpr)
	  lhs1 (flat-applysigma sigma lhs1)
	  lhs2 (flat-applysigma sigma lhs2))

    (setq common (common-elements (cdr lhs1) (cdr lhs2)))
    (setq lhs1 (set-diff lhs1 common)
	  lhs2 (set-diff lhs2 common))
  
    (setq l1 (applysigma sigma (if t1 (list (rhs r1) t1) (ncons (rhs r1))))
	  l2 (applysigma sigma (if t2 (list (rhs r2) t2) (ncons (rhs r2)))))

    (setq t1 (flat-term (append lhs2 l1))
	  t2 (flat-term (append lhs1 l2)))
    (if (null (cddr t1)) (setq t1 (cadr t1)))
    (if (null (cddr t2)) (setq t2 (cadr t2)))
    (setq r1 (make-eqn t1 t2 nil source))
    (if-well-typed-eqn r1 (process-critpair r1))

    (sloop for sig2 in (set-unify (cdr lhs1) (cdr lhs2)) do
      (process-new-ac-cp2 lhs1 lhs2 l1 l2 sig2 source))
    ))

(defun process-new-ac-cp2 (lhs1 lhs2 l1 l2 sigma source &aux common)
  (setq $ncritpr (add1 $ncritpr)
	lhs1 (flat-applysigma sigma lhs1)
	lhs2 (flat-applysigma sigma lhs2))

  (setq common (common-elements (cdr lhs1) (cdr lhs2)))
  (setq lhs1 (set-diff lhs1 common)
	lhs2 (set-diff lhs2 common))
  
  (setq l1 (applysigma sigma l1)
	l2 (applysigma sigma l2))
  (setq l1 (flat-term (append lhs2 l1))
	l2 (flat-term (append lhs1 l2)))
  (if (null (cddr l1)) (setq l1 (cadr l1)))
  (if (null (cddr l2)) (setq l2 (cadr l2)))
  (setq l1 (make-eqn l1 l2 nil source))
  (if-well-typed-eqn l1 (process-critpair l1)))
|#

(defun set-unify (l1 l2)
  ;; this is not a complete set-unification procedure.
  (setq l1 (rem-dups l1) l2 (rem-dups l2))
  (sloop for xa in l1 nconc 
	 (sloop for xb in l2 append (ac-unification xa xb))))

(defun trace-ac-superposition (r1 r2 flag)
  (case flag
    (1 (format t "Extension of [~d] and Rule [~d]." (ruleno r1) (ruleno r2)))
    (2 (format t "Extensions of [~d] and [~d]." (ruleno r1) (ruleno r2)))
    (3 (format t  "Rule [~d] and (x + y) * z ---> (x * z) + (y * z)."  
	       (ruleno r1)))
    (t (format t "Rules [~d] and [~d]." (ruleno r1) (ruleno r2)))
    )
  (terpri))

(defmacro ac-critical-source ()
  `(caseq flag
     (1 (list (ruleno r1) (ruleno r2) 'ext1))
     (2 (list (ruleno r1) (ruleno r2) 'ext2))
     (t (list (ruleno r1) (ruleno r2)))
     ))

(defmacro process-ac-critical-pair (uni)
  ; cut from ac-sup-term in critical.lisp.
  (let ((tmp1 (gensym)) (tmp2 (gensym)) (lhs (gensym)) (rhs (gensym))
        (ctx (gensym)) (eqn (gensym)))
    `(let (,tmp1 ,tmp2 ,lhs ,rhs ,ctx ,eqn)
       (caseq flag
         (1 (setq ,tmp1 (or (cdr (assq *xex1* ,uni)) *xex1*)))
         (2 (setq ,tmp1 (or (cdr (assq *xex1* ,uni)) *xex1*)
                  ,tmp2 (or (cdr (assq *xex2* ,uni)) *xex2*))))
       
       (setq $ncritpr (add1 $ncritpr)
             ,lhs (applysigma ,uni
                   (rplat-in-by pos lhs2
                                (add-rest-args 
                                  (rhs r1)
                                  (if ,tmp1 
                                      (make-term (op-of sub)
                                                 (ncons ,tmp1)))))
                   )
             ,rhs (applysigma ,uni
                   (add-rest-args (rhs r2)
                                  (if ,tmp2
                                      (make-term (op-of sub) 
                                                 (ncons ,tmp2))))
                   )
             ,ctx nil
;	          (if (or (ctx r1) (ctx r2))
;		      (handle-conditions (ctx r1) (ctx r2) ,uni))
             ,eqn (make-eqn ,lhs ,rhs ,ctx source)
	     ,eqn (flatten-eqn ,eqn))

       (if-well-typed-eqn ,eqn (process-critpair ,eqn)))))

(defun is-superposed-sub (sub)
  (if $symmetry-check
      (let ((res (member0 sub $superposed-subs)))
	(if (not res)
	  (if $symmetry-terms 
	      (sloop for xl in $symmetry-terms 
		     if (member0 sub xl) 
		     return (setq $superposed-subs 
				  (append $superposed-subs xl))
		     finally (push sub $superposed-subs))
	    (push sub $superposed-subs)))
	res)))

(defun ac-sup-term (r1 r2 lhs2 sub pos flag &aux source unifs)
  ; sub is a subterm of lhs2, namely, the lhs of r2. 
  ; r1 will visit all subterms of lhs2. 
  ; r2 maybe an extended rule.
  ; If r1 is also an extended rule, in this case, r2 must be extednded, too,
  ; r1 does not need to visit all subterms of lhs2.

  (unless (is-superposed-sub sub)
      (cond ((eq pos 3) (setq pos nil))
            ((same-root (lhs r1) sub)
	     (when (setq unifs (unifiers (lhs r1) sub flag))
		   (setq source (ac-critical-source))
		   (sloop for uni in unifs 
			  if (or (not $polynomial)
				 (and (is-degree-qualified uni (product-degree (lhs r1)) (ref-lhs-vars r1))
				      (is-degree-qualified uni (product-degree (lhs r2)) (ref-lhs-vars r2))))
			  do
			  (setq $superposed-sub sub)
			  (trace-message 4"" 
					 (trace-superpose (ruleno r1) (ruleno r2) sub uni))
			  (if (if $ac-distree
				  (distree-process-ac-critical-pair uni)
				(process-ac-critical-pair uni))
			      (return nil))))))

      (if* (and (not (predicatep (op-of (lhs r1)))) (neq 2 flag)) then
	   (sloop for xa in (args-of sub) as l1 from 1 
		  if (or (is-deleted-rule r1)
			 (is-deleted-rule r2)) return nil 
		  else if (nonvarp xa) 
		  do (ac-sup-term r1 r2 lhs2 xa (append1 pos l1) flag)))))

(defmacro add-all-pairs (rule) 
  `(sloop with rule1 = ,rule
	  with ruleno = (ruleno rule1)
	  for rule2 in $rule-set 
	  if (and (not (is-deleted-rule rule2))
		  (> ruleno (ruleno rule2)))
	  do
	  (add-pairs rule1 rule2)))

(defun pick-ac-pair (&aux l1 done)
  ;(while (and $rules-to-pair 
  ;      (is-deleted-rule (car $rules-to-pair)))
  ;(pop $rules-to-pair))

  (while (not done)
    (if* (null $pair-set) 
	 then (setq l1 nil done t)
	 elseif (null (cdar $pair-set))
	 then
	 (setq $pair-set (cdr $pair-set))
	 else
	 (setq l1 (car $pair-set))
	 (sloop for xa in (cdr l1) do
		(setf (cdr l1) (cddr l1))
		(if (and (not (is-deleted-rule (cadr xa)))
			 (not (is-deleted-rule (caddr xa))))
		    (return (setq l1 xa done t)))
		finally (setq l1 nil))
	 (if l1 (setq done t))
	 ))
  l1)

(defun make-pairs (rule1 rule2)
  (let ((lhs1 (lhs rule1)) (lhs2 (lhs rule2)) 
	(psize (+ (lhsize rule1) (lhsize rule2)))
	pairs x1 x2)
    (setq x1 (ac-root lhs1)
	  x2 (ac-root lhs2))
    (push (list psize rule1 rule2 0) pairs)
    (if* (not $idem-superpose) then
	 (if (and x1 x2 (same-root lhs1 lhs2))
	     (push (list (add $ex2 psize) rule1 rule2 2) pairs))
	 else
	 (if (and x1 
		  (or (neq (ruleno rule1) (ruleno rule2))
		      (not $symmetry-check)))
	     (push (list (add $ex1 psize) rule1 rule2 1) pairs))
	 (when x2 
	       (if (neq (ruleno rule1) (ruleno rule2))
		   (push (list (add $ex1 psize) rule2 rule1 1) pairs))
	       (if (and x1 (same-root lhs1 lhs2))
		   (push (list (add $ex2 psize) rule1 rule2 2) pairs))))
    (nreverse pairs)
    ))

(defun ac-add-pairs (rule1 rule2)
  (let* ((lhs1 (lhs rule1))
	 (lhs2 (lhs rule2))
	 (psize (add (lhsize rule1) (lhsize rule2))) 
	 x1 x2)
     (setq x1 (ac-root lhs1)
	   x2 (ac-root lhs2))
     (add-pair (list psize rule1 rule2 0))
     (if* (not $idem-superpose) then
       (if (and x1 x2 (same-root lhs1 lhs2))
	   (add-pair (list (add $ex2 psize) rule1 rule2 2)))
       else
       (if (and x1 
		(or (neq (ruleno rule1) (ruleno rule2))
		    (not $symmetry-check)))
	   (add-pair (list (add $ex1 psize) rule1 rule2 1)))
       (when x2 
	 (if (neq (ruleno rule1) (ruleno rule2))
	     (add-pair (list (add $ex1 psize) rule2 rule1 1)))
	 (if (and x1 (same-root lhs1 lhs2))
	     (add-pair (list (add $ex2 psize) rule1 rule2 2)))))
     ))

(defun add-pair (pair &aux l1)
  (if (setq l1 (assoc (car pair) $pair-set))
      (nconc l1 (ncons pair))
      (setq $pair-set (insert (list (car pair) pair) 
			      $pair-set #'car-lessp))))

(defun add-pairs (rule1 rule2)
  (if (acceptable-pair rule1 rule2) 
      (if* $polynomial
	  then (if (and (is-general-rule rule1) (is-general-rule rule2))
		   (poly-add-pairs rule1 rule2))
	  elseif $ac 
	  then (ac-add-pairs rule1 rule2)
	  else (add-pair (list (add (lhsize rule1) (lhsize rule2)) rule1 rule2 0)))
      ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The following functions are for debugging.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun look-at-pairs (nums)
  (sloop for l3 in $pair-set do
    (sloop for pa in (cadr l3) 
	  as r1 = (cadr pa)
	  as r2 = (caddr pa)
	  as n1 = (ruleno r1)
	  as n2 = (ruleno r2)
	  if (or (memq n1 nums) (memq n2 nums))
          do (terpri) 
	  (princ (pair-info pa n1 n2)))))

(defun pair-info (pa &optional n1 n2)
  (uconcat "weight: " (car pa) 
           "  rule: " (if n1 n1 (ruleno (cadr pa)))
           " and rule: " (if n2 n2 (ruleno (caddr pa)))))

(defun look-at-pair-and (nums)
  (sloop with flag with i = 0
        with n1 = (car nums)
        with n2 = (cadr nums) 
        for pas in $pair-set do
    (sloop for pa in (cadr pas)
          as r1 = (cadr pa)
          as r2 = (caddr pa) do
      (setq i (add1 i))
      (when (and (= n1 (ruleno r1)) (= n2 (ruleno r2))) 
	(setq flag t) (terpri) (princ i) (princ ": ") (princ pa)))
    finally (return flag)))

(defun list-pairs ()
  (sloop with i = 0
        for pas in $pair-set do
    (sloop for pa in (cadr pas)
          as r1 = (cadr pa)
          as r2 = (caddr pa) do
      (setq i (add1 i))
      (terpri) 
      (princ (uconcat i ": weight = " (car pas) " r1 = "  (ruleno r1) 
                        ", r2 = " (ruleno r2) ", flag = " (cadddr pa))))))


;; This function was in polynomial.lisp
(defun move-lhs-args (ruleno-c rule)
  ; a rule is a nilpotent rule if it is of form 
  ;       x+x+x+ ... +x ---> 0
  ; where + is ac and 0 is the unit of +. Its abrev. form is
  ;       nx ---> 0
  ; where n is a natural number, called as the nilpotentistics
  ; "c" is a number and the root of the lhs of "rule" has nilpotent "c".
  ; If the lhs of "rule" has n copies of a smaller argument less then others,
  ; move c-n copies of that argument to the rhs.
  ; If not and there exists n copies of any arguments and c <= 2n,
  ; then move n arguments to the rhs.
  (let ((ruleno (car ruleno-c))
	(c (cadr ruleno-c))
	(lhs (mult-form (args-of (lhs rule)))) small)

    (if* (cdr lhs) then
      (if* (> ruleno (ruleno rule)) then
	; At first, partition lhs into big and small two sets.
	(sloop for xa in lhs as t1 = (car xa) do
	      (pop lhs)
	      (if (sloop for ya in lhs thereis (poly-lrpo (car ya) t1))
		  (push xa small)
		(setq lhs (append1 lhs xa)))))

      (if (and (null small) (null (cddr lhs)) 
	       (equal (rhs rule) (nth 3 ruleno-c)))

	  (setq small (ncons (if (> (cdar lhs) (cdadr lhs))
				 (car lhs) 
				 (cadr lhs)))))
      
      (if* small then
	(setq lhs (args-of (lhs rule)))
	(sloop for xa in small do (setq lhs (remove0 (car xa) lhs)))
	(setq lhs (if (cdr lhs)
		      (make-term (op-of (lhs rule)) lhs) 
		    (car lhs))
	      c (nconc (list (op-of (lhs rule)) (rhs rule))
		       (sloop for xa in small 
			     append (ntimes (- c (cdr xa)) (car xa))))
	      c (norm-term (flat-term c))
	      $ncritpr (add1 $ncritpr)
	      c (if (nequal lhs c) 
		    (make-eqn lhs c (ctx rule)
			      (list ruleno (ruleno rule) 'ext2)))
	      lhs (cancellation c))
	
	(cond ((null lhs) nil)
	      ((equal (setq lhs (orient-rule-time lhs)) '*reset*) 
	       (push c $eqn-set) (reset))
	      ((eq lhs '*kb-top*) nil)
	      (lhs (add-rule-time lhs)))
	elseif (> ruleno (ruleno rule)) then
	(make-rule-instances rule))
      )))
