(in-package "USER")

;; $superposed-subs contains a list of subterms of a lhs, which have been 
;; superposed with the other rule. That' is, there is no need
;; to superpose identical terms more than once.
;; $superposed-sub contains the lattes one.

(defun critpairs (rule)
  ; Generates critical pairs using RULE.  Returns t.
  ; There are essentially two ways of doing this after an unmarked-rule
  ; has been picked (there are two ways of doing that).  One is to go
  ; through the rule set and superpose this rule with all the earlier
  ; generated rules (Huet's paper discusses this). Another is to superpose
  ; this rule only with all the rules that have been picked already
  ; for computing critical pairs.
  ; This function makes use of the auxiliary global variable $AUX-RSET
  ; which contains either the rule set (for the first case) or only the
  ; marked-rules (for the second strategy). The user sets the strategy
  ; using the flag $CRIT-STR.  Critical-pairs are processed as and when
  ; they are generated, so the left-hand-side of many rules (including
  ; the ones currently being superposed) could have become reducible by
  ; newly generated rules.  Many superpositions can be saved by checking
  ; the global variable $DEL-RULES to see if this is the case.
  ;
  (if* ; (eq $condi 'i)
       ; then (induc-superposition rule)
       ; elseif
      $ac
      then (ac-critical-pairs rule)
      else

      (trace-message 3 "Compute critical pairs with: "
		     (terpri) (princ "  ") (write-rule rule))

      (setq $aux-rules (intro-with-rules rule)
	    rule (rule-x-to-y rule))

      (sloop with nruleno = $nrules
	     for xa in $aux-rules 
	     if (> (ruleno xa) nruleno)
	     return nil
	     else if (acceptable-pair rule xa) 
	     do
	     (superposition xa rule))

      ;(if (detachment-rule rule) (detachment-critical rule))
      )
  t)

(defmacro sos-check (rule1 rule2)
  `(or (null $support) 
       (not (is-source-type ,rule1 'user)) 
       ;; rule1 is an input eqn but not sos.
       (not (is-source-type ,rule2 'user))))

(defun acceptable-pair (rule1 rule2)
  (cond ((is-deleted-rule rule1) nil)
	((is-deleted-rule rule2) nil)
	((and (has-var-order-condition rule1)
	      (has-var-order-condition rule2)) nil)
	(t
	 (case $crit-with-str
	       (m t)
	       (o (> (ruleno rule1) (ruleno rule2)))
	       (a (if (superposed rule1 rule2) 
		      nil
		    (mark-superposed rule1 rule2)))
	       (t t)))
	))

(defun pure-critical-pairs (rule)
  (trace-message 3  "Compute critical pairs with: "
		 (terpri) (princ "  ") (write-rule rule))

  (setq $aux-rules (intro-with-rules rule)
	rule (rule-x-to-y rule))

  (sloop for xa in $aux-rules 
	 if (acceptable-pair xa rule)
	 do (pure-superposition xa rule))
  t)

(defun hyper-superpose (rule)
  ;; Simulate Hyperparamodulation, where rule will not be kept 
  ;; in the system.
  (when (listp $aux-rules)
	(setq rule (make-dummy-rule rule t))
	(push-end rule $subsume-rules)
	(sloop for xa in $aux-rules
	       if (is-deleted-rule rule)
	       return nil
	       else if (or (variablep (rhs xa)) (null (args-of (rhs xa))))
	       do (setq $superposed-subs nil $superposed-sub nil)
	       (case $kb
		     ((*pure* *distree*)
		      (pure-sup-term xa rule (lhs rule) t nil))
		     (t (sup-term xa rule (lhs rule) (lhs rule) t nil))
		     )
	       ))
  (if (is-source-type rule 'user) (push rule $aux-rules))
  )

(defun superposition (rule1 rule2)
  (if* (or (is-condi-rule rule1) (is-condi-rule rule2))
       then (func-superposition rule1 rule2)
       elseif (pred-rulep rule1) 
       then (if (pred-rulep rule2) 
		 (pred-superposition rule1 rule2)
		 (pred-func-superposition rule1 rule2))
       elseif (pred-rulep rule2) 
       then (pred-func-superposition rule2 rule1)
       else (func-superposition rule1 rule2)))

(defun func-superposition (r1 r2)
  ; - Tries to generate critical-pairs between the rules R1 and R2.
  ; Increase efficiency by superposing only once at the root.  If the two
  ; rules are the same, then try only one with the other after changing
  ; variables in one.  As critical-pairs are processed, stop if one of
  ; these rules gets deleted.
  (setq $superposed-subs nil $superposed-sub nil)
  (if* (eq (ruleno r1) (ruleno r2))
     then
     ;(if $condi (induc-idem-superposition r1))
     (if* (is-general-rule r1) 
	  then
         (sloop with diff-rhs = (nequal (rhs r1) (rhs r2))
               for lhs in (commune-terms (lhs r1))
               do (sup-term r2 r1 lhs lhs
			    (and diff-rhs (nequal (lhs r1) lhs)) nil)))
     else
     (if* (or (is-general-rule r2) (ctx r1))
	  then
         (sloop with diff-rhs = (nequal (rhs r1) (rhs r2))
               for lhs2 in (commune-terms (lhs r2))
               do (sup-term r1 r2 lhs2 lhs2 diff-rhs nil)))
     (if* (or (is-general-rule r1) (ctx r2)) then
         (if (not (or (is-deleted-rule r1) (is-deleted-rule r2)))
             (sloop for lhs1 in (commune-terms (lhs r1)) 
                   do (sup-term r2 r1 lhs1 lhs1 nil nil))))))

(defmacro pure-eq-sup-term (r1 r2)
  ;; When r1 is general, superposing r1 into r1.
  `(when (is-general-rule ,r1)
	 (pure-sup-term ,r2 ,r1 (first-arg (lhs ,r1)) t '(1))
	 (if (nonvarp (second-arg (lhs ,r1)))
	     (pure-sup-term ,r2 ,r1 (second-arg (lhs ,r1)) t '(2)))
	 ))

(defun pure-superposition (r1 r2)
  (setq $superposed-subs nil $superposed-sub nil)
  (if* (eq (ruleno r1) (ruleno r2)) 
       then
       (if (and (is-general-rule r1) (not (eq (op-of (lhs r1)) *=*)))
	   (pure-sup-term r2 r1 (lhs r1) nil nil))
       else

       (cond
	((eq (op-of (lhs r1)) *=*) ;; Try only superpose r2 into r1.
	 (if (not (eq (op-of (lhs r2)) *=*)) (pure-eq-sup-term r1 r2)))

	((eq (op-of (lhs r2)) *=*) ;; Try only superpose r1 into r2.
	 (pure-eq-sup-term r2 r1))

	(t ;; At first, superpose r1 into r2.
	 (if (is-general-rule r2)
	     (pure-sup-term r1 r2 (lhs r2) (nequal (rhs r1) (rhs r2)) nil))
	 ;; Then, superpose r2 into r1.
	 (if (and (is-general-rule r1) (not (or (is-deleted-rule r1) (is-deleted-rule r2))))
	     (pure-sup-term r2 r1 (lhs r1) nil nil)))
	)))

(defun sup-term (r1 r2 lhs2 sub root pos)
  ; Takes R1 and R2 and the subterm of the left-hand-side of R2 at POS
  ; (in the left-hand-side) to be unified with the lhs of the other
  ; rule.  The flag ROOT indicates if need to superpose at the root.
  ; If unifies, then the resulting critical-pair is processed at
  ; once.  If result is non-trivial, add the new rule which may
  ; delete other rules.  Depending on the flag IM-DEL (set by the
  ; user at the top-level), the deleted rules can be left in the
  ; equation set or be processed too.  This is repeated to superpose
  ; at all positions in one left-hand-side. If one of the rules gets
  ; deleted, stop at once.  This is indicated by C-FLAG.
  (if*  (not (is-superposed-sub sub)) then
      (if* root then (sup-term2 r1 r2 lhs2 sub pos))
      (if* (not (predicatep (op-of (lhs r1)))) then
          (sloop for xa in (args-of sub) as l1 from 1 
                if (or (is-deleted-rule r1) (is-deleted-rule r2))
		return nil
                else if (and (nonvarp xa) (not (is-skolem-op (op-of xa))))
		do (sup-term r1 r2 lhs2 xa t (append1 pos l1))))))

(defun pure-sup-term (r1 r2 sub root pos)
  ;; Superposing r1 into r2.
  (if* (not (is-superposed-sub sub)) then
      (if root (pure-sup-term2 r1 r2 sub pos))
      (sloop for xa in (args-of sub) 
	     as l1 from 1 
	     if (or (is-deleted-rule r1) (is-deleted-rule r2))
	     return nil
	     else 
	     do
	     (if (eq $del-rule-str 2) 
		 (while $eqn-set 
		   (if (eq $kb '*pure*)
		       (pure-process-equation (pop $eqn-set))
		     (distree-process-equation (pop $eqn-set)))
		   (if (or (is-deleted-rule r1) (is-deleted-rule r2))
		       (return-from pure-sup-term nil))
		   ))
	     (if (and (nonvarp xa) (not (is-skolem-op (op-of xa))))
		 (pure-sup-term r1 r2 xa t (append1 pos l1)))
	     )))

(defun sup-term2 (r1 r2 lhs2 sub pos)
  ; - auxiliay function of SUPTERM.
  (let (result sigma ctx)
     (setq sigma (unifier (lhs r1) sub))
     (if* sigma then
	  (setq $superposed-sub sub)
	  (trace-message 4 "" 
	       (trace-superpose (ruleno r1) (ruleno r2)	sub sigma))
;         (if* (or (ctx r1) (ctx r2)) 
;             (setq ctx (handle-conditions (ctx r1) (ctx r2) sigma)))
         (if* (not-falsep ctx) then
             (setq result 
		   (make-eqn
                        (flat-term (applysigma 
				     sigma (rplat-in-by pos lhs2 (rhs r1))))
                        (flat-applysigma sigma (rhs r2))
                        ctx 
                        (list (ruleno r1) (ruleno r2)))
                   ;;result (flatten-eqn result)
                   $ncritpr (add1 $ncritpr))
             (if-well-typed-eqn result (process-critpair result))))))

(defun pure-sup-term2 (r1 r2 sub pos &aux sigma)
  ;(add-time $unif-time) ;; this macro is very expensive.
  (when (setq sigma (if (eq $kb '*pure*)
			(unifier (lhs r1) sub)
		      (distree-unifier (lhs r1) sub 
				       (and (is-linear-rule r1) (is-linear-rule r2))
				       )))
	(incf $ncritpr)
	(setq $superposed-sub sub)
	(trace-message 4 "" 
		       (trace-superpose (ruleno r1) (ruleno r2)	sub sigma))

	(if (eq $kb '*distree*)
	    (distree-handle-critical-pair r1 r2 pos sigma)
	  (pure-process-critpair 
	   (make-eqn
	    (applysigma sigma (rplat-in-by pos (lhs r2) (rhs r1)))
	    (applysigma sigma (rhs r2))
	    nil
	    (list (ruleno r1) (ruleno r2)))
	   )
	  )))

(defun pure-sup-term3 (t1 t2 r1 r2)
  (when (if (eq $kb '*pure*) (unifier t1 t2) (distree-unifier t1 t2))
	(inconsistent-eqn 
	 (make-eqn *trueterm* *falseterm* nil
		   (list (ruleno r1) (ruleno r2))))
	))

(defun pure-unit-conflict-test (rule &aux term)
  ;; Superpose rule into the first arg of *=*-root rules.
  (cond
   ((eq (op-of (lhs rule)) *=*)
    (setq term (rename-x-to-y (lhs rule)))
    (sloop for xa in $rule-set
	   if (not (eq (op-of (lhs xa)) *=*))
	   do (pure-sup-term3 (list *=* (lhs xa) (rhs xa)) term xa rule)))

   (t
    (setq term (rename-x-to-y (list *=* (lhs rule) (rhs rule))))
    (sloop for xa in $subsume-rules
	   if (eq (op-of (lhs xa)) *=*)
	   do (pure-sup-term3 term (lhs xa) rule xa))
    )))

#|
(defun handle-conditions (ctx1 ctx2 sigma)
  (if* $condi
      then (setq $premises-set nil $var-premises nil)
           (nofalse-premises (merge-premises ctx1 ctx2) sigma)
      else (norm-ctx-and (flat-applysigma sigma ctx1)
                         (flat-applysigma sigma ctx2))))

(defun induc-superposition (rule)
  ; Computing critical pair between rule and all other rules with one side.
  (sloop for lhs in (commune-terms (lhs rule)) do
    (induc-sup-term rule lhs lhs nil)))

(defun induc-sup-term (rule lhs sub pos)
  ; if "sub" = f(v1, v2, ..., vn) where f is not free constructors, then
  ; computing critical pairs with definition rules.
  (if* (and (not (memq (op-of sub) $free-constructors))
           (sloop for a in (args-of sub) always (variablep a))) then
      (sloop with ruleno = (ruleno rule)
            for rule2 in (cdr (assoc (op-of sub) $op-rules)) 
            if (and (equal (car (rule-source rule2)) 'def)
                    (neq ruleno (ruleno rule2)))
              do (sup-term2 rule2 rule lhs sub pos)))
  (sloop for xa in (args-of sub) as l1 from 1 do
    (if* (nonvarp xa) 
        then (induc-sup-term rule lhs xa (append1 pos l1)))))

(defun induc-idem-superposition (rule &aux l1 l2 l3)
  (setq l2 (op-of (lhs rule)))
  (if* (or (eq l2 *=*) (memq l2 $commutative)) then 
      (idem-super-commu rule))

  (if* (and (not (truep (rhs rule))) (equal (op-of (lhs rule)) *=*)) then
     (setq l1 (unifier (first-arg (lhs rule)) (second-arg (lhs rule))))
     (if* l1 then
	  (setq $superposed-sub (first-arg (lhs rule)))
	  (trace-message 4 "" 
	       (trace-superpose (ruleno rule) (ruleno rule) 
				(first-arg (lhs rule)) l1))

         (setq $premises-set nil
               $var-premises nil
               l3 (nofalse-premises (ctx rule) l1))
         (if* (not-falsep l3) then
             (setf l2 (make-eqn *trueterm* 
                                (flat-applysigma l1 (rhs rule))
                                l3 (list 'idem (ruleno rule))))
	     (update-used-rules l2)
	     (incf $ncritpr)
             (if-well-typed-eqn l2 (process-critpair l2))))))
|#

(defun instance-delete-condition (rule1 rule2)
  ; As a completmentary of unit strategy for conditionals.
  (let* ((lhs2 (lhs rule2)) (rhs2 (rhs rule2))
         (pre2 (if* (predicatep (op-of lhs2))
                       then (list lhs2 rhs2) 
                       else (list (list *=* lhs2 rhs2) nil)))
         sigmas eqn)

    (sloop for pre in (cdr (ctx rule1)) 
          if (and (equal (cadr pre) (cadr pre2))
                  (setq sigmas (unifiers (car pre2) (car pre))))
            do (setq eqn (removen pre (ctx rule1) 1)
                     eqn (if* (cdr eqn) then eqn)
                     eqn (make-eqn (lhs rule1) (rhs rule1) eqn
                                   (list (ruleno rule1) (ruleno rule2))))
               (sloop with new for sigma in sigmas do
                 (setq new (applysubst-rule sigma eqn)
                       $ncritpr (add1 $ncritpr))
                 (trace-message
		  2 ""
		  (format t "Delete conditions of [~d] by [~d] ...~%"
			  (ruleno rule1) (ruleno rule2)))
                 (trace-message 4 "Instantiate condition ..."
				(write-eqn new))
                 (if-well-typed-eqn new (process-critpair new))))))

(defun process-critpair (eqn &aux result)
  ; The new criitcal pair EQN is processed immediately.
  ; If the delelting-rule-stradegy is set to 1, then process
  ; all new equations produced.
  (unless (eqn-is-too-big eqn)
;  (if $condi (setq eqn (condi-crit-checkeq eqn)))
  (when eqn
   (setq result (catch 'kb-top (process-equation eqn)))
   (case result
	 ((*changekb* *kb-top*) (throw 'kb-top result))
	 ((*newop* *sepa*) 
	  (sloop while $eqn-set do (process-equation (pop $eqn-set))))
	 (t (if* (eq $del-rule-str 2) 
		 (sloop while $eqn-set do (process-equation (pop $eqn-set))))
	    )))))

(defun pure-process-critpair (eqn &aux result)
  (unless (eqn-is-too-big eqn)
  (setq result (catch 'kb-top
		(if (eq $kb '*pure*)
		    (pure-process-equation eqn)
		  (distree-process-equation eqn))))
  (if (memq result '(*changekb* *kb-top*)) (throw 'kb-top result))))

(defun unit-rule (lhs rhs)
  (if* (or (variablep rhs) (null (cdr rhs)))
      (and (null (cdr (setq lhs (removen rhs (args-of lhs) 1))))
           (nequal (setq lhs (car lhs)) rhs)
           (or (variablep lhs) (null (cdr lhs))))))

(defun trace-superpose (ruleno1 ruleno2 sub sigma)
  (format $out-port "    Superposing Rule [~d] into " ruleno1)
  (write-term sub $out-port)
  (format $out-port " of Rule [~d] with the mgu:~%      [" ruleno2)
  (write-sigma sigma $out-port) (princ "]." $out-port) 
  (terpri $out-port)
  )

(defun trace-crit (rns crit &optional is-ass sigma)
  (case (first rns)
    (idem (princ "    By idempotency, the rule [" $out-port))
    (distr (princ "    Superpose the distribution law into the rule [" $out-port))
    (t (format $out-port "    Superpose Rule [~d] into Rule [" (first rns))))
  (format $out-port "~d] yields a critical pair:" (second rns))

  (terpri) (princ "        ")
  (if is-ass 
      (write-assertion rns crit)
    (write-eqn crit))
  (when sigma 
    (princ "    with the unifier [") (write-sigma sigma) (princ "].") (terpri)))
