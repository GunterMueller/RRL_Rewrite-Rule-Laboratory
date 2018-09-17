;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")



#+franz
(declare (special $subs $subs2))

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
  ; using the flag $CRIT_STR.  Critical-pairs are processed as and when
  ; they are generated, so the left-hand-side of many rules (including
  ; the ones currently being superposed) could have become reducible by
  ; newly generated rules.  Many superpositions can be saved by checking
  ; the global variable $DEL-RULES to see if this is the case.
  ;
  (if* (and $induc (neq $induc 'c)) 
      then (induc-superposition rule)
      elseif (and $ac (neq $pick-rule-str 'm) $ac)
      then (ac-critpairs rule)
      else

      (if* (> $trace_flag 1) then (terpri)
         (princ  "Computing critical pairs with: ") (terpri) (princ "  ")
         (write-rule rule))

      (if* (detachment-rule rule) (detachment-critical rule))

      (setq $aux-rset (intro-rule rule))

      (sloop with l2 = (ruleno rule)
	    for xa in $aux-rset
	    as l3 = (ruleno xa) do
	    (cond ((member0 l2 $del-rule-nums) (return nil))
		  ((member0 l3 $del-rule-nums) 
		   (setq $aux-rset (delete0 xa $aux-rset 1)))
		  ($ac ; that's the case when $pick-rule-str = m
		   (sloop for pair in (make-pairs rule xa)
			 do (ac-critpairs pair)))
		  ((and (greaterp l3 l2) (eq $crit-with-str 'o))
		   (return nil))
                 ((acceptable-pair xa rule) (superposition xa rule))))
      t))

(defun pure-critpairs (rule)
  (if* (> $trace_flag 1) then (terpri)
      (princ  "Computing critical pairs with: ") (terpri) (princ "  ")
      (write-rule rule))

  (setq $aux-rset (intro-rule rule))

  (sloop with l2 = (ruleno rule)
	for xa in $aux-rset
	as l3 = (ruleno xa) do
    (cond ((member0 l2 $del-rule-nums) (return nil))
	  ((member0 l3 $del-rule-nums) 
	   (setq $aux-rset (delete0 xa $aux-rset 1)))
	  (t (pure-superposition xa rule))))
   t)

(defun ac-critpairs (pair)
  (let ((rule1 (cadr pair)) (rule2 (caddr pair)) (flag (cadddr pair)))
    (if* (or (null $in-fopc) (is-condi-rule rule1) (is-condi-rule rule2))
	then (ac-superposition rule1 rule2 flag)
	elseif (pred-rulep rule1) 
	then (if* (pred-rulep rule2) 
		 then (pred-superposition rule1 rule2)
		 else (pred-func-superposition rule1 rule2 flag))
	elseif (pred-rulep rule2)
	then (pred-func-superposition rule2 rule1)
	else (ac-superposition rule1 rule2 flag))))

(defun superposition (rule1 rule2)
  (if* (nondo-crit rule1 rule2) then
      (if* (memq $pick-rule-str '(m a)) then (mark-superposed rule1 rule2))
      (if* (or (is-condi-rule rule1) (is-condi-rule rule2))
          then (func-superposition rule1 rule2)
          elseif (pred-rulep rule1) 
          then (if* (pred-rulep rule2) 
                   then (pred-superposition rule1 rule2)
                   else (pred-func-superposition rule1 rule2))
          elseif (pred-rulep rule2) 
          then (pred-func-superposition rule2 rule1)
          else (func-superposition rule1 rule2))))

(defun func-superposition (r1 r2)
  ; - Tries to generate critical-pairs between the rules R1 and R2.
  ; Increase efficiency by superposing only once at the root.  If the two
  ; rules are the same, then try only one with the other after changing
  ; variables in one.  As critical-pairs are processed, stop if one of
  ; these rules gets deleted.
  (setq $subs nil $subs2 nil)    
  (setq $no-rule-del t)      ;; $no-rule-del= nil iff r1 or r2 is deleted. 
  (if* (= (ruleno r1) (ruleno r2))
     then
     (if* $induc (induc-idem-superposition r1))
     (if* (is-general-rule r1) then
         (setq r2 (make-new-rule (lhs r2) (rhs r2) (ctx r2) 
                                 (rule-source r2) (ruleno r2)))
         (sloop with diff-rhs = (nequal (rhs r1) (rhs r2))
               for lhs in (commune-terms (lhs r1))
               do (sup-term r2 r1 lhs lhs
			    (and diff-rhs (nequal (lhs r1) lhs)) nil)))
     else
     (if* (or (is-general-rule r2) (ctx r1)) then
         (sloop with diff-rhs = (nequal (rhs r1) (rhs r2))
               for lhs2 in (commune-terms (lhs r2))
               do (sup-term r1 r2 lhs2 lhs2 diff-rhs nil)))
     (if* (or (is-general-rule r1) (ctx r2)) then
         (if* $no-rule-del then
             (sloop for lhs1 in (commune-terms (lhs r1)) 
                   do (sup-term r2 r1 lhs1 lhs1 nil nil))))))

(defun pure-superposition (r1 r2)
  (setq $subs nil $subs2 nil)    
  (setq $no-rule-del t)      ;; $no-rule-del= nil iff r1 or r2 is deleted. 
  (if* (= (ruleno r1) (ruleno r2)) then  
    ;; why use eq for nums****
    (setq r2 (make-new-rule (lhs r2) (rhs r2) (ctx r2) 
			    (rule-source r2) (ruleno r2)))
    (pure-sup-term r2 r1 (lhs r1) nil nil)
    else
    (if* (is-general-rule r2) 
	(pure-sup-term r1 r2 (lhs r2) (nequal (rhs r1) (rhs r2)) nil))
    (if* (and (is-general-rule r1) $no-rule-del) 
	(pure-sup-term r2 r1 (lhs r1) nil nil))))

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
  ; deleted, stop at once.  This is indicated by C_FLAG.
  (if*  (not (member0 sub $subs)) then
      (push sub $subs)
      (if* root then (sup-term2 r1 r2 lhs2 sub pos))
      (if* (not (predicatep (op-of (lhs r1)))) then
          (sloop for xa in (args-of sub) as l1 from 1 
                if (not $no-rule-del) return nil
                else if (nonvarp xa) 
                       do (sup-term r1 r2 lhs2 xa t (append1 pos l1))))))

(defun pure-sup-term (r1 r2 sub root pos)
  (if* (not (member0 sub $subs)) then
      (push sub $subs)
      (if* root then (pure-sup-term2 r1 r2 sub pos))
      (sloop for xa in (args-of sub) 
	    as l1 from 1 
	    if (not $no-rule-del) return nil
	    else if (nonvarp xa) 
		   do (pure-sup-term r1 r2 xa t (append1 pos l1)))))

(defun sup-term2 (r1 r2 lhs2 sub pos)
  ; - auxiliay function of SUPTERM.
  (let (result subst ctx)
     (add-time $unif_time (setq subst (unifier (lhs r1) sub)))
     (if* subst then
         (if* (or (ctx r1) (ctx r2)) 
             (setq ctx (handle-conditions (ctx r1) (ctx r2) subst)))
         (if* (not-falsep ctx) then
             (setq result (make-eqn
                        (applysubst subst (rplat-in-by pos lhs2 (rhs r1)))
                        (applysubst subst (rhs r2))
                        ctx 
                        (list (ruleno r1) (ruleno r2)))
                   result (flatten-eqn result)
                   $ncritpr (1+ $ncritpr))
             (if* (well-typed-eqn result) then (process-critpair result subst))))))

(defun pure-sup-term2 (r1 r2 sub pos)
  (let (result subst)
     (add-time $unif_time (setq subst (nonac-unify (lhs r1) sub)))
     (if* subst then
	 (setq result (make-eqn
                        (applysubst subst (rplat-in-by pos (lhs r2) (rhs r1)))
                        (applysubst subst (rhs r2))
                        nil
                        (list (ruleno r1) (ruleno r2)))
	       $ncritpr (1+ $ncritpr))
	 (pure-process-critpair result subst))))

(defun handle-conditions (ctx1 ctx2 sigma)
  (if* $induc
      then (setq $premises-set nil $var-premises nil $var-type-list nil)
           (nofalse-premises (merge-premises ctx1 ctx2) sigma)
      else (norm-ctx-and (flat-term (applysubst sigma ctx1))
                         (flat-term (applysubst sigma ctx2)))))

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
            for rule2 in (cdr (assoc (op-of sub) $op_rules)) 
            if (and (eq (car (rule-source rule2)) 'def)
                    (nequal ruleno (ruleno rule2)))
              do (sup-term2 rule2 rule lhs sub pos)))
  (sloop for xa in (args-of sub) as l1 from 1 do
    (if* (nonvarp xa) 
        then (induc-sup-term rule lhs xa (append1 pos l1)))))

(defun induc-idem-superposition (rule &aux l1 l2 l3)

  (if* (or (eq (setq l2 (op-of (lhs rule))) '=) (memq l2 $commutative)) then 
      (idem-super-commu rule))

  (if* (and (not (truep (rhs rule))) (eq (op-of (lhs rule)) '=)) then
     (add-time $unif_time (setq l1 (unifier (first-arg (lhs rule)) 
                                            (second-arg (lhs rule)))))
     (if* l1 then
         (setq $premises-set nil
               $var-premises nil
               $var-type-list nil
               l3 (nofalse-premises (ctx rule) l1))
         (if* (not-falsep l3) then
             (setq l2 (make-eqn '(true) 
                                (flat-term (applysubst l1 (rhs rule)))
                                l3 (append (list 'idem (ruleno rule))
                                           (rem-dups $used-rule-nums)))
                   $used-rule-nums nil
                   $ncritpr (1+ $ncritpr))
             (if* (well-typed-eqn l2) then (process-critpair l2 l1))))))

(defun instance-delete-condition (rule1 rule2)
  ; As a completmentary of unit strategy for conditionals.
  (let* ((lhs2 (lhs rule2)) (rhs2 (rhs rule2))
         (pre2 (if* (predicatep (op-of lhs2))
                       then (list lhs2 rhs2) 
                       else (list (list '= lhs2 rhs2) nil)))
         sigmas eqn)

    (sloop for pre in (cdr (ctx rule1)) 
          if (and (equal (cadr pre) (cadr pre2))
;                  (setq sigmas (unifier (car pre2) (car pre))))
                  (setq sigmas (unifiers (car pre2) (car pre))))
            do (setq eqn (remove0 pre (ctx rule1) 1)
                     eqn (if* (cdr eqn) then eqn)
;                     sigmas (ncons sigmas)
                     eqn (make-eqn (lhs rule1) (rhs rule1) eqn
                                   (list (ruleno rule1) (ruleno rule2))))
               (sloop with new for sigma in sigmas do
                 (setq new (flatten-eqn (applysubst sigma eqn))
                       $ncritpr (1+ $ncritpr))
                 (if* (> $trace_flag 1) then
                     (terpri) (princ (uconcat "Deleting conditions of [" (ruleno rule1)
                                              "] by [" (ruleno rule2) "] ..."))
                     (terpri))
                 (if* $try then (terpri) (princ "Instantiating condition ...") (terpri))
                 (if* (well-typed-eqn new) then (process-critpair new sigma))))))

(defun ac-superposition (r1 r2 flag &aux c) 
  ; - Tries to generate critical-pairs between the rules R1 and R2.
  ; Increase efficiency by superposing only once at the root.  If the two
  ; rules are the same, then try only one with the other after changing
  ; variables in one.  As critical-pairs are processed, stop if one of
  ; these rules gets deleted.
  ;
  (if* (memq $pick-rule-str '(m a)) then (mark-superposed r1 r2))
  (if* (> $trace_flag 2) (trace-ac-superposition r1 r2 flag))
  (setq $no-rule-del t)
  (if* (= flag 3) then (poly-super-distribution r1)
      else
      (setq $subs nil
	    $subs2 nil)
      (if* (= (ruleno r1) (ruleno r2)) then
	  (if* (= $idem 1) then
	      (setq r2 (make-new-rule (lhs r2) (rhs r2) (ctx r2) 
				      (rule-source r2) (ruleno r2)))
	      (if* $symmetry-check (setq $symmetry-terms (ref-symmetry-terms r1)))
	  (if* (and $new-ac (= flag 2))
	      then (new-ac-super-same r1 r2)
	      else
	      (sloop for lhs1 in (commune-terms (lhs r1)) do
		(ac-sup-term r2 r1 lhs1 lhs1 nil flag))))

	  elseif (setq c (is-character-rule r1))
	  then (if* (and (= flag 2) (same-op (lhs r1) (lhs r2))) 
		   (move-lhs-args c r2))
	  elseif (setq c (is-character-rule r2)) 
	  then (if* (and (= flag 2) (same-op (lhs r1) (lhs r2))) 
		   (move-lhs-args c r1))
	  else
	  (if* $symmetry-check
	      (setq $symmetry-terms 
		    (append (ref-symmetry-terms r1)
			    (ref-symmetry-terms r2))))

	  (if* (and $new-ac (= flag 2))
	      then (new-ac-super-at-roots r1 r2)
	      else
	      (sloop for lhs2 in (commune-terms (lhs r2)) do
		(ac-sup-term r1 r2 lhs2 lhs2 nil flag)))

	  (if* (and $no-rule-del (= flag 0)) then
	      (sloop for lhs1 in (commune-terms (lhs r1)) do
		(ac-sup-term r2 r1 lhs1 lhs1 3 0))))))

(defun new-ac-super-at-roots (r1 r2)
  ;; the lhss of r1 and r2 are rooted by the same ac operator.
  ;; New trick to avoid extensions.
  (let ((op (op-of (lhs r1))) (var (make-new-variable 'y)))
    (sloop for a1 in (rem-dups (args-of (lhs r1))) do
      (sloop for a2 in (rem-dups (args-of (lhs r2))) 
	    if $no-rule-del
	      do
	(if* (variablep a1) then
	    (if* (variablep a2) then
		(process-new-ac-cp r1 r2 
				   (remove0 a1 (lhs r1) 1) (remove0 a2 (lhs r2) 1)
				   (ncons (cons a1 a2)))
		(process-new-ac-cp r1 r2
				   (remove0 a1 (lhs r1) 1) (remove0 a2 (lhs r2) 1)
				   (ncons (list a1 op a2 var)) var)
		(process-new-ac-cp r2 r1
				   (remove0 a2 (lhs r2) 1) (remove0 a1 (lhs r1) 1)
				   (ncons (list a2 op a1 var)) var)
		;(let ((var1 (make-new-variable 'u))
		;      (var2 (make-new-variable 'v)))
		;(process-new-ac-cp r1 r2
		;                   (remove0 a1 (lhs r1) 1) (remove0 a2 (lhs r2) 1)
		;                   (list (list a2 op var1 var)
		;			       (list a1 op var2 var))
		;		   var2 var1))
		else
		(process-new-ac-cp r1 r2
				   (remove0 a1 (lhs r1) 1) (remove0 a2 (lhs r2) 1)
				   (ncons (cons a1 a2)))
		(process-new-ac-cp r1 r2
				   (remove0 a1 (lhs r1) 1) (remove0 a2 (lhs r2) 1)
				   (ncons (list a1 op a2 var)) var))
	    else
	    (if* (variablep a2) then
		(process-new-ac-cp r2 r1
				   (remove0 a2 (lhs r2) 1) (remove0 a1 (lhs r1) 1)
				   (ncons (cons a2 a1)))
		(process-new-ac-cp r2 r1
				   (remove0 a2 (lhs r2) 1) (remove0 a1 (lhs r1) 1)
				   (ncons (list a2 op a1 var)) var)
		else
		(sloop for sigma in (unify a1 a2 0 t) do
		  (process-new-ac-cp r1 r2
				   (remove0 a1 (lhs r1) 1) (remove0 a2 (lhs r2) 1)
				   (cdr sigma)))))))

    (when $no-rule-del
      (sloop for lhs2 in (commune-terms (lhs r2)) do
	(ac-sup-term r1 r2 lhs2 lhs2 3 0)))
    ))
  

(defun new-ac-super-same (r1 r2)
  ;; the lhss of r1 and r2 are rooted by the same ac operator.
  ;; New trick to avoid extensions.
  (let ((op (op-of (lhs r1))) (var (make-new-variable 'y)))
    (sloop for a1 in (rem-dups (args-of (lhs r1))) do
      (sloop for a2 in (rem-dups (args-of (lhs r2))) 
	    if $no-rule-del
	      do
	(if* (variablep a1) then
	    (if* (variablep a2) then
		(process-new-ac-cp r1 r2
				   (remove0 a1 (lhs r1) 1) (remove0 a2 (lhs r2) 1)
				   (ncons (list a1 op a2 var)) var)
		else
		(process-new-ac-cp r1 r2
				   (remove0 a1 (lhs r1) 1) (remove0 a2 (lhs r2) 1)
				   (ncons (cons a1 a2)))
		(process-new-ac-cp r1 r2
				   (remove0 a1 (lhs r1) 1) (remove0 a2 (lhs r2) 1)
				   (ncons (list a1 op a2 var)) var))
	    elseif (not (variablep a2)) then
	    (sloop for sigma in (unify a1 a2 0 t) 
		  if (sloop for xa in (cdr sigma) thereis (not (variablep (cdr xa))))
		    do (process-new-ac-cp r1 r2
					  (remove0 a1 (lhs r1) 1) (remove0 a2 (lhs r2) 1)
					  (cdr sigma))))))

    (when $no-rule-del
      (sloop for lhs2 in (commune-terms (lhs r2)) do
	(ac-sup-term r1 r2 lhs2 lhs2 3 0)))))
  
(defun process-new-ac-cp (r1 r2 lhs1 lhs2 sigma &optional t2 t1)
  (let ((source (list (ruleno r1) (ruleno r2))) common l1 l2)
    (setq $ncritpr (1+ $ncritpr)
	  lhs1 (make-flat (applysubst sigma lhs1))
	  lhs2 (make-flat (applysubst sigma lhs2)))

    (setq common (common-elements (cdr lhs1) (cdr lhs2)))
    (setq lhs1 (set-diff lhs1 common)
	  lhs2 (set-diff lhs2 common))
  
    (setq l1 (applysubst sigma (if* t1 (list (rhs r1) t1) (ncons (rhs r1))))
	  l2 (applysubst sigma (if* t2 (list (rhs r2) t2) (ncons (rhs r2)))))

    (setq t1 (flat-term (append lhs2 l1))
	  t2 (flat-term (append lhs1 l2)))
    (if* (null (cddr t1)) (setq t1 (cadr t1)))
    (if* (null (cddr t2)) (setq t2 (cadr t2)))
    (setq r1 (make-eqn t1 t2 nil source))
    (if* (well-typed-eqn r1) (process-critpair r1 sigma))

    (sloop for sig2 in (set-unify (cdr lhs1) (cdr lhs2)) do
      (process-new-ac-cp2 lhs1 lhs2 l1 l2 sig2 source))
    ))

(defun process-new-ac-cp2 (lhs1 lhs2 l1 l2 sigma source &aux common)
  (setq $ncritpr (1+ $ncritpr)
	lhs1 (make-flat (applysubst sigma lhs1))
	lhs2 (make-flat (applysubst sigma lhs2)))

  (setq common (common-elements (cdr lhs1) (cdr lhs2)))
  (setq lhs1 (set-diff lhs1 common)
	lhs2 (set-diff lhs2 common))
  
  (setq l1 (applysubst sigma l1)
	l2 (applysubst sigma l2))
  (setq l1 (flat-term (append lhs2 l1))
	l2 (flat-term (append lhs1 l2)))
  (if* (null (cddr l1)) (setq l1 (cadr l1)))
  (if* (null (cddr l2)) (setq l2 (cadr l2)))
  (setq l1 (make-eqn l1 l2 nil source))
  (if* (well-typed-eqn l1) (process-critpair l1 sigma)))

(defun set-unify (l1 l2)
  ;; this is not a complete set-unification procedure.
  (setq l1 (rem-dups l1) l2 (rem-dups l2))
  (sloop for xa in l1 nconc (sloop for xb in l2 append (unify-with-ac xa xb))))

(defun trace-ac-superposition (r1 r2 flag)
  (terpri) (princ "Computing critical pairs between ")
  (caseq flag
    (0 (princ (uconcat "Rules [" (ruleno r1) "] and [" (ruleno r2) "].")))
    (1 (princ (uconcat "Extension of [" (ruleno r1) "] and Rule [" (ruleno r2) "].")))
    (2 (princ (uconcat "Extensions of [" (ruleno r1) "] and [" (ruleno r2) "].")))
    (3 (princ (uconcat "Rule [" (ruleno r1) "] and (X+Y)*Z ---> (X*Z)+(Y*Z)."))))
  (terpri))

(defmacro ac-critical-source ()
  `(caseq flag
     (0 (list (ruleno r1) (ruleno r2)))
     (1 (list (ruleno r1) (ruleno r2) 'ext1))
     (2 (list (ruleno r1) (ruleno r2) 'ext2))))

(defmacro process-ac-critical-pair (uni)
  ; cut from ac-sup-term in critical.lisp.
  (let ((tmp1 (gensym)) (tmp2 (gensym)) (lhs (gensym)) (rhs (gensym))
        (ctx (gensym)) (eqn (gensym)))
    `(let (,tmp1 ,tmp2 ,lhs ,rhs ,ctx ,eqn)
       (caseq flag
         (1 (setq ,tmp1 (or (cdr (assq 'xex1 ,uni)) 'xex1)))
         (2 (setq ,tmp1 (or (cdr (assq 'xex1 ,uni)) 'xex1)
                  ,tmp2 (or (cdr (assq 'xex2 ,uni)) 'xex2))))
       
       (setq $ncritpr (1+ $ncritpr)
             ,lhs (apply-to
                   (rplat-in-by pos lhs2
                                (add-rest-args 
                                  (rhs r1)
                                  (if* ,tmp1 
                                      (make-term (op-of sub)
                                                 (ncons ,tmp1)))))
                   ,uni)
             ,rhs (apply-to
                   (add-rest-args (rhs r2)
                                  (if* ,tmp2
                                      (make-term (op-of sub) 
                                                 (ncons ,tmp2))))
                   ,uni)
             ,ctx (if* (or (ctx r1) (ctx r2)) then
                     (handle-conditions (ctx r1) (ctx r2) ,uni))
             ,eqn (make-eqn ,lhs ,rhs ,ctx source))

       (if* (well-typed-eqn ,eqn) then
           (process-critpair (flatten-eqn ,eqn) uni)))))

(defun ac-sup-term (r1 r2 lhs2 sub pos flag &aux source unifs)
  ; sub is a subterm of lhs2, namely, the lhs of r2. 
  ; r1 will visit all subterms of lhs2. 
  ; r2 maybe an extended rule.
  ; If r1 is also an extended rule, in this case, r2 must be extednded, too,
  ; r1 does not need to visit all subterms of lhs2.
  (if* (member0 sub $subs)
      then nil
      else

      (if* $symmetry-terms 
          (sloop for xl in $symmetry-terms 
                if (member0 sub xl) return (setq $subs (append $subs xl))
                finally (push sub $subs))
          (push sub $subs))
      (cond ((equal pos 3) (setq pos nil))
            ((same-op (lhs r1) sub)
             (if* (and $polynomial (eq (op-of sub) '*) (not (memq '* $ac))) then
                 (if* (= flag 0)
                     (poly-super-at-*-0 r1 r2 lhs2 sub pos (ac-critical-source))
                     (poly-super-at-*-1 r1 r2 lhs2 sub pos (ac-critical-source)))
                 elseif (setq unifs (unify (lhs r1) sub flag))
                 then
                 (setq unifs (sort unifs 'lessp-size-bindings)
                       source (ac-critical-source))
                 (sloop for unifi in unifs 
                       as uni = (cdr unifi) do
                   (if* (process-ac-critical-pair uni) (return nil))))))

      (if* (and (not (predicatep (op-of (lhs r1)))) (nequal 2 flag)) then
          (sloop for xa in (args-of sub) as l1 from 1 
                if (not $no-rule-del) return nil 
                else if (nonvarp xa) 
                       do (ac-sup-term r1 r2 lhs2 xa (append1 pos l1) flag)))))


(defun process-critpair (eqn &optional sigma)
  ; The new criitcal pair EQN is processed immediately.
  ; If the delelting-rule-stradegy is set to 1, then process
  ; all new equations produced.
  (if* (= $trace_flag 3) then (trace-crit (eqn-source eqn) eqn nil sigma))
  (if* $induc then (setq eqn (pre-crit-checkeq eqn)))
  (if* eqn then
      (setq sigma (*catch 'kb-top (process-equation eqn)))
      (caseq sigma
        ((*undo* *kb-top*) (*throw 'kb-top sigma))
        ((*newop* *sepa*) 
         (sloop while $eqn-set do (process-equation (pop $eqn-set))))
        (t (if* (= $del_rule_str 2) 
               (sloop while $eqn-set do (process-equation (pop $eqn-set))))
           (if* (or (memq (first (eqn-source eqn)) $del-rule-nums)
                   (memq (second (eqn-source eqn)) $del-rule-nums)) 
               then (setq $no-rule-del nil) t)))))

(defun pure-process-critpair (eqn &optional sigma)
  (if* (= $trace_flag 3) then (trace-crit (eqn-source eqn) eqn nil sigma))
  (if* eqn then
      (setq sigma (*catch 'kb-top (pure-process-equation eqn)))
      (caseq sigma
        ((*undo* *kb-top*) (*throw 'kb-top sigma))
        ((*newop* *sepa*) 
         (sloop while $eqn-set do (pure-process-equation (pop $eqn-set))))
        (t (if* (= $del_rule_str 2) 
               (sloop while $eqn-set do (pure-process-equation (pop $eqn-set))))
           (if* (or (memq (first (eqn-source eqn)) $del-rule-nums)
                   (memq (second (eqn-source eqn)) $del-rule-nums))
               then (setq $no-rule-del nil) t)))))

(defun process-ac-unifier (uni info)
  (setq uni (sloop for xa in uni collect (cons (car xa) (make-flat (cdr xa)))))
  (if* (or (neq $blocking-on 'y) (is-blocked uni)) then
      (let* ((r1 (pop info))
             (r2 (pop info))
             (lhs2 (pop info))
             (sub (pop info))
             (pos (pop info))
             (flag (pop info))
             (source (pop info)))
        (process-ac-critical-pair uni))
      else nil))

(defun remove-pairs-with (rule)
  (setq $pair-set (sloop for pair in $pair-set 
                        if (not (member0 rule pair)) collect pair)))

(defun add-pairs (rule1 rule2 &aux l1)
  (sloop for pair in (make-pairs rule1 rule2) do 
	(if* (setq l1 (assoc (car pair) $pair-set))
	    (if* (cadr l1) 
		(nconc (cadr l1) (ncons pair))
	      (push pair (cadr l1)))
	  (setq $pair-set (insert (list (car pair) (ncons pair)) 
				  $pair-set 'car-lessp t)))))

(defun pick-ac-pair ()
  (sloop with l1 while t do
    (if* (setq l1 (car $pair-set)) then
        (if* (cadr l1) then
            (sloop with xa while t do
              (setq xa (pop (cadr l1)))
              (if* xa 
                  (if* (not (or (memq (ruleno (cadr xa)) $del-rule-nums)
                               (memq (ruleno (caddr xa)) $del-rule-nums)))
                      (return (setq l1 xa)))
                  (return (setq l1 nil))))
            (if* l1 (return l1))
            else
            (pop $pair-set))
        else (return nil))))

(defun acceptable-pair (rule1 rule2)
  (and (or (null $support) 
           (not (is-source-type rule1 'user))
           (memq (cadr (rule-source rule1)) $support)
           (not (is-source-type rule2 'user))
	   (memq (cadr (rule-source rule2)) $support))
       (caseq $idem
         ((1 2) t)
         (3 (or (null (ctx rule1)) (null (ctx rule2))))
         (4 (or (is-source-type rule2 'user)
		(is-source-type rule2 'user)))
         (t nil))))

(defmacro poly-make-pairs ()
  `(let ()
     (setq rhs-root1 (is-rooted-+ (rhs rule1))
           rhs-root2 (is-rooted-+ (rhs rule2)))
     (if* (and (or rhs-root1 (is-rooted-+ lhs1))
	      (or rhs-root2 (is-rooted-+ lhs2)))
         (push-end (list (times 2 psize) rule1 rule2 0) pairs)
         (push-end (list psize rule1 rule2 0) pairs))

     (if* (= (ruleno rule1) (ruleno rule2)) then
       (if* (not (is-character-rule rule2))
	   (push (list psize rule1 rule2 3) pairs))
       (if* (ac-root lhs1) (push (list (times 10 psize) rule1 rule2 2) pairs))
       elseif (same-root lhs1 lhs2)
       then (if* (or (is-character-rule rule1) (is-character-rule rule2))
                then (push-end (list (+ -1000 psize) rule1 rule2 2) pairs)
                elseif (and (is-homogeneous-term lhs1)
                            (is-homogeneous-term lhs2))
                then (if* (< (length (cdr lhs1))
                            (length (cdr lhs2)))
                         then (push-end (list (- psize 10000) rule1 rule2 1) 
					pairs)
                         elseif (> (length (cdr lhs1))
                                   (length (cdr lhs2)))
                         then (push-end (list (- psize 10000) rule2 rule1 1) 
					pairs))
		elseif (ac-root lhs1)
		then (push-end (list (times 10 psize) rule1 rule2 2) pairs))
       elseif (is-rooted-+ lhs1) 
       then (if* (and (eq (op-of lhs2) '*) (not rhs-root2))
		(push-end (list (+ $ex1 psize) rule2 rule1 1) pairs)
	      (push-end (list (times 5 psize) rule1 rule2 1) pairs))
       elseif (is-rooted-+ lhs2) 
       then (if* (and (eq (op-of lhs1) '*) (not rhs-root1))
		(push-end (list (+ $ex1 psize) rule1 rule2 1) pairs)
	        (push-end (list (times 5 psize) rule2 rule1 1) pairs))
       )))

(defun make-pairs (rule1 rule2)
  (if* (acceptable-pair rule1 rule2) then
    (let* ((lhs1 (lhs rule1))
	   (lhs2 (lhs rule2))
	   (psize (+ (lhsize rule1) (lhsize rule2))) 
	   pairs rhs-root1 rhs-root2)
      (if* $polynomial
	  then (poly-make-pairs)
	  elseif $ac then
	  (let ((ex1 (ac-root lhs1)) (ex2 (ac-root lhs2)))
	    (if* $new-ac then
	      (setq pairs 
		    (cond 
		     ((and ex1 ex2 (same-root lhs1 lhs2))
		      (ncons (list psize rule1 rule2 2)))
		     (ex1 (list (list psize rule1 rule2 0)
				(list (+ $ex1 psize) rule1 rule2 1)))
		     (ex2 (list (list psize rule1 rule2 0)
				(list (+ $ex1 psize) rule2 rule1 1)))
		     (t (ncons (list psize rule1 rule2 0)))))
	      else
	      (setq pairs (ncons (list psize rule1 rule2 0)))
	      (if* (> $idem 1) then
		(if* (and ex1 ex2 (same-root lhs1 lhs2))
		    (push-end (list (+ $ex2 psize) rule1 rule2 2) pairs))
		else
		(if* ex1 (push-end (list (+ $ex1 psize) rule1 rule2 1) pairs))
		(if* ex2 then
		  (if* (nequal (ruleno rule1) (ruleno rule2))
		      (push-end (list (+ $ex1 psize) rule2 rule1 1) pairs))
		  (if* (and ex1 (same-root lhs1 lhs2))
		      (push-end (list (+ $ex2 psize) rule1 rule2 2) pairs))))))
	  else (setq pairs (ncons (list psize rule1 rule2 0))))
      pairs)))

(defun unit-rule (lhs rhs)
  (if* (or (variablep rhs) (null (cdr rhs)))
      (and (null (cdr (setq lhs (remove0 rhs (args-of lhs) 1))))
           (nequal (setq lhs (car lhs)) rhs)
           (or (variablep lhs) (null (cdr lhs))))))

(defun trace-crit (rns crit &optional is-ass sigma)
  (terpri)
  (caseq (first rns)
    (idem (princ "    By idempotency, the rule ["))
    (distr (princ "    Superposing the distribution law into the rule ["))
    (t (princ (uconcat "    Superposing Rule [" (first rns) "] into Rule ["))))
  (princ (uconcat (second rns) "] yields a critical pair: "))

  (terpri) (princ "        ")
  (if* is-ass 
      (write-assertion `(,rns . ,crit))
      (write-eqn crit))
  (if* sigma then 
      (princ "    with the unifier [") (write-sigma sigma) (princ "].") (terpri)))

;; the following functions are for debugging.
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
           "  rule: " (if* n1 n1 (ruleno (cadr pa)))
           " and rule: " (if* n2 n2 (ruleno (caddr pa)))))

(defun look-at-pair-and (nums)
  (sloop with flag with i = 0
        with n1 = (car nums)
        with n2 = (cadr nums) 
        for pas in $pair-set do
    (sloop for pa in (cadr pas)
          as r1 = (cadr pa)
          as r2 = (caddr pa) do
      (setq i (1+ i))
      (if* (and (= n1 (ruleno r1)) (= n2 (ruleno r2))) then
          (setq flag t) (terpri) (princ i) (princ ": ") (princ pa)))
            finally (return flag)))

(defun list-pairs ()
  (sloop with i = 0
        for pas in $pair-set do
    (sloop for pa in (cadr pas)
          as r1 = (cadr pa)
          as r2 = (caddr pa) do
      (setq i (1+ i))
      (terpri) 
      (princ (uconcat i ": weight = " (car pas) " r1 = "  (ruleno r1) 
                        ", r2 = " (ruleno r2) ", flag = " (cadddr pa))))))
