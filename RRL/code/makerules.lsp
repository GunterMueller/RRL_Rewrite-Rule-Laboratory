;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

;;; fixed 5 in quotient -- siva

(defun is-valid-condi-rule (eqn oneway good-only)
  ;  Tries to make a rule from terms T1 and T2.
  ;         Returns:  1 - if varset(T1) properly contains varset(T2) 
  ;	      	      2 - if varset(T2) properly contains varset(T1) 
  ;	      	      3 - if varset(T1) = varset(T2)
  ;	    	    nil - if neither varset contains the other.
  ;
  ; In the last case, when no rule can be made out of T1 and T2, call the
  ; function INVALID-RULE which will introduce a new operator and try to
  ; form two rules.
  ;
  (let ((vart1 (var-list (lhs eqn))) 
	(vart2 (var-list (rhs eqn))) 
	(cvars (all-pre-vars (cdr (ctx eqn))))
	l4 l5)
    (setq l4 (length vart1)
	  l5 (length vart2))
    (cond ((and (= l4 l5) (is-subset vart2 vart1)) 
	   (if (or (not good-only) (is-subset cvars vart1)) 3))
	  ((and (not oneway) (lessp l4 l5) (is-subset vart1 vart2)) 
	   (if (or (not good-only) (is-subset cvars vart2)) 2))
	  ((is-subset vart2 vart1) 
	   (if (or (not good-only) (is-subset cvars vart1)) 1))
	  (good-only nil)
          (t (invalid-rule eqn vart1 vart2 oneway)))))

(defun is-valid-rule (eqn oneway good-only)
  ; Tries to make a rule from terms T1 and T2.
  ; Returns:  1 - if varset(T1) properly contains varset(T2) 
  ;	      2 - if varset(T2) properly contains varset(T1) 
  ;	      3 - if varset(T1) = varset(T2)
  ;	    nil - if neither varset contains the other.
  ; In the last case, when no rule can be made out of T1 and T2, call the
  ; function INVALID-RULE which will introduce a new operator and try to
  ; form two rules.
  (let ((t1 (lhs eqn)) (t2 (rhs eqn)) l1 l2)
    (cond ((is-inconsi-pair t1 t2)
	   (if* $in-fopc
	       then (if* (equal (ctx eqn) t2) 
			then (inconsistent-eqn eqn)
			else (add-rule (make-new-rule
					(make-term 'eq (commu-exchange (list t1 t2)))
					'(true) (ctx eqn) (eqn-source eqn)))
			)
	       else (inconsistent-eqn eqn))
	   nil)
	  ((is-commut-pair t1 t2)
	   (make-ass-com-op (op-of t1) eqn (memq (op-of t1) $associative)) 
	   (reset-kb '*kb-top*))
          ((is-assoc-under-c t1 t2) (make-ass-com-op (op-of t1) eqn t) nil)
	  ;((and $cycle-rule (is-cycle-eqn eqn)) (make-cycle-rule eqn) nil)
	  (t (if* (is-assoc-pair t1 t2) then (push (op-of t1) $associative))
	    (setq t1 (var-list t1) 
		  t2 (var-list t2)
		  l1 (length t1)
	          l2 (length t2))
            (cond ((and (= l1 l2) (is-subset t1 t2)) (if* oneway 1 3))
		  ((and (not oneway) (lessp l1 l2) (is-subset t1 t2)) 2)
		  ((is-subset t2 t1) 1)
		  (good-only nil)
	  	  (t (invalid-rule eqn t1 t2 oneway)))))))

(defun invalid-rule (eqn varl varr oneway)
  ; Called when an equation to be oriented is not valid either way
  ; or when the user explicitly wants to introduce a new operator.
  ; If introduces the operator as a function of the intersection
  ; of the varsets.
  (terpri) (princ "This eqn cannot be oriented into a rule") 
  (if oneway 
      (princ (uconcat " because its RHS contains " 
		      (car (set-diff varr varl)))))
  (princ ":") (terpri) 
  (princ "  ") (write-eqn eqn) (terpri)
  (if* $akb_flag 
      then (if* (< (length $history) $max-history) 
	       then (setq $max-history (sub1 $max-history))
	       (princ "Undo to last interaction.") (terpri) (undo)
               elseif (= $post-posi 1) 
               then (postpone-it eqn) nil
	       else (princ "Introduce new operator.") (terpri) 
	       (add-operator eqn varl varr nil))
      else
      (user-selectq 
	(abort "    Quit to the top level" (*throw 'reset '*reset*))
	(drop "     Discard the equation" nil)
	(leftright "As it is. The rule will not be used for reduction." 
		(setq eqn (make-new-rule
			   (lhs eqn) (rhs eqn) (ctx eqn) (eqn-source eqn)))
		(add-crit-rule eqn))
	(makeeq "   Introduce the equality predicate"
		(make-eq (lhs eqn) (rhs eqn) eqn))
	(operator " Introduce new operator" 
		  (add-operator eqn varl varr nil))
	(postpone " Postpone the equation" 
		  (setq $post-set (nconc $post-set (ncons eqn))))
	(rightleft "From right to left. The rule will not be used for reduction" 
		(setq eqn (make-new-rule
			   (rhs eqn) (lhs eqn) (ctx eqn) (eqn-source eqn)))
		(add-crit-rule eqn))
	(undo "     Undo it to the last interacion" (undo))
	)
      nil))

(defun ctx-dominant-rule (rule &aux pres pre)
  ; a rule is said to be dominant by its conditon if the variables of lhs
  ; don't include all that of rhs and one of the premises conatains
  ; all variables of the body.
  (if* (and $induc (setq pres (cdr (ctx rule)))
	   (sloop with vars = (union (var-list (lhs rule)) (all-vars (rhs rule)))
		 for xa in pres
		 if (is-subset vars (all-vars (car xa)))
		   return (setq pre xa)
		 finally (return nil)))
      then 
      (if* (nequal pre (car pres)) then
	  (setq rule (change-ctx rule (cons '*&* (cons pre (remove0 pre pres))))))
      (cons (op-of (car pre)) rule)))

(defun make-new-rule (lhs rhs ctx source &optional nrule size 
			  &aux cvars extra-cvars lvars)

  (setq lvars (var-list lhs))
  (when (and ctx $induc)
	(setq cvars (all-pre-vars (cdr ctx)))
	(when (not (is-subset cvars lvars))
	      (setq extra-cvars (set-diff cvars lvars))
	      (if (or (eq $condi-dominate 2)
		      (is-subset lvars cvars))
		  (push nil extra-cvars)
		(push t extra-cvars))))

  (setq lhs (newvarsin lhs (if* extra-cvars
			       (append (cdr extra-cvars) lvars)
			     lvars))
	rhs (repvarsin rhs))

  (when ctx
	(setq ctx (repvarsin ctx)
	      cvars (repvarsin cvars)
	      extra-cvars (repvarsin extra-cvars)))

  (setq size (if* size then (+ size (size lhs) (size rhs))
		 elseif $polynomial 
		 then (+ (poly-size lhs) (quotient (poly-size rhs) 50))
		 elseif (and $induc ctx) 
		 then (body-premises-size lhs (cdr ctx) source extra-cvars)
		 else (special-size lhs rhs source extra-cvars))
	size (if* (memq 'def source) (quotient size 2) size)
	nrule (if* nrule then nrule else (setq $nrules (1+ $nrules))))

  (make-rule lhs rhs ctx nrule source size extra-cvars (or cvars (if* lvars t)))
  )

(defun special-size (lhs rhs source red)
  (caseq $rule-size
    (s (+ (* 2 (w-size lhs)) (w-size rhs)))
    (d (+ (times 10 (depth lhs)) (quotient (+ (w-size lhs) (w-size rhs)) 5)))
    (l (+ (times (if* red 20 5) (literal-num lhs)) (w-size lhs) (w-size rhs)))
    (u (unknown-size lhs (size rhs) source (if* red 20 5)))))

(defun body-premises-size (lhs pres source &optional weight)
  (setq pres (sloop for pre in pres collect (car pre))
	weight (if* weight then 20 else 5))
  (caseq $rule-size
    (s (+ (size lhs) (apply '+ (mapcar 'size pres))))
    (d (+ (times weight (depth lhs))
	  (quotient  (apply '+ (mapcar 'size pres)) 5)))
    (l (+ (times weight (1+ (length pres)))
	  (quotient  (apply '+ (mapcar 'size pres)) 5)))
    (u (unknown-size lhs 0 source weight))))    

(defun unknown-size (term pres-size source weight &aux level)
  ; This function is named because of its experimental status.
  (setq level (if* (and (numberp (first source)) (numberp (second source)))
		  then (1+ (min (get-rule-level (first source)) 
				  (get-rule-level (second source))))
		  else (caseq (first source)
			 (idem (get-rule-level (second source)))
			 (deleted (max 0 (sub1 (get-rule-level (second source)))))
			 (t 0))))
  (+ $ncritpr (times 100 level) (times weight (size term)) pres-size))

(defun get-rule-level (ruleno)
  ; we define simply that the level of a rule is the size of the rule divided by 50.
  (sloop for rule in $rule-set 
	as rulno = (ruleno rule)
	if (= ruleno rulno) return (quotient (lhsize rule) 100)
	finally (return 0)))

(defun add-operator (eqn varl varr varc)
  ; Called when new operators are needed to orient an equation into a rule.
  (let (l1 l2)
    (start-push-history eqn)
    (cond ((is-subset varc varl)
	   (setq l1 (new-term varl varr $akb_flag)
                 varl (change-lhs eqn (rhs eqn)))
	   (push (change-rhs eqn l1) $eqn-set)
	   (push (change-rhs varl l1) $eqn-set))
	  ((is-subset varr varl) 
	   (setq l1 (new-term varl varc $akb_flag))
	   (push (change-ctx eqn l1) $eqn-set)
	   (push (make-eqn (ctx eqn) l1 nil (eqn-source eqn)) $eqn-set))
	  (t (setq l2 (new-term varl varr $akb_flag)
		   l1 (new-term varl varc $akb_flag)
		   varc (eqn-source eqn))
	   (push (make-eqn (lhs eqn) l2 l1 varc) $eqn-set)
	   (push (make-eqn (rhs eqn) l2 l1 varc) $eqn-set)
	   (push (make-eqn (ctx eqn) l1 nil varc) $eqn-set)))
   (*throw 'kb-top '*newop*)))

(defun new-term (varl varr auto)
  ; Return a new term whose root symbol is new one and
  ; its arguments are the intersection of VARL and VARR.
  (let ((l1 (intersection varl varr)))
     (make-term (if* auto then (auto-operator (length l1))
			 else (ask-for-operator (length l1))) l1)))

(defun ask-for-operator (arity)
  ; Asks user for a new operator and gives arity ARITY.
  ; Returns operator after adding it to $operlist.
  (prog (ans)
    loop-op
    (if* (is-empty-line $in-port) then (princ "Give me a new operator name: "))
    (setq ans (read-atom 'end))
    (terpri)
    (if* (member ans $operlist)
        then (princ "A new name please!") (terpri)
             (go loop-op))
    (if* (or (not (is-valid-op ans)) 
	    (and (numberp ans) (nequal arity 0)))
        then (princ "Sorry, not a valid operator.") (terpri)
             (go loop-op))
    (set-arity ans arity)
    (if* (and (is-infix-op ans) (= arity 2)) then (set-infix ans))
    (push ans $operlist)
    (return ans)))

(defun auto-operator (arity)
  ; Asks user for a new operator and gives arity ARITY.
  ; Returns operator after adding it to $operlist.
  (let (ans)
    (initsym 'f)
    (setq ans (newsym 'f))
    (sloop while (member ans $operlist) do (setq ans (newsym 'f)))
    (set-arity ans arity)
    (push ans $operlist)
    ans))

; From propsko
(defun make-rule-from-ass (ass source &aux l2)
  ; Sort maximal items onto the left side of the rule.  If this
  ; cannot be done, add whatever equations are necessary to 
  ; the equation set and return nil.
  (if* (setq l2 (assertion2equation (make-eqn ass nil nil source)))
      (return-from make-rule-from-ass (orient-an-eqn l2)))
		   
  (setq ass
	(if* (eq (op-of ass) 'xor) 
	    then (if* (member '(true) ass)
		     then (delete0 '(true) (cdr ass))
		     else `((true) . ,(args-of ass)))
	    else `((true) ,ass)))

  ; When finding length of maximal element $anspred should not be 
  ; included.

  (if* (eq $ordering 's) 
      then (make-rule-size-order ass source)
      else
      (sloop for xa in ass do
	(pop ass)
	(if* (sloop for ya in ass thereis (compare-item ya xa))
	    then (push xa l2)
	    else (setq ass (append1 ass xa))))
      (make-new-rule (simp-xor-simp ass) (simp-xor-simp l2) nil source)))

(defun make-rule-size-order (ass source &aux ass-wo-$ans maxsize l2)
  (setq ass-wo-$ans (set-diff ass (ans-member ass))
	maxsize (if* (null ass-wo-$ans) then 0 else
		    (apply 'max (mapcar 'literal-num ass-wo-$ans))))
  (sloop for xa in ass do
    (pop ass)
    (if* (or (< (literal-num xa) maxsize)
	    ; Put $anspred on right-hand side, unless there
	    ; no argument larger than it. This means $anspred
	    ; will be put on the right-hand side if the
	    ; arg list contains anything but true.
	    (and $narrow (eq (car xa) $anspred)
		 (sloop for ya in ass thereis (compare-item ya xa)))
	    (sloop for ya in ass
		  thereis (and (= (literal-num ya) maxsize)
			       (size-compare ya xa))))
	then (push xa l2)
	else (setq ass (append1 ass xa))))
  (setq l2 (check-mismatch l2 (var-list (cons 'xor ass)) source))
  (make-new-rule (simp-xor-simp ass) (simp-xor-simp l2) nil source))

(defun check-mismatch (terms vars source &aux terms2 var2)
   (sloop for xa in terms do
      (pop terms)
      (if* (or (eq (car xa) $anspred) (is-subset (var-list xa) vars))
	then (setq terms (append1 terms xa))
	else (push xa terms2) (setq var2 (union var2 (var-list xa))))
      finally (if* terms2 then
		  (setq var2 (new-term vars var2 t)
			terms (append1 terms var2))
		  (if* (> $trace_flag 1) then
		      (terpri) (princ "Following term will be a part of the rhs of a rule,")
		      (terpri) (princ "    ") 
		      (write-term (if* (cdr terms2) 
				      then (make-term 'xor terms2)
				      else (car terms2)))
		      (terpri) (princ "    but it contains variables not in the lhs. ")
		      (terpri) (princ "    We replace it by ")
		      (write-term var2) (princ ".") (terpri))
		  (make-rule-size-order (cons var2 terms2) source)))
   terms)

(defun occurs-in-rule (var rule)
  ;; return t iff var occurs in rule.
  (or (occurs-in var (lhs rule))
      (occurs-in var (rhs rule))
      (if (ctx rule)
	  (sloop for pre in (cdr (ctx rule))
		 thereis (occurs-in var (car pre)))
	)))

(defun is-condi-dominate-rule (rule &aux (nth9 (nth 9 rule)))
  (and (consp nth9) (null (car nth9))))
