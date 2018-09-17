(in-package "USER")

(defmacro lrpo (t1 t2) 
  `(if (or $condi (null $ac))
       (lrpo> ,t1 ,t2)
       (aclrpo ,t1 ,t2)))

; This file contains the functions for lexicographic recursive path ordering.

(defun lrpo> (t1 t2)
  ; Compares two terms, T1 and T2, using LRPO with equivalent
  ; operators.  Returns T if T1 > T2 using LRPO.
  ; First check if either T1 or T2 is a variable.  If not, then compare
  ; root operators and handle the three cases of equivalent, greater,
  ; and neither equivalent nor greater in the precedence relation on
  ; function symbols.
  (cond	((variablep t1) nil)
        ((variablep t2) (occurs-in t2 t1))
	((grt-prec (op-of t1) (op-of t2))
	 (sloop for xb in (args-of t2) always (lrpo> t1 xb)))
        ((eqops (op-of t1) (op-of t2))
	 (cond ((null (args-of t2)) (args-of t1))
	       ((op-has-status (op-of t1))
		(cond ((> (get-arity (op-of t1)) (get-arity (op-of t2)))
		       (sloop for xb in (args-of t2) always (lrpo> t1 xb)))
		      ((= (get-arity (op-of t1)) (get-arity (op-of t2)))
		       (rpostatus> t1 t2))
		      (t (sloop for xa in (args-of t1) thereis (lrpo>= xa t2))))
		)
	       (t (rpomult> t1 t2))))
	(t (sloop for xa in (args-of t1) thereis (lrpo>= xa t2)))))

(defun lrpo>= (t1 t2)
  ;; return t iff t1 >rpo t2 or t1 =rpo t2.
  ;; Assuming variables >=rpo constants.
  (cond ((variablep t1) (or (equal t1 t2) (is-constant-term t2)))
	((variablep t2) (occurs-in t2 t1))
	((eqops (op-of t1) (op-of t2)) 
	 (cond ((null (args-of t2)) t)
	       ((op-has-status (op-of t1))
		(cond ((> (get-arity (op-of t1)) (get-arity (op-of t2)))
		       (sloop for xb in (args-of t2) always (lrpo> t1 xb)))
		      ((= (get-arity (op-of t1)) (get-arity (op-of t2)))
		       (rpostatus>= t1 t2))
		      (t (sloop for xa in (args-of t1) thereis (lrpo>= xa t2))))
		)
	       (t (rpomult>= t1 t2))))
	((grt-prec (op-of t1) (op-of t2))
	 (sloop for xb in (args-of t2) always (lrpo> t1 xb)))
	(t (sloop for xa in (args-of t1) thereis (lrpo>= xa t2)))))

(defun rpomult> (l1 l2)
  ;  Called when the top-level operators, T1 and T2, are equivalent
  ;	    and have multiset status.  Returns T if T1 > T2.
  (setq l2 (mult-diff-set (args-of l1) (args-of l2))
	l1 (car l2)
	l2 (cdr l2))
  (cond ((null l2) l1)
	((null l1) nil)
	(t (sloop for xa in l2 always
		  (sloop for xb in l1 thereis (lrpo> xb xa))))))

(defun rpomult>= (l1 l2)
  ;; Called when the top-level operators, T1 and T2, are equivalent
  ;; and have multiset status.  Returns T if T1 > T2.
  (setq l2 (mult-diff-set (args-of l1) (args-of l2))
	l1 (car l2)
	l2 (cdr l2))
  (cond ((null l2) t)
	((null l1) nil)
	(t (sloop for xa in l2 always
		  (sloop for xb in l1 thereis (lrpo>= xb xa))))))

(defmacro rpostatus> (t1 t2)
  ; Called when T1 and T2 have equivalent operators at the top
  ; level and those operators have status.  Compares the list of
  ; arguments from left-to-right or right-to-left and decides if T1 > T2.
  `(if (op-has-rl-status (op-of ,t1))
       (lexico-comp-rl ,t1 ,t2)
       (lexico-comp-lr ,t1 ,t2)))

(defmacro rpostatus>= (t1 t2)
  `(if (op-has-rl-status (op-of ,t1))
       (lexico-comp-rl ,t1 ,t2 t)
       (lexico-comp-lr ,t1 ,t2 t)))

(defmacro lexico-comp-lr (t1 t2 &optional equiv)
  `(lexico-comp-real ,t1 ,t2 (args-of ,t1) (args-of ,t2) ,equiv))

(defmacro lexico-comp-rl (t1 t2 &optional equiv)
  `(lexico-comp-real ,t1 ,t2 (reverse (args-of ,t1)) (reverse (args-of ,t2)) ,equiv))

(defun lexico-comp-real (t1 t2 lis1 lis2 equiv)
  (sloop while (and lis1 lis2) do
	 (if* (lrpo= (car lis1) (car lis2))
	      then (pop lis1) (pop lis2)
	      else (return)))
  (cond ((null lis1) (if (and equiv (null lis2)) t nil))
	((null lis2) t)
	((lrpo> (car lis1) (car lis2))
	 (if equiv
	     (sloop for xb in (cdr lis2) always (lrpo>= t1 xb))
	   (sloop for xb in (cdr lis2) always (lrpo> t1 xb))))
	(t (sloop for xa in (cdr lis1) thereis (lrpo>= xa t2)))))

(defun lrpo= (t1 t2)
  ;  Tests if the two terms, T1 and T2, are equivalent.
  ;	    (let t = f(t1,t2,...,tn) and s = g(s1,s2,...sm)
  ;	     t is equivalent to s iff f ~ g in precedence, n = m and
  ;	     there is a permutation on 1...n such that t1 ~ sj where
  ;	     i is mapped to j.
  ;	     If, however, f and g have status then s1 ~ ti for i = 1,2,...,n
  ;	     Equivalent means same upto permutation of arguments.)
  (cond ((variablep t1) (equal t1 t2))
	((variablep t2) nil)
	((and (eqops (op-of t1) (op-of t2)) 
	      (= (get-arity (op-of t1)) (get-arity (op-of t2))))
	 (if* (op-has-status (op-of t1)) 
	    then (sloop for xa in (args-of t1)
		        as ya in (args-of t2) always (lrpo= xa ya))
	    elseif (args-of t1) 
	    then (equiv-list (args-of t1) (args-of t2))
	    else t))))

(defun equiv-list (l1 l2)
  ; Suppose l1 = {t1, t2, ..., tn} and l2 = {s1, s2, ..., sn}.
  ; Return t iff there is a permutation on 1...n such that 
  ;    equiv(ti, sj) where i is mapped to j.
  (sloop for xa in l1 do
	 (sloop for xb in l2
		if (lrpo= xa xb)
		return (setq l2 (append l3 l2))
		else collect xb into l3
		finally (return (setq l1 nil)))
	 (if (null l1) (return)))
  l1)

;;;;;;;;;;;; merged from aclrpo.lisp ;;;;;;;;;;;;;;;;;;

;; From Common Lisp to Franz Lisp:
;; (3) (if* ===> (if
;; (4) (sloop ===> (loop
;; (5) (lrpo> ===> (pure-lrpo 
;; (6) (op-has-status ===> (get-status
;; (7) (mult-diff-set (args-of l1) (args-of l2))
;;    ===>
;;   (mult-diff (mult-form (args-of l1)) (mult-form (args-of l2)))

(setq $aclrpo 'new) 

;  For efficiency consideration, the implementation of NEWAC-LRPO is 
;; not complete, because
;;    (1) we restricted the size of each (Ti - BigT) in the partition 
;;        to be <= 2;
;;    (2) we pull out the first big-root or eq-root subterm in a
;;        small-root term in T; and this is done for all such
;;        small-root terms in T at the same time.
;; Even with such restrictions, it works for most practical examples.

(defun aclrpo (t1 t2)
  ; Called when some operators are ac in the system. 
  ; Return t iff t1 is bigger than t2.
  ; Suppose t1 and t2 are already flattened.
  (cond
   ((null $aclrpo) (lrpo> t1 t2))
   ((eq $aclrpo 'new) (aco-lrpo> t1 t2))
;  ((eq $aclrpo 'poly) (poly-order> t1 t2))
   (t (if (prec-consistent (union (op-list t1) (op-list t2)))
	  (let ((t11 (distr-ac-order t1)) (t22 (distr-ac-order t2)))
	    (if (equal (cdr t11) (cdr t22)) 
		(greaterp (car t11) (car t22))
	      (lrpo> (cdr t11) (cdr t22))))))))

(defun prec-consistent (ops &aux acops min min2)
  ; return t if
  ;  (a) there are at most two ac-operators;
  ;  (b) one of ac-op is minial, except unary or nullary operators;
  ;  (c) the other ac-op is second minimal.
  (setq ops (sloop for op in ops 
		  if (and (not (is-bool-op op))
			  (> (get-arity op) 1)) collect op)
	acops (sloop for op in ops if (ac-op-p op) collect op))
  (if* (null (cddr acops)) then
      (if* (cdr acops) then 
	  (if* (grt-prec (first acops) (second acops))
	      then (setq min (second acops) 
			 min2 (first acops))
	      elseif (grt-prec (second acops) (first acops))
	      then (setq min2 (second acops) 
			 min (first acops)))
	  else (setq min (first acops)))
      (if* min then
	  (setq ops (set-diff ops acops))
	  (if* min2
	      then (sloop for op in ops always (grt-prec op min2))
	      else (sloop for op in ops always (grt-prec op min))))))

(defun distr-ac-order (term)
   (setq $num-trans 0
         term (ac-distri term))
   (cons $num-trans term))

(defun ac-distri (term &aux args)
  ; The same as using the rule "(x f y) g z ---> (x g z) f (y g z)"
  ; to simply TERM where f > g in the precedence.
  (if* (or (variablep term) (null (args-of term))) then term else
     (setq args (mapcar 'ac-distri (args-of term)))
     (sloop with op1 = (op-of term) with arg with args1 while args do
	    (setq arg (pop args))
	    (if* (or (variablep arg) (null (args-of arg)))
		then (setq args1 (append1 args1 arg))
		elseif (or (grt-prec op1 (op-of arg))
			   (and (eqops op1 (op-of arg)) 
				(> (op-of arg) op1))) 
		then (setq args (sloop for arg2 in (args-of arg)
				       collect
				       (compress-flat 
					 op1
					 (append args1 (cons arg2 args))))
			   term (compress-flat (op-of arg) args)
			   $num-trans (add1 $num-trans))
		     (return (ac-distri term))
		else (setq args1 (append1 args1 arg)))
	     finally (return (compress-flat op1 args1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; New code starts here ....  Hantao (3/19/90)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro aco-rpostatus> (t1 t2)
  ; Called when T1 and T2 have equivalent operators at the top
  ; level and those operators have status.  Compares the list of
  ; arguments from left-to-right or right-to-left and decides if T1 > T2.
  `(if (op-has-rl-status (op-of ,t1))
       (aco-lexico-comp-rl ,t1 ,t2)
       (aco-lexico-comp-lr ,t1 ,t2)))

(defmacro aco-rpostatus>= (t1 t2)
  `(if (op-has-rl-status (op-of ,t1))
       (aco-lexico-comp-rl ,t1 ,t2 t)
       (aco-lexico-comp-lr ,t1 ,t2 t)))

(defun aco-lrpo> (t1 t2)
  (cond	((variablep t1) nil)
        ((variablep t2) (is-subt t2 t1))
	((equal (op-of t1) 'pc) (aco-lrpo> (first-arg t1) t2))
        ((eqops (op-of t1) (op-of t2))
	 (cond ((ac-root t1) (aco-hard> t1 t2))
	       ((null (args-of t2)) (args-of t1))
	       ((and (op-has-status (op-of t1))
		     (equal (length t1) (length t2)))
		(aco-rpostatus> t1 t2))
	       (t (aco-rpomult> t1 t2))))
	((grt-prec (op-of t1) (op-of t2))
	 (sloop for xb in (args-of t2) always (aco-lrpo> t1 xb)))
	(t (sloop for xa in (args-of t1) thereis (aco-lpro>= xa t2)))))

(defun aco-lpro>= (t1 t2)
  ;; return t iff t1 >rpo t2 or t1 =rpo t2.
  (cond ((variablep t1) (eq t1 t2))
	((variablep t2) (is-subt t2 t1))
	((equal (op-of t1) 'pc) (aco-lrpo> (first-arg t1) t2))
	((eqops (op-of t1) (op-of t2)) 
	 (cond ((null (args-of t2)) t)
	       ((and (op-has-status (op-of t1))
		     (equal (length t1) (length t2)))
		(aco-rpostatus>= t1 t2))
	       (t (aco-rpomult>= t1 t2))))
	((grt-prec (op-of t1) (op-of t2))
	 (sloop for xb in (args-of t2) always (aco-lrpo> t1 xb)))
	(t (sloop for xa in (args-of t1) thereis (aco-lpro>= xa t2)))))

(defmacro aco-delete-equiv ()
  `(sloop for x1 in l1 do
	 (sloop for x2 in l2 
		if (and (> (cdr x2) 0)
		        (aco-lrpo= (car x1) (car x2))
			;;(equal (car x1) (car x2))
			)
		do
		(if* (>= (cdr x1) (cdr x2))
		     then 
		     (setf (cdr x1) (- (cdr x1) (cdr x2)))
		     (setf (cdr x2) 0)
		     else
		     (setf (cdr x2) (- (cdr x2) (cdr x1)))
		     (setf (cdr x1) 0)
		     ))))

(defmacro aco-collect-bigt ()
  ;; Collect all bigt in l1.
  `(sloop with res for xa in l1
	  for ti = (car xa) 
	  if (and (> (cdr xa) 0) (nonvarp ti)
		  (or (equal (op-of ti) 'pc) (grt-prec (op-of ti) f)))
	  do
	  (if (equal (op-of ti) 'pc) 
	      (push ti res)			    
	    (push (list 'pc ti) res))
	  (setq s1 (- s1 (cdr xa)))
	  (setf (cdr xa) 0)
	  finally (return res)))

(defmacro aco-compute-sizes ()
  `(setq l1 (sloop for xa in l1 if (> (cdr xa) 0) 
		  collect (progn (setq s1 (+ s1 (cdr xa))) xa))
	 l2 (sloop for xa in l2 if (> (cdr xa) 0) 
		  collect (progn (setq s2 (+ s2 (cdr xa))) xa))))

(defmacro my-copylist2 (l1)
  `(sloop for xa in ,l1 collect (cons (car xa) (cdr xa))))

(defmacro aco-pull-out-big-eq-subs ()
  ;; For each term t in l1, decide whether there is subterm of t
  ;; whose root is >= f. Adjust s1 accordingly.
  `(sloop with res with sub 
	  for xa in l1 do
	  (if (and (nonvarp (car xa))
		   (> (cdr xa) 0)
		   (setq sub (find-out-big-eq-subs f (car xa))))
	      (if* (eqops (op-of sub) f)
		   then 
		   (sloop for arg in (args-of sub) do
			  (push (cons arg (cdr xa)) res))
		   (setq s1 (+ s1 (* (cdr xa) (1- (length (args-of sub))))))
		   else
		   (push (cons sub (cdr xa)) res)
		   )
	    (push xa terms))
	  finally (return res)))

(defun aco-hard> (l1 l2 &aux (f (op-of l1)) (s1 0) (s2 0) terms)
  ;  The root operator of T1 and T2 are equivalent AC.
  ;  Returns T if T1 >aco T2.
  (setq l1 (mult-form (args-of l1))
	l2 (mult-form (args-of l2)))

  ;; Step 1: Delete equivalent terms from both l1 and l2.
  ;; Compute the sizes of T and S.
  (aco-delete-equiv)
  (aco-compute-sizes)

  (cond ((null l2) l1)
	((null l1) nil)

	;; Step 3: Partitoin T into T1 U T2 U ... U Tm.
	;; Try to prove f(Ti) > si.
	((and (>= s1 s2)
	      (aco-nobigt-partition 
	       f (my-copylist2 l1) (my-copylist2 l2) (- s1 s2))))

	;; Step 4: Pseudo-copy big-root subterms,
	;; and partitoin the remaining T into T1 U T2 U ... U Tm.
	;; Try to prove f(Ti U BigT) > si.
	((setq terms (aco-collect-bigt))
	 (aco-bigt-partition f terms l1 l2 s1))

	;; Step 5: Pull out arguments of small-root subterms.
	((setq l1 (aco-pull-out-big-eq-subs))
	 (aco-harder f l1 terms l2))

	(t nil)
	))

(defun aco-harder (f l1 terms l2 &aux (s1 0) (s2 0))
  ;; Step 5.1: Delete equivalent terms from both l1 and l2.
  (aco-delete-equiv)

  ;; Step 5.2: Compute the sizes of T and S.
  (setq l1 (nconc terms l1))
  (aco-compute-sizes)

  ;; Step 5.3: Partitoin T into T1 U T2 U ... U Tm.
  (cond ((null l2) t)
	((null l1) nil)
	
	;; Step 5.4: Pseudo-copy big-root subterms.
	((setq terms (aco-collect-bigt))
	 (aco-bigt-partition f terms l1 l2 s1))

	((>= s1 s2) (aco-nobigt-partition f l1 l2 (- s1 s2)))
	(t nil)
	))

(defun aco-nobigt-partition (f l1 l2 surplus &aux ss)
  ;; Partitoin l1 into T1 U T2 U ... U Tm, where m = |l2|, such that
  ;; for any term ti in l2, there exists Ti, f(Ti) >aco ti.
  ;; Ti cannot be empty. For efficiency, we require that |Ti| <= 2.
  ;; Though this is not complete.
  ;; surplus is the # of elements in l1 - the # of elements in l2.
  (sloop for xb in l2 always
	 (or (one-kill-one l1 xb)

	     (and (nonvarp (car xb))
		  (grt-prec f (op-of (car xb)))
		  (>= (setq ss (- surplus (cdr xb))) 0)  
		  (two-kill-one f l1 xb)
		  (setq surplus ss))

;	     (and (>= (setq ss (- surplus (* 2 (cdr xb)))) 0)  
;		  (three-kill-one f l1 xb)
;		  (setq surplus ss))

	     )))


(defun one-kill-one (l1 xb)
  ;; Find a term ti in l1 such that ti >lrpo xb.
  (sloop for xa in l1 do
	 (if (and (> (cdr xa) 0) (aco-lrpo> (car xa) (car xb)))
	     (if* (>= (cdr xa) (cdr xb))
		 then
		 (setf (cdr xa) (- (cdr xa) (cdr xb)))
		 (return t)
		 else
		 (setf (cdr xb) (- (cdr xb) (cdr xa)))
		 (setf (cdr xa) 0)))
	 finally (return nil)))

(defun two-kill-one (f l1 xb &aux min)
  ;; Find two distinct terms t1 and t2 in l1 such that f(t1, t2) >lrpo xb.
  (or 

   ;; the same term ti is used twice.
   (sloop with n2 = (* 2 (cdr xb))
	  for xa in l1 
	  if (and (>= (cdr xa) n2)
		  (aco-lrpo> (list f (car xa) (car xa)) (car xb)))
	  return (progn (setf (cdr xa) (- (cdr xa) n2)) t)
	  finally (return nil))

   ;; two different ti and tj are used.
   (sloop for l11 on l1 
	 for xa1 = (car l11) 
	 if (> (cdr xa1) 0) do
	 (sloop for xa2 in (cdr l11) do
		(if* (and (> (cdr xa2) 0)
			  (aco-lrpo> (list f (car xa1) (car xa2)) (car xb)))
		    then
		    (setq min (min (cdr xa1) (cdr xa2)))
		    (if* (>= min (cdr xb))
			 then
			 (setf (cdr xa1) (- (cdr xa1) (cdr xb)))
			 (setf (cdr xa2) (- (cdr xa2) (cdr xb)))
			 (setq min 'done)
			 (return t)
			 else
			 (setf (cdr xb) (- (cdr xb) min))
			 (setf (cdr xa1) (- (cdr xa1) min))
			 (setf (cdr xa2) (- (cdr xa2) min)))))
	 (if (eq min 'done) (return t))
	 finally (return nil))
  ))

;(defun three-kill-one (f l1 xb &aux min)
;  (terpri)
;  (princ "THREE-KILL-ONE: not implemented.")
;  (terpri)
;  nil)
  
(defun aco-bigt-partition (f bigt l1 l2 s1 &aux s11)
  ;; Partitoin l1 into T1 U T2 U ... U Tm, where m = |l2|, such that
  ;; for any term ti in l2, there exists Ti, f(Ti U bigT) >aco ti.
  ;; Ti can be empty.
  (sloop with fbigt = (make-term f bigt) 
	 for xb in l2  always
	 (or (aco-lrpo> fbigt (car xb))

	     (if (and (nonvarp (car xb))
		      (grt-prec f (op-of (car xb))))

		 (or (and (>= (setq s11 (- s1 (cdr xb))) 0) 
			  (bigt-one-kill-one f bigt l1 xb)
			  (setq s1 s11))

		     (and (>= (setq s11 (- s1 (* 2 (cdr xb)))) 0) 
			  (bigt-two-kill-one f bigt l1 xb)
			  (setq s1 s11))
		     )

	       (and (>= (setq s11 (- s1 (cdr xb))) 0) 
		    (one-kill-one l1 xb)
		    (setq s1 s11))
	       ))))

(defun bigt-one-kill-one (f bigt l1 xb)
  ;; Find a term ti in l1 such that f(bigt, ti) >lrpo term.
  (sloop for xa in l1 do
	 (if (and (> (cdr xa) 0) 
		  (aco-lrpo> (make-term f (cons (car xa) bigt))
			       (car xb)))
	     (if* (>= (cdr xa) (cdr xb))
		 then
		 (setf (cdr xa) (- (cdr xa) (cdr xb)))
		 (return t)
		 else
		 (setf (cdr xb) (- (cdr xb) (cdr xa)))
		 (setf (cdr xa) 0)))
	 finally (return nil)))

(defun bigt-two-kill-one (f bigt l1 xb &aux min)
  ;; Find two distinct terms t1 and t2 in l1 such that 
  ;;     f(bigt, t1, t2) >lrpo term.
  (sloop for l11 on l1 
	 for xa1 = (car l11) 
	 if (> (cdr xa1) 0) do
	 (sloop for xa2 in (cdr l11) do
		(if* (and (> (cdr xa2) 0)
			  (aco-lrpo> 
			   (make-term f (cons (car xa1) (cons (car xa2) bigt)))
			   (car xb)))
		    then
		    (setq min (min (cdr xa1) (cdr xa2)))
		    (if* (>= min (cdr xb))
			 then
			 (setf (cdr xa1) (- (cdr xa1) (cdr xb)))
			 (setf (cdr xa2) (- (cdr xa2) (cdr xb)))
			 (setq min 'done)
			 (return t)
			 else
			 (setf (cdr xb) (- (cdr xb) min))
			 (setf (cdr xa1) (- (cdr xa1) min))
			 (setf (cdr xa2) (- (cdr xa2) min)))))
	 (if (eq min 'done) (return t))
	 finally (return nil)))

(defun aco-rpomult> (l1 l2)
  ;  Called when the top-level operators, T1 and T2, are equivalent
  ;	    and have multiset status.  Returns T if T1 > T2.
  (setq l2 (mult-diff-set (args-of l1) (args-of l2))
	l1 (car l2)
	l2 (cdr l2))
  (cond ((null l2) l1)
	((null l1) nil)
	(t (sloop for xa in l2 always
		  (sloop for xb in l1 thereis (aco-lrpo> xb xa))))))

(defun aco-rpomult>= (l1 l2)
  ;; Called when the top-level operators, T1 and T2, are equaluivalent
  ;; and have multiset status.  Returns T if T1 > T2.
  (setq l2 (mult-diff-set (args-of l1) (args-of l2))
	l1 (car l2)
	l2 (cdr l2))
  (cond ((null l2) t)
	((null l1) nil)
	(t (sloop for xa in l2 always
		  (sloop for xb in l1 thereis (aco-lpro>= xb xa))))))

(defun aco-lexico-comp-lr (t1 t2 &optional equiv &aux lis1 lis2)
  (setq lis1 (args-of t1) 
	lis2 (args-of t2))
  (sloop while (and lis1 lis2)
	 do
	 (if* (aco-lrpo= (car lis1) (car lis2))
	      then (pop lis1) (pop lis2)
	      else (return)))
  (cond ((null lis1) (if (and equiv (null lis2)) t nil))
	((null lis2) t)
	((aco-lrpo> (car lis1) (car lis2))
	 (if equiv
	     (sloop for xb in (cdr lis2) always (aco-lpro>= t1 xb))
	   (sloop for xb in (cdr lis2) always (aco-lrpo> t1 xb))))
	(t (sloop for xa in (cdr lis1) thereis (aco-lpro>= xa t2)))))

(defun aco-lexico-comp-rl (t1 t2 &optional equiv &aux l1 l2)
  (setq l1 (length (cdr t1))
	l2 (length (cdr t2)))
  (sloop while (and (> l1 0) (> l2 0))
	 do
	 (if* (aco-lrpo= (nth l1 t1) (nth l2 t2))
	      (setq l1 (1- l1) l2 (1- l2))
	      (return)))
  (cond ((eq l1 0) (if (and equiv (eq l2 0)) t nil))
	((eq l2 0) t)
	((aco-lrpo> (nth l1 t1) (nth l2 t2))
	 (if equiv
	     (sloop for xb from 1 to (1- l2) 
		    always (aco-lpro>= t1 (nth xb t2)))
	   (sloop for xb from 1 to (1- l2) 
		  always (aco-lrpo> t1 (nth xb t2)))))
	(t (sloop for xa from 1 to (1- l1) 
		  thereis (aco-lpro>= (nth xa t1) t2)))))  

(defun aco-lrpo= (t1 t2)
  ;  Tests if the two terms, T1 and T2, are equivalent.
  ;	    (let t = f(t1,t2,...,tn) and s = g(s1,s2,...sm)
  ;	     t is equivalent to s iff f ~ g in precedence, n = m and
  ;	     there is a permutation on 1...n such that t1 ~ sj where
  ;	     i is mapped to j.
  ;	     If, however, f and g have status then s1 ~ ti for i = 1,2,...,n
  ;	     Equivalent means same upto permutation of arguments.)
  (cond ((variablep t1) (equal t1 t2))
	((variablep t2) nil)
	((and (eqops (op-of t1) (op-of t2)) 
	      (equal (length (args-of t1)) (length (args-of t2))))
	 (if* (op-has-status (op-of t1)) 
	    then (sloop for xa in (args-of t1)
		        as ya in (args-of t2) always (aco-lrpo= xa ya))
	    elseif (args-of t1) 
	    then (aco-equiv-list (args-of t1) (args-of t2))
	    else t))))

(defun aco-equiv-list (l1 l2)
  ; Suppose l1 = {t1, t2, ..., tn} and l2 = {s1, s2, ..., sn}.
  ; Return t iff there is a permutation on 1...n such that 
  ;    equiv(ti, sj) where i is mapped to j.
  (sloop for xa in l1 do
	 (sloop for xb in l2
		if (aco-lrpo= xa xb)
		return (setq l2 (append l3 l2))
		else collect xb into l3
		finally (return (setq l1 nil)))
	 (if (null l1) (return)))
  l1)

(defun find-out-big-eq-subs (f term)
  ;; This function resturns the first bigt in term.
  (if (grt-prec (op-of term) f) term
    (if (eqops (op-of term) f) term
      (sloop for arg in (args-of term)
	     if (and (nonvarp arg) (setq arg (find-out-big-eq-subs f arg)))
	     return arg))))

(defun car-lrpo< (x1 x2) (aco-lrpo> (car x2) (car x1)))

(defmacro is-prec-related (o1 o2)
  `(or (member ,o2 (cdr (assoc ,o1 $precedence)))
       (member ,o1 (cdr (assoc ,o2 $precedence)))
       (eqops ,o1 ,o2)))

(defun is-rel-prec (op1 op2)
  ; Check if OP1 and OP2 are related in precedence.
  (or (is-prec-related op1 op2)
      (neq (default-precedence op1) (default-precedence op2))))

(defmacro eqops (l1 l2)
  ; Checks if L1 and L2 are equivalent in the precedence.
  `(member ,l2 (ops-equiv-to ,l1)))

; To orient rules, function symbols must have some precedence relation
; and there is a concept of equivalent operators.  All this information
; is stored in two global variables which are:
;   $GLOB-PREC	A list of list of operators. The first operator
;               in each list is greater in precedence than the other
;               operators in the list.
;   $EQOP-LIST	A list of lists of operators.  All the operators in
;               each list are equivalent in precedence.
; If an operator has status, that information is stored on the property
; list of the operator itself (under status - rl or lr).  There is also a
; need to maintain a global list $ST-LIST which contains a list of all
; operators that have been assigned status.  This is needed because when
; the system is initialized, all operators should have no status.
; It should be noted that equivalent operators have the same status.
; When the precedence relation is extended, information must be updated
; correctly.
;
; The following functions maintain the precedence list and can update them.
;

(defmacro grt-prec (op1 op2)
  ; Checks if OP1 > OP2 in the precedence.
  `(if* (member ,op2 (cdr (assoc ,op1 $precedence))) then t
      elseif (member ,op1 (cdr (assoc ,op2 $precedence))) then nil
      else (> (default-precedence ,op1) (default-precedence ,op2))))

(defun default-precedence (op1)
  ; Return the default precedence value of op1.
  ; The following defualt precedence relations is assumed:
  ;    6.  {non-constant-skolem-functions}
  ;    5.  {prdicates, functions} >
  ;    4.  {constant-funcs} > 
  ;    3.  {booleans} >
  ;    2.  $anspred >
  ;    1.  {constructors} >
  ;    0.  {constant-constructors}
  (cond 
   ((memq op1 *true*false*) 0)
   ((memq op1 $constructors) (if (is-constant-op op1) 0 1))
   ;((eq op1 $anspred) 2)
   ((is-bool-op op1) 3)
   ((and (neq $condi 'i) (predicatep op1)) 5)
   ((is-constant-op op1) 4)
   ((is-skolem-op op1) 6)
   (t 5)))

(defun operator-ordering (op1 op2)
  ; Checks if OP1 > OP2 in the precedence.
  (if* (member op2 (cdr (assoc op1 $precedence))) then t
      elseif (member op1 (cdr (assoc op2 $precedence))) then nil
      else (let ((n1 (default-precedence op1))
		 (n2 (default-precedence op2)))
	     (if* (> n1 n2) then t
		 elseif (< n1 n2) then nil
		 elseif (> (get-arity op1) (get-arity op2)) then t
		 elseif (< (get-arity op1) (get-arity op2)) then nil
		 else (> op1 op2)))))

(defun total-op-ordering (op1 op2)
  ; Checks if OP1 > OP2 in the precedence.
  (if* (member op2 (cdr (assoc op1 $precedence))) then t
      elseif (member op1 (cdr (assoc op2 $precedence))) then nil
      else (let ((n1 (default-precedence op1))
		 (n2 (default-precedence op2)))
	     (if* (= n1 3)
		  then (if (= n2 3) (< n1 n2) t)
		  elseif (= n2 3) then nil
		  elseif (> n1 n2) then t
		  elseif (< n1 n2) then nil
		  elseif (> (get-arity op1) (get-arity op2)) then t
		  elseif (< (get-arity op1) (get-arity op2)) then nil
		  else (> op1 op2)))))

(defun ops-equiv-to (op)
  ; Returns a list of operators equivalent to OP in the precedence.
  ; Note: at least (OP) will be returned.
  (let (temp)
    (sloop for xa in $eqop-list do
	  (if* (member op xa) then (setq temp xa) (return nil)))
    (if* temp then temp else (ncons op))))

(defun equiv-ops (op)
  ; Returns a list of operators equivalent to OP in the precedence.
  ; Note: If only one operaotr in the list, i.e., OP itself, then
  ; the empty list will be returned.
  (sloop for xa in $eqop-list if (member op xa) return xa))

(defun update-by-eq (op1)
  ;  Update $GLOB-PREC such each operator equivalent to OP1 has
  ; the same precedence relation with other operators.
  (let ((tail (cdr (assoc op1 $precedence))) l1)
     (sloop for op in (equiv-ops op1) do
	(if* (neq op op1) then
	   (if* (setq l1 (assoc op $precedence)) 
		then (rplacd l1 tail)
		else (setq $precedence
			   (nconc $precedence (ncons (cons op tail)))))))))

(defun ok-prev-rules (op &aux (temp t))
  ;  Called when the user introduces status for an operator in
  ; the middle.  This may upset the orientation of some of the
  ; previous rules and it may not be wise to proceed so first
  ; ask the user and flag this.
  (sloop for xa in $rule-set 
	 if (not (or (is-deleted-rule xa) (predicatep (op-of (lhs xa)))))
	 do (if* (member op (op-list (lhs xa)))
		 then
		 (if* (not (lrpo (lhs xa) (rhs xa)))
		      then (terpri)
		      (princ "The following rule is not orientable now:")
		      (terpri) (write-rule xa)
		      (if* (not (ok-to-continue))
			   then 
			   (setq temp nil)
			   (return nil)))))
  (when temp
    (princ (uconcat "Operator, " (op-name op) ", given status: "))
    (princ (get-op-status-name op)) (terpri))
  temp)

(defun remove-eq-op (ops)
  ;  If op1 and op2 are equivalent and both in OPS, then remove one of them.
  (let (op ops2)
     (sloop while ops do 
	(setq op (pop ops))
	(if* (> (get-arity op) 1) then
	   (sloop for o in (equiv-ops op) do 
		(setq ops (delete0 o ops)
		      ops2 (delete0 o ops2))))
	(append1 ops2 op t))
   ops2))

(defun trans-status (op2 op1)
  (let ((status (get-op-status-name op1)))
     (sloop for op in (ops-equiv-to op2) do
	    (set-op-status op status))))

(defun status-candidates (ops)
  ;  Return those operators in OPS that have not status and
  ; their arity is bigger than 1.
  (sloop for op in ops 
	if (and (> (get-arity op) 1) (not (op-has-status op))) 
	collect op))

(defun print-sugg-info (t1 t2 sugg twoway eqn &aux l3)
    (terpri) (princ "  To order:  ")
    (write-term t1) (princ "  >  ") (write-term-bool t2) (terpri)  
    (if* twoway then (princ "        or:  ")
        (write-term-bool t1) (princ "  <  ") (write-term-bool t2) (terpri))
    (if* sugg then
	(princ "  Here are some precedence suggestions:") (terpri)
	(sloop for xa in sugg as i from 1 do
	    (if* l3 
	      then 
	      (if (< i 10) (tab 31) (tab 30))
	      (format t "      ~d.  " i)
	      (princ (op-name (car xa))) (princ " > ")
	      (princ (op-name (cadr xa))) (terpri)
	      (setq l3 nil) 
	      else
	      (if (< i 10) (princ " "))
	      (format t "      ~d.  " i)
	      (princ (op-name (car xa))) (princ " > ")
	      (princ (op-name (cadr xa)))
	      (if twoway (setq l3 t) (terpri))))
        (princ "Either type a list of numbers or") (terpri)
     elseif (and (not twoway) (not (ctx eqn))
		 (is-subset (get-lhs-vars eqn) (get-rhs-vars eqn)))
       then (princ "I have no precedence suggestions.  ") 
	    (princ "You wanted to orient it from left to right,") (terpri)
	    (princ "    however, it may be orientable in the other")
	    (princ " direction. ") (terpri)
	    (princ "Try doing Equiv or Status.") (terpri) 
       else (princ "I have no precedence suggestions.  ") (terpri)
	    (princ "Try doing Equiv or Status.") (terpri) 
    ))

(defun precedence-suggestions (l1 l2 twoway &aux l3 pair)
  ; L1 and L2 are two lists of operators (one of T1, one of T2
  ; to make a rule T1 -> T2).  Called when LRPO cannot orient
  ; and seek to increment the precedence relation on function
  ; symbols to make this rule orientable.  This returns a list
  ; of pairs of unrelated operators so that the user can choose
  ; which suggestions he wants.
  (setq l1 (remove-eq-op l1)  
	l2 (remove-eq-op l2))
  
  (sloop for opl in l1 do
	 (sloop for opr in l2 do
		(unless (or (is-rel-prec opl opr)
			    (member0 (setq pair (list opl opr)) l3))
		  (append1 l3 pair t)
		  (if twoway (append1 l3 (list opr opl) t)))))
  l3)

(defun remove-sugg (sugg)
  ;  Remove the suggestions in "sugg" that have already 
  ; a relation in the precedence.
  (sloop for s in sugg if (not (is-rel-prec (car s) (cadr s))) collect s))

(defun add-sugg (op1 op2)
  ;  SUGG is a list of two operators (op1 op2).  Adds the relation
  ; op1 > op2 in the precedence and make sure the global
  ; varaible $GLOB-PREC is updated correctly.
  (cond ((null $precedence) 
         (setq $precedence (ncons (cons op1 (ops-equiv-to op2)))))
        ((assoc op1 $precedence) (add-sugg1 op1 op2))
	(t (setq $precedence (cons (ncons op1) $precedence))
	   (add-sugg1 op1 op2)))
  (update-by-eq op1))

(defun add-sugg1 (op1 op2)
  ; Local function.  Called by ADD-SUGG.
  (dolist (xa $precedence)
	  (when (member op1 xa)
		(dolist (o2 (ops-equiv-to op2)) 
			(if (not (member o2 xa)) (push-end o2 xa)))
		(dolist (o2 (assoc op2 $precedence)) 
			(if (not (member o2 xa)) (push-end o2 xa)))
		)))

