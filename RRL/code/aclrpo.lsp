(in-package "USER")

(setq $aclrpo 'new) 

;  For efficiency consideration, the implementation of NEWAC-LRPO is 
;; not complete, because
;;    (1) we restricted the size of each (Ti - BigT) in the partition 
;;        to be <= 2;
;;    (2) we pseudo-copy all big-root terms in T at the same time;
;;    (3) we pull out the first big-root or eq-root subterm in a
;;        small-root term in T; and this is done for all such
;;        small-root terms in T at the same time.
;; Even with such restrictions, it works for most practical examples.

(defun aclrpo (t1 t2)
  ; Called when some operators are ac in the system. 
  ; Return t iff t1 is bigger than t2.
  ; Suppose t1 and t2 are already flattened.
  (cond
   ((null $aclrpo) (pure-lrpo t1 t2))
   ((eq $aclrpo 'new) (aco-lrpo> t1 t2))
   ;((eq $aclrpo 'poly) (poly-order> t1 t2))
   (t (if* (prec-consistent (union (op-list t1) (op-list t2)))
	  (let ((t11 (distr-ac-order t1)) (t22 (distr-ac-order t2)))
	    (if* (equal (cdr t11) (cdr t22)) 
		(greaterp (car t11) (car t22))
	      (pure-lrpo (cdr t11) (cdr t22))))))))

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
  `(if* (eq (get-status (op-of ,t1)) 'rl)
       (aco-lexico-comp-rl ,t1 ,t2)
       (aco-lexico-comp-lr ,t1 ,t2)))

(defmacro aco-rpostatus>= (t1 t2)
  `(if* (eq (get-status (op-of ,t1)) 2)
       (aco-lexico-comp-rl ,t1 ,t2 t)
       (aco-lexico-comp-lr ,t1 ,t2 t)))

(defun aco-lrpo> (t1 t2)
  (cond	((variablep t1) nil)
        ((variablep t2) (is-subt t2 t1))
	((eq (op-of t1) 'pc) (aco-lrpo> (first-arg t1) t2))
        ((eqops (op-of t1) (op-of t2))
	 (cond ((ac-root t1) (aco-hard> t1 t2))
	       ((null (args-of t2)) (args-of t1))
	       ((and (get-status (op-of t1))
		     (eq (length t1) (length t2)))
		(aco-rpostatus> t1 t2))
	       (t (aco-rpomult> t1 t2))))
	((grt-prec (op-of t1) (op-of t2))
	 (sloop for xb in (args-of t2) always (aco-lrpo> t1 xb)))
	(t (sloop for xa in (args-of t1) thereis (aco-lpro>= xa t2)))))

(defun aco-lpro>= (t1 t2)
  ;; return t iff t1 >rpo t2 or t1 =rpo t2.
  (cond ((variablep t1) (eq t1 t2))
	((variablep t2) (is-subt t2 t1))
	((eq (op-of t1) 'pc) (aco-lrpo> (first-arg t1) t2))
	((eqops (op-of t1) (op-of t2)) 
	 (cond ((null (args-of t2)) t)
	       ((and (get-status (op-of t1))
		     (eq (length t1) (length t2)))
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
		  (or (eq (op-of ti) 'pc) (grt-prec (op-of ti) f)))
	  do
	  (if* (eq (op-of ti) 'pc) 
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
	  (if* (and (nonvarp (car xa))
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
  ;; Ti cannot be empty. For efficiency, we require that |Ti - BigT| <= 2.
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
  ;; Find a term ti in l1 such that ti >lrpo term.
  (sloop for xa in l1 do
	 (if* (and (> (cdr xa) 0) (aco-lrpo> (car xa) (car xb)))
	     (if* (>= (cdr xa) (cdr xb))
		 then
		 (setf (cdr xa) (- (cdr xa) (cdr xb)))
		 (return t)
		 else
		 (setf (cdr xb) (- (cdr xb) (cdr xa)))
		 (setf (cdr xa) 0)))
	 finally (return nil)))

(defun two-kill-one (f l1 xb &aux min)
  ;; Find two distinct terms t1 and t2 in l1 such that f(t1, t2) >lrpo term.
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
	 (if* (eq min 'done) (return t))
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

	     (if* (and (nonvarp (car xb))
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
	 (if* (and (> (cdr xa) 0) 
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
	 (if* (eq min 'done) (return t))
	 finally (return nil)))

(defun aco-rpomult> (l1 l2)
  ;  Called when the top-level operators, T1 and T2, are equivalent
  ;	    and have multiset status.  Returns T if T1 > T2.
  (setq l2 (mult-diff (mult-form (args-of l1)) (mult-form (args-of l2)))
	l1 (car l2)
	l2 (cdr l2))
  (cond ((null l2) l1)
	((null l1) nil)
	(t (sloop for xa in l2 always
		  (sloop for xb in l1 thereis (aco-lrpo> xb xa))))))

(defun aco-rpomult>= (l1 l2)
  ;; Called when the top-level operators, T1 and T2, are equivalent
  ;; and have multiset status.  Returns T if T1 > T2.
  (setq l2 (mult-diff (mult-form (args-of l1)) (mult-form (args-of l2)))
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
  (cond ((null lis1) (if* (and equiv (null lis2)) t nil))
	((null lis2) t)
	((aco-lrpo> (car lis1) (car lis2))
	 (if* equiv
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
  (cond ((eq l1 0) (if* (and equiv (eq l2 0)) t nil))
	((eq l2 0) t)
	((aco-lrpo> (nth l1 t1) (nth l2 t2))
	 (if* equiv
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
	 (if* (get-status (op-of t1)) 
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
	 (if* (null l1) (return)))
  l1)

(defun find-out-big-eq-subs (f term)
  ;; This function resturns the first bigt in term.
  (if* (grt-prec (op-of term) f) term
    (if* (eqops (op-of term) f) term
      (sloop for arg in (args-of term)
	     if (and (nonvarp arg) (setq arg (find-out-big-eq-subs f arg)))
	     return arg))))

(defun car-lrpo< (x1 x2) (aco-lrpo> (car x2) (car x1)))
