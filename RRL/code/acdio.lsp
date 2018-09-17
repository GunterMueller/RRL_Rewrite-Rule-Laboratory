;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")


(defun flatten-rule (rule)
 (change-lhs-rhs rule (flat-term (lhs rule)) (flat-term (rhs rule))))

(defun flatten-eqn (eqn)
  (setq eqn (change-lhs-rhs eqn (flat-term (lhs eqn)) (flat-term (rhs eqn))))
  (if* (ctx eqn) (change-ctx eqn (flatten-premises (ctx eqn))) eqn))

(defun flatten-premises (ctx)
  (if* (eq (car ctx) '*&*) then
      (cons '*&* 
	    (sloop for pre in (cdr ctx) 
		  collect (make-pre (flat-term (first pre)) 
				    (flat-term (second pre))
				    (cddr pre))))
      else
      (flat-term ctx)))

(defun flat-term-func (term) 
  ; Make sure every term in the system is flattend and brted.
  (if* (variablep term) then term else
      (setq term (if* $ac then (make-flat term)
		     elseif $commutative then (c-permutation term)
		     else term))
      (if* $in-fopc then (brt term) else term)))

(defun make-flat (term)
  (cond
    ((variablep term) term)
    ((null (args-of term)) term)
    (t (compress-flat (op-of term) (mapcar 'make-flat (args-of term))))))

(defun compress-flat (op args)
  (make-term op 
	(if* (ac-op-p op) 
	     then (flat-sort-args op args)
	     elseif (eq op '=) 
	     then (arrange-eq-args (first args) (second args)) args	     
	     elseif (commutativep op)
	     then (commu-exchange args)
	     else args)))

(defun flat-sort-args (op args)
    (sloop with ans for arg in args do
        (setq ans (if* (and (nonvarp arg) (eq op (op-of arg))) 
			then (merge-list (args-of arg) ans 'total-order)
			else (insert-list arg ans 'total-order)))
	finally (return ans)))

(defun is-assoc-under-c (t1 t2)
   ; Return T iff T1 is of form "f(f(x, y), z)" and T2 of form
   ; "f(x, f(y, z))" or vice versa, where "f" is commutative.
   (and	(is-assoc-pair t1 t2)
	(memq (op-of t1) $commutative)))

(defun is-assoc-pair (t1 t2 &aux ops vars)
  (and (nonvarp t1) 
       (= (get-arity (op-of t1)) 2)
       (= (length (setq ops (all-ops t1))) 2)
       (eq (car ops) (cadr ops))
       (= (length (setq vars (var-list t1))) 3)
       (equal ops (all-ops t2))
       (is-subset vars (setq ops (var-list t2)))
       (is-subset ops vars)
       (nequal (first-arg t1) (first-arg t2))
       (nequal (second-arg t1) (second-arg t2))))

(defun make-ass-com-op (op eqn ac-flag &aux ops)
  (start-push-history eqn)
  (terpri)
  (princ (uconcat "'" op "' has the "
		  (if* ac-flag then "associative and " else "")
		 "commutative property now: ")) (terpri) 
  (princ "    ") (write-eqn eqn)

  (if* (get op 'status) then
     (princ (uconcat "'" op "' has been given the status " 
		(get op 'status) "."))
     (princ " Now, the status is cancelled.") (terpri)
     (remprop op 'status)
     (delete0 op (ops-equiv-to op)))

  (if* ac-flag then (push op $ac) 
		   (setq $commutative (delete0 op $commutative 1))
	      else (push op $commutative))

  (setq ac-flag (if* ac-flag then 'make-flat else 'c-permutation))

  ; >>>>> 1/29/89
  (if* $witness-eqn (flatten-witness (eqn-source eqn)))

  ;;(if* $prove-eqn (setq $prove-eqn (flatten-eqn eqn)))

  ; >>>>> 4/29/89
  (setq $p-commut-rules (sloop for rule in $p-commut-rules 
			      if (not (member op rule)) collect rule))

  (if* $testset (flatten-testset ac-flag eqn))
      
  (setq ops (flatten-rules op ac-flag (eqn-source eqn)))
  (if* (and ops (neq 'make-flat ac-flag)) (wash-def-rules ops)))

(defun flatten-rules (op flatten &optional source &aux def-rule-ops)
  ; Flatten the equations and rules in the current system.
  ; Delete the rules which have "op".
  ; If the ac is the first time introduced, then changeing the
  ; critical pair computing strategies.
  (setq $free-constructors (delete0 op $free-constructors))
  (if* $post-ass-set then (flatten-post-ass flatten))
  (setq def-rule-ops (flatten-rules2 op flatten source))
  (setq $eqn-set (mapcar 'flatten-eqn $eqn-set)
	$post-set (mapcar 'flatten-eqn $post-set))
  ; If this is the first AC operator, then change the strategy of
  ; computing critical pairs.
  (if* (and (eq flatten 'make-flat) (null (cdr $ac))) then
      (setq $blocking-on 'y $norm_str 'o)
      (sloop for xa in $rule-set do
        (if* (not (crit-marked xa))
	    then (sloop for xb in $rule-set do (add-pairs xa xb)))))
  def-rule-ops)

(defun flatten-rules2 (op flatten source &aux l2 neweq def-rule-ops)
  ; Auxillary function of "faltten-rules".
  (sloop for xa in $rule-set 
	if (memq op (all-ops (lhs xa))) do
	(if* (> $trace_flag 1) then (terpri) 
	    (princ (uconcat "  The LHS of Rule contains '" op "', which is "
			    (if* (eq flatten 'c-permutation) 
				"commutative now."
			        "AC now."))) 
	    (terpri)
	    (write-rule xa))
	(if* (and $induc (eq (car (rule-source xa)) 'def)) 
	    then
	  (if* (eq flatten 'c-permutation)
	      (insert1 (op-of (lhs xa)) def-rule-ops))
	  else
	  (clean-rule xa) ; removes from op_list and if ac corr. pairs.
	  (setq l2 (make-eqn (lhs xa) (rhs xa) (ctx xa) 
			     (nconc (list 'deleted (ruleno xa) 'ac-op)
				    (if* source
					(if* (eq (car source) 'deleted)
					    (list (car source) (cadr source) 
						  (caddr source))
					    (list (car source) 
						  (cadr source)))))))
	  (push l2 neweq)))

  (sloop for xa in $rule-set do
	(if* (memq op (all-ops (rhs xa))) then
	  (if* (> $trace_flag 1) then (terpri) 
	      (princ (uconcat "  The RHS of Rule contains '" op "', which is "
			      (if* (eq flatten 'c-permutation)
				  "commutative now."
				"AC now."))) 
	      (terpri)
	      (write-rule xa))
	  (setq l2 (if* (predicatep (op-of (rhs xa)))
		       (norm-rhs (funcall flatten (rhs xa)))
		     (norm-ctx (funcall flatten (rhs xa)))))
	  (replace xa (change-rhs xa l2)))
	(if* (ctx xa) (replace xa (change-ctx xa (flatten-premises (ctx xa))))))

  (setq $eqn-set (nreconc neweq $eqn-set))
  def-rule-ops)

(defun flatten-post-ass (flatten &aux l2)
   (setq l2 $post-ass-set
	 $post-ass-set nil)
   (sloop with xb for xa in l2 do
     (if* (not (eq (cddr xa) (setq xb (funcall flatten (cddr xa))))) 
	then (if* (= $trace_flag 3) then
		(princ "Process proposition: ") (write-assertion (cdr xa)))
	     (process-ass-simple xb (cadr xa))
        else (setq $post-ass-set (nconc $post-ass-set (ncons xa))))))

(defun has-acop (t1) (sloop for op in (all-ops t1) thereis (ac-op-p op)))

(defun flatten (op args)
  ;  Simplifies ARGS for associativity and commutativity of the operator OP.
  (sloop for term in args append
     (cond ((null term) term)
           ((variablep term) (ncons term))
           ((equal op (op-of term)) (flatten op (args-of term)))
           (t (ncons term)))))

(defun elimcom (argsx argsy)
  (sloop
    for x in argsx
	if
	(sloop
	  for terms on argsy
	  as y = (car terms)
	  if (ac-equal y x)
	  return (prog1 nil (setq argsy (nconc new-argsy (cdr terms))))
	  else collect y into new-argsy
	  finally (return t))
	collect x into new-argsx
	finally(return (list new-argsx argsy))))

(defun multi-com (args)
  (sloop for term in args
	if (and (variablep term)
		(sloop for l in vars-argsx
		      if (equal (car l) term)
			return (rplacd l (1+ (cdr l)))
		      finally (return nil)))
	  do nil
	else if (and (nonvarp term)
		     (sloop for l in non-vars-argsx
			   if (equal (car l) term)
			     return (rplacd l (1+ (cdr l)))
			   finally (return nil)))
	       do nil
	else
	  if (variablep term) collect (cons term 1) into vars-argsx
	else collect (cons term 1) into non-vars-argsx 
	finally (return (cons vars-argsx non-vars-argsx))))

;      (return (let ((l1 (split-alist vars-argsx))
;		    (l2 (split-alist non-vars-argsx)))
;		(list (car l1) (car l2) (nconc (cadr l1) (cadr l2)))))))

(defun ac-member (t1 list)
  (sloop for y on list if (ac-equal(car y) t1) return y finally (return nil)))

(defun wash-def-rules (ops)
  ; "ops" are operators of which the definition rules
  ; containing a newly commutative operators. 
  ; If their definition can be simplified, then save their old
  ; definition structure (or cover-set) in $non-comm-cover-sets
  ; and delete them from $cover-sets.
  (sloop with del for op in ops do
    (setq del nil)
    (sloop with result with rul3
	  for rul1 in (cdr (assoc op $op_rules)) 
	  if (eq (car (rule-source rul1)) 'def) do
      (setq rul3 (flatten-eqn rul1))
      (if* (sloop for rul2 in result thereis (similar-eqn rul3 rul2))
	  then (clean-rule rul1) (setq del t)
	  else (replace rul1 rul3) (push rul3 result)))
    (if* del then
	(setq del (assoc op $cover-sets))
	(push del $non-comm-cover-sets ))))

;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

;#+franz (include "datamacs.l")
;#-franz (in-package "USER")


#+franz
(declare (special $combination $subs2 $last-soln
		  $symmetry-terms $good-symmetry-terms $sym-arg-positions))

(setq $combination nil $subs2 nil $sym-arg-positions nil 
      $good-symmetry-terms nil
      )

; This is the code for solving diophontine equations in order
; to find a basis which is used in ac unification.

; all-ones is the special case when ai's and bj's are all
; ones in the diophontine eqn. So only special solutions are
; needed. [these have only 2 1's and rest 0's]

(defun all-ones (vargsx nargsx vargsy nargsy op top)
  (let* ((l2 (length vargsx)) (l1 (length nargsx)) (l (+ l1 l2))
	(m1 (length vargsy)) (m2 (length nargsy)) (m (+ m1 m2))
	(numargs (+ l m))
	(basis (make-array (list (* l m) numargs)))
	(Q (make-array (* l m)))
	(sigma (make-array (* l m)))
	(args (make-array  numargs))
	(row 0)
	character-indexes temp)

    (setq top (and top $prime-acu))
    (setq character-indexes 
	  (dio-initialize basis (setq numargs (1- numargs))
			  args (nconc nargsx vargsx vargsy nargsy)))

    (sloop for xi from 0 to (1- l) do
      (sloop for yi downfrom numargs to l do
	(if* (< xi l1)
	    then (if* (< (- yi l) m1)		;
		     then
		     (if* (occurs-in (aref args yi) (aref args xi))
			 then ()
			 else
			 (aset (aref args xi) Q row)
			 (aset nil sigma row)
			 (aset  1 basis row xi)
			 (aset 1 basis row yi)
			 (setq row (1+ row)))
		     elseif (plausible (aref args xi) (aref args yi))
		     then
		     (setq temp (list xi yi))
		     (aset temp sigma row)
		     (aset (aref args xi) Q row)
		     (aset 1 basis row xi)
		     (aset 1 basis row yi)
		     (setq row (1+ row)))
	    else (if* (< (- yi l) m1)
		     then (if* (or (neq 'xex1 (aref args xi))
				  (neq 'xex2 (aref args yi))) then
			      (aset (make-new-variable) Q row)
			      (aset nil sigma row)
			      (aset 1 basis row xi)
			      (aset 1 basis row yi)
			      (setq row (1+ row)))
		     else (if* (occurs-in (aref args xi) (aref args yi))
			      then ()
			      else
			      (aset (aref args yi) Q row)
			      (aset nil sigma row)
			      (aset 1 basis row xi)
			      (aset 1 basis row yi)
			      (setq row (1+ row)))))))
	(if* (> row 0) then
	    (get-solutions character-indexes basis Q sigma args numargs
			   (if* (> $idem 2) 
			       (con-nums 0 numargs) 
			       (sloop for i from 0 to numargs
				     if (nonvarp (aref args i)) collect i))
			   (1- row) op
			   top))))
		    
(defun dio-initialize (basis numargs args arg-elements)
  (setq $last-soln nil)
  (fillarray basis '(0))
  (sloop for ind from 0 as arg in arg-elements
	do (aset arg args ind))
  (setq $sym-arg-positions (if* $symmetry-terms (sym-arg-positions numargs args)))
  (if* $sym-arg-positions then
      (setq $good-symmetry-terms 
	    (sloop for l1 in $symmetry-terms 
		  if (sloop for xb in l1 always (assoc xb $sym-arg-positions))
		    collect l1))
      (sloop with sym-indexes = (sloop for xa in $sym-arg-positions collect (cdr xa))
	    for i from 0 to numargs
	    if (not (memq i sym-indexes)) collect i)
      else
      (setq $good-symmetry-terms nil)))

(defun full-dio (vargsx nargsx vargsy nargsy vecx vecy op top)
  (let* ((temp (find-basis-vectors vecx vecy))
	 (tmp (length temp))
	 (arg-elements (nconc vargsx nargsx nargsy vargsy))
	 (numargs (length arg-elements))
	 (args (make-array numargs))
	 (basis (make-array (list tmp numargs)))
	 (row 0)
	 (Q (make-array tmp))
	 (sigma (make-array tmp))
	 character-indexes)

    (setq top (and top $prime-acu))
    (setq character-indexes 
	  (dio-initialize basis (setq numargs (1- numargs)) args arg-elements))

    (sloop for soln in temp do
      (if* (sloop for i from 0  
		as j in soln thereis (and (> j 1) (nonvarp (aref args i))))
	  then ()
	  elseif (setq tmp (sloop for i from 0
				 as j in soln
				 if (and (> j 0) (nonvarp (aref args i)))
				   collect i))
	  then (if* (sloop for i from 0 as j in soln
			 thereis (and (> j 0) (variablep (aref args i))
				      (sloop for k in tmp
					    thereis (occurs-in (aref args i) 
							       (aref args k)))))
		   then ()
		   elseif (and $sym-arg-positions
			       (sloop for l1 in $good-symmetry-terms 
				     thereis (loose-sym-sequence tmp l1)))
		   then ()
		   else
		   (if* (null (cdr tmp)) then
		       (sloop for i from 0 as j in soln do
			 (aset j basis row i))
		       (aset (aref args (car tmp)) Q row)
		       (setq row (1+ row))
		       elseif (all-plaus args tmp) then
		       (sloop for i from 0 as j in soln do
			 (aset j basis row i))
		       (aset (aref args (car tmp)) Q row)
		       (aset tmp sigma row)
		       (setq row (1+ row))))
	  elseif (sloop for s in soln as i from 0 
		       always (or (= 0 s) (memq (aref args i) '(xex1 xex2))))
	  then ()
	  else
	  (sloop for i from 0 as j in soln do (aset j basis row i))
	  (aset (make-new-variable) Q row)
	  (setq row (1+ row))))

    (if* (> row 0) then
	(get-solutions character-indexes basis Q sigma args numargs 
		       (if* (> $idem 2) 
			   (con-nums 0 numargs) 
			   (sloop for i from 0 to numargs
				 if (nonvarp (aref args i)) collect i))
		       (1- row) op top))))

(defun loose-sym-sequence (nv-cols sym-terms)
  (and (cddr sym-terms)
       (not (condense-sequence nv-cols (sloop for xa in sym-terms 
				     collect (cdr (assoc xa $sym-arg-positions)))))))

(defun condense-sequence (s1 s2)
  ; Suppose a, b and c are any three successive elements of s2.
  ; Return t iff b is in s1 whenever both a and c in s1.
  ; Note that s1 and s2 are both in increasing order.
  (sloop with flag = 0
	for xa in s2 do
    (sloop while (and s1 (< (car s1) xa)) do (pop s1))
    (if* s1 
	(if* (equal xa (car s1)) then
	    (if* (= flag 2) 
		then (return nil)
		else (setq flag 1) (pop s1))
	    elseif (= flag 1) then (setq flag 2))
	(return t))
	finally (return t)))

(defun find-basis-vectors (vecx vecy)
  (if* (sloop for xa in vecx always (= xa 1))
      then (half-ones (length vecx) vecy)
      elseif (sloop for xa in vecy always (= xa 1))
      then (half-ones (length vecy) vecx t)
      else (general-basis-vectors vecx vecy)))

(defun half-ones (m vec &optional first-half)
  (sloop with lvec = (length vec)
	with half
	for i from 1 
	as y in vec 
	if (> y 0)
	  nconc (progn
		  (setq half (sloop for j from 1 to lvec 
				   collect (if* (= j i) 1 0)))
		  (sloop for xa in (combinate m y)
			collect (if* first-half (append half xa) (append xa half))))))

(defun general-basis-vectors (vecx vecy)
  (let*
    ((n (length vecx))
     (m (length vecy))
     (n1 (1+ n)) 
     (m1 (1+ m))
     (a (make-array  n1)) 
     (b (make-array  m1))
     (x (make-array  n1)) 
     (y (make-array  m1))
     (sumx (make-array  n1))
     (sumy (make-array  m1))
     (ymax (make-array  `(,n1 ,m1)))
     (d (make-array `(,n1 ,m1))) 
     (e (make-array  `(,n1 ,m1)))
     validsolns amax bmax newvec)

    (fillarray a (cons 0 vecx))
    (fillarray b (cons 0 vecy))
    (fillarray x '(0))
    (fillarray y '(0))
    (fillarray sumx '(0))
    (fillarray sumy '(0))
    (setq amax (sloop for i from 1 to n maximize (aref a  i))
	  bmax (sloop for i from 1 to m maximize (aref b i)))
    (sloop for j from 1 to m
	  do (sloop for i from 1 to n
		   do (let((gcd (gcd (aref a i) (aref b j))))
			(aset (quotient (aref b j) gcd) d i j)
			(aset (quotient (aref a i) gcd) e i j))))
    (sloop for incremented =
	      (sloop for k downfrom n to 1 
		    do (aset (1+ (aref x k)) x k)
		    if (or (> (aref x k) bmax)
			   (< (sumymax k a b x sumx d e ymax amax m) (aref sumx k)))
		      do (aset 0 x k)
		    else do
			   (sloop with sumxk = (aref sumx k)
				 for i from (1+ k) to n do 
			     (progn
			       (aset sumxk sumx i)
			       (sloop for j from 1 to m
				     do (aset (aref ymax k j) ymax i j))))
			 and return t
		    finally (return nil))
	  if incremented 
	    do (sloop with quotient = nil
		     for k = m then k
		     if (= k 0) return (fillarray sumy '(0))
		     else if (= k m)
			    if (nequal 0 (remainder (- (aref sumx n) 
						    (aref sumy (sub1 k))) (aref b k)))
			      do (progn (aset 0 y m) (setq k (sub1 k)))
		     else do (setq quotient (quotient (- (aref sumx n) 
							 (aref sumy (sub1 k))) 
						      (aref b k)))
			  and do (progn
				   (when (and (<= quotient (or (aref ymax n m) amax)) 
					      (aset  quotient y m)
					      (setq newvec (append (cdr (listarray x)) 
								   (cdr (listarray y))))
					      (sloop for v in validsolns
						    always (not (less-vector v newvec))))
				     (push newvec validsolns))
				   (aset 0 y m) (setq k (sub1 k)))
		     else do (aset (1+ (aref y k)) y k)
			  and if (or (> (aref y k) (or (aref ymax n k) amax))
				     (> (aset (+ (* (aref b k) (aref y k)) 
						 (aref sumy (sub1 k))) sumy k)
					(aref sumx n)))
				do (progn (aset 0 y k) (setq k (sub1 k)))
		     else do
			    (progn (sloop for i from (1+ k) to m 
					 do (aset (aref sumy k) sumy i)) (setq k m)))
	  else return (nconc validsolns (get-lcm-solns d e n m)))))

(defun get-lcm-solns (d e n m)
  (sloop for i from 1 to n
	nconc (sloop for j from 1 to m
		    collect
		      (nconc (sloop for x from 1 to n 
				   if (= x i) collect (aref d i j) 
				   else collect 0)
			     (sloop for y from 1 to m
				   if (= y j) collect (aref e i j) 
				   else collect 0)))))

(defun sumymax (k a b x sumx d e ymax amax m)
  (aset (+(aref sumx (sub1 k)) (*(aref a  k) (aref x k))) sumx k)
  (sloop
    for j from 1 to m
   
    if (null (aref ymax (sub1 k) j))
    if (<= (aref d k j) (aref x k))
    do (aset (sub1(aref e k j)) ymax  k j)
    else do  (aset nil  ymax k j)
    else  if (<= (aref d k j) (aref x k))
    do (aset (min(sub1 (aref e k j)) (aref ymax (sub1 k) j)) ymax k j)
    else do (aset (aref ymax (sub1 k) j)  ymax k j))
  (sloop
    for j from 1 to m
    sum (*(if* (null(aref ymax k j)) amax (aref ymax k j)) (aref b j))))


;;; Transfer solutions for diophantine equation into substitutions. 

(defun get-solutions (character-indexes basis Q sigma args numargs nvcols nrow op top)
  (let ((no-0-basis (make-array (1+ nrow))))
    (sloop for i from 0 to nrow do
      (aset (sloop for j from 0 to numargs
		  if (> (aref basis i j) 0) collect j) 
	    no-0-basis i))
    (take-out nil 
	      (con-nums 0 nrow) 
	      no-0-basis
	      (con-nums 0 numargs)
	      nvcols
	      (list character-indexes basis numargs args Q sigma op)
	      top)))

(defun take-out (soln rest no-0-basis null-cols nvcols info top)
  (if* rest then
      (let ((new-null-cols null-cols) bad i)
	(setq i (car rest))
	(sloop for xa in (aref no-0-basis i)
	      do (if* (memq xa null-cols)
		     then (setq new-null-cols (remq xa new-null-cols 1))
		     elseif (memq xa nvcols)
		     then (return (setq bad t))))
	(if* bad 
	    (take-out soln (cdr rest) no-0-basis null-cols nvcols info top)
	    (nconc
	      (take-out soln (cdr rest) no-0-basis null-cols nvcols info top)
	      (if* new-null-cols 
		  (take-out (cons i soln) (cdr rest) no-0-basis
			    new-null-cols nvcols info top)
		  (if* top
		      (one-composition (cons i soln) info t)
		      (nconc 
			(one-composition (cons i soln) info nil)
			(take-out (cons i soln) (cdr rest) no-0-basis
				  nil nvcols info nil)))))))))

(defun one-composition (soln info top)
  ; "soln" is a complete composition of the solutions in the basis.
  ; Try to return a set of AC-unifiers upon this composition.
  (if* (and $sym-arg-positions
	   (not (symmetry-non-deletable
		  soln (car info) (cadr info)))) then
      (if* (= $trace_flag 3) then 
	  (terpri) (princ "Deleting a unifier by symmetry relation.") 
	  (terpri))
      (inc $symmetry-dels)
      nil
      elseif (and top $last-soln (is-subseq-list $last-soln soln))
      then nil
      else
      (if* (< $idem 3) (setq $last-soln soln))
      (add-soln soln (cdr info))))
;		       (nconc (add-soln soln (cdr info))
;			      (take-out soln (cdr rest) no-0-basis 
;					new-null-cols nvcols info))))

(defun add-soln (soln info)
  (let ((basis (car info))
	(numargs (cadr info))
	(args (caddr info))
	(Q (cadddr info))
	(sigma (nth 4 info))
	(op (nth 5 info))
	subs fail l1)
    (sloop for col from 0 to numargs do
      (if* (variablep (aref args col)) then
	  (sloop	with flag = nil
		for s in soln
		if (> (setq l1 (aref basis s col)) 0)
		  append (ntimes l1 (aref Q s)) into sub		
		  and if (not (variablep (aref Q s))) do (setq flag t)
		finally (if* sub then
			    (setq sub (if* (cdr sub) (cons op sub) (car sub)))
			    (if* subs 
				(if* (setq subs 
					  (comp1 subs
						 (ncons (cons (aref args col) sub))))
				    () 
				    (setq fail t))
				(setq subs (ncons (cons (aref args col) sub)))))))
      (if* fail then (return nil)))
    (if* fail then nil
	else 
	(setq subs (ncons subs))
	(sloop for s in soln 
	      if (null (aref sigma s)) do nil
	      else if (setq subs (sloop for sub in subs 
				       append (res1 sub (aref sigma s) args)))
		     do nil
	      else return nil)
	subs)))

(defun combinate (m n &aux res)
  ; Return all m-tuples of non-negative integers such that the sum of the integers
  ; in each tuple is equal to n.
  ; If m = 1 or n = 1, this computation is easy, do it without saving.
  ; Otherwise, check if the result has been stored. 
  ; If not, compute it, save it and return it.
  (if* (= m 1) 
      then (ncons (ncons n))
      elseif (= n 1)
      then (sloop for xa from 1 to m 
		 collect (sloop for xb from 1 to m 
			       collect (if* (= xa xb) 1 0)))
      elseif (and (setq res (assoc n $combination))
		  (setq res (assoc m (cdr res))))
      then (cdr res)
      else 
      (setq res (combinate2 m n))
      (add-associate-list n (cons m res) $combination)
      res))

(defun combinate2 (m n)
  ; Return all m-tuples of non-negative integers such that the sum of the integers
  ; in each tuple is equal to n.
  ; Assume n > 1 and m > 1.
  (cons (cons n (sloop for i from 2 to m collect 0))
	(sloop with m1 = (sub1 m)
	      for i from 1 to n
	      as j = (- n i) 
	      nconc (sloop for xa in (combinate m1 i) collect (cons j xa)))))


(defun dio (vecx vecy &optional (num 1))
  (let* ((time 0) temp tmp)
    (setq temp (add-time time
			 (sloop for i from 1 to (sub1 num) do
			   (find-basis-vectors vecx vecy)
			       finally (return (find-basis-vectors vecx vecy))))
	  tmp (length temp))
    (mark time "Time used.")
    (mark tmp "Number of basis solutions.")
    (if* (ok-to-continue "Display them ? ")
	(sloop for xa in temp do
	  (terpri) (princ xa)
	      finally (terpri)))))

(defun dio2 (vecx vecy &optional (num 1))
  (let* ((time 0) temp tmp)
    (setq temp (add-time time 
			 (sloop for i from 1 to (sub1 num) do
			   (general-basis-vectors vecx vecy)
			   finally (return (general-basis-vectors vecx vecy))))
	  tmp (length temp))
    (mark time "Time used.")
    (mark tmp "Number of basis solutions.")
    (if* (ok-to-continue "Display them ? ")
	(sloop for xa in temp do
	  (terpri) (princ xa)
	      finally (terpri)))))

(defun sym-arg-positions (num args)
  (sloop for i from 0 to num
	nconc
	  (sloop with xa = (aref args i)
		for l1 in $symmetry-terms 
		append (sloop for xb in l1 
			     if (equal xa xb) collect (cons xb i)))))

(defun symmetry-non-deletable (soln character-indexes basis)
  (sloop for l1 in $good-symmetry-terms 
	always (non-decreasing-seq 
		     (sloop for xb in l1 
			   collect (cardinality soln basis (variablep xb)
						(cdr (assoc xb $sym-arg-positions))
						character-indexes)))))

(defun cardinality (soln basis isvar col character-indexes)
  (if* isvar 
      (sloop for j in soln sum (aref basis j col))
      (sloop for j in soln 
	    if (> (aref basis j col) 0)
	      return (sloop with sum = 0 
			   for i in character-indexes
			   do (setq sum (+ (times sum 10) (aref basis j i)))
			   finally (return sum)))))

