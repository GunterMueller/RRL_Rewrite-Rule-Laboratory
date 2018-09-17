;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

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

    (loop for xi from 0 to (1- l) do
      (loop for yi from numargs downto l do
	(if (< xi l1)
	    then (if (< (- yi l) m1)		;
		     then
		     (if (occurs-in (aref args yi) (aref args xi))
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
	    else (if (< (- yi l) m1)
		     then (if (or (neq 'xex1 (aref args xi))
				  (neq 'xex2 (aref args yi))) then
			      (aset (make-new-variable) Q row)
			      (aset nil sigma row)
			      (aset 1 basis row xi)
			      (aset 1 basis row yi)
			      (setq row (1+ row)))
		     else (if (occurs-in (aref args xi) (aref args yi))
			      then ()
			      else
			      (aset (aref args yi) Q row)
			      (aset nil sigma row)
			      (aset 1 basis row xi)
			      (aset 1 basis row yi)
			      (setq row (1+ row)))))))
	(if (> row 0) then
	    (get-solutions character-indexes basis Q sigma args numargs
			   (if (> $idem 2) 
			       (con-nums 0 numargs) 
			       (loop for i from 0 to numargs
				     if (nonvarp (aref args i)) collect i))
			   (1- row) op
			   top))))
		    
(defun dio-initialize (basis numargs args arg-elements)
  (setq $last-soln nil)
  (fillarray basis '(0))
  (loop for ind from 0 as arg in arg-elements
	do (aset arg args ind))
  (setq $sym-arg-positions (if $symmetry-terms (sym-arg-positions numargs args)))
  (if $sym-arg-positions then
      (setq $good-symmetry-terms 
	    (loop for l1 in $symmetry-terms 
		  if (loop for xb in l1 always (assoc xb $sym-arg-positions))
		    collect l1))
      (loop with sym-indexes = (loop for xa in $sym-arg-positions collect (cdr xa))
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

    (loop for soln in temp do
      (if (loop for i from 0  
		as j in soln thereis (and (> j 1) (nonvarp (aref args i))))
	  then ()
	  elseif (setq tmp (loop for i from 0
				 as j in soln
				 if (and (> j 0) (nonvarp (aref args i)))
				   collect i))
	  then (if (loop for i from 0 as j in soln
			 thereis (and (> j 0) (variablep (aref args i))
				      (loop for k in tmp
					    thereis (occurs-in (aref args i) 
							       (aref args k)))))
		   then ()
		   elseif (and $sym-arg-positions
			       (loop for l1 in $good-symmetry-terms 
				     thereis (loose-sym-sequence tmp l1)))
		   then ()
		   else
		   (if (null (cdr tmp)) then
		       (loop for i from 0 as j in soln do
			 (aset j basis row i))
		       (aset (aref args (car tmp)) Q row)
		       (setq row (1+ row))
		       elseif (all-plaus args tmp) then
		       (loop for i from 0 as j in soln do
			 (aset j basis row i))
		       (aset (aref args (car tmp)) Q row)
		       (aset tmp sigma row)
		       (setq row (add1 row))))
	  elseif (loop for s in soln as i from 0 
		       always (or (eq 0 s) (memq (aref args i) '(xex1 xex2))))
	  then ()
	  else
	  (loop for i from 0 as j in soln do (aset j basis row i))
	  (aset (make-new-variable) Q row)
	  (setq row (1+ row))))

    (if (> row 0) then
	(get-solutions character-indexes basis Q sigma args numargs 
		       (if (> $idem 2) 
			   (con-nums 0 numargs) 
			   (loop for i from 0 to numargs
				 if (nonvarp (aref args i)) collect i))
		       (1- row) op top))))

(defun loose-sym-sequence (nv-cols sym-terms)
  (and (cddr sym-terms)
       (not (condense-sequence nv-cols (loop for xa in sym-terms 
				     collect (cdr (assoc xa $sym-arg-positions)))))))

(defun condense-sequence (s1 s2)
  ; Suppose a, b and c are any three successive elements of s2.
  ; Return t iff b is in s1 whenever both a and c in s1.
  ; Note that s1 and s2 are both in increasing order.
  (loop with flag = 0
	for xa in s2 do
    (loop while (and s1 (< (car s1) xa)) do (pop s1))
    (if s1 
	(if (eq xa (car s1)) then
	    (if (= flag 2) 
		then (return nil)
		else (setq flag 1) (pop s1))
	    elseif (eq flag 1) then (setq flag 2))
	(return t))
	finally (return t)))

(defun find-basis-vectors (vecx vecy)
  (if (loop for xa in vecx always (eq xa 1))
      then (half-ones (length vecx) vecy)
      elseif (loop for xa in vecy always (eq xa 1))
      then (half-ones (length vecy) vecx t)
      else (general-basis-vectors vecx vecy)))

(defun half-ones (m vec &optional first-half)
  (loop with lvec = (length vec)
	with half
	for i from 1 
	as y in vec 
	if (> y 0)
	  nconc (progn
		  (setq half (loop for j from 1 to lvec 
				   collect (if (= j i) 1 0)))
		  (loop for xa in (combinate m y)
			collect (if first-half (append half xa) (append xa half))))))

(defun general-basis-vectors (vecx vecy)
  (let*
    ((n (length vecx))
     (m (length vecy))
     (n1 (add1 n)) 
     (m1 (add1 m))
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
    (setq amax (loop for i from 1 to n maximize (aref a  i))
	  bmax (loop for i from 1 to m maximize (aref b i)))
    (loop for j from 1 to m
	  do (loop for i from 1 to n
		   do (let((gcd (gcd (aref a i) (aref b j))))
			(aset (quotient (aref b j) gcd) d i j)
			(aset (quotient (aref a i) gcd) e i j))))
    (loop for incremented =
	      (loop for k from n downto 1 
		    do (aset (add1 (aref x k)) x k)
		    if (or (> (aref x k) bmax)
			   (< (sumymax k a b x sumx d e ymax amax m) (aref sumx k)))
		      do (aset 0 x k)
		    else do
			   (loop with sumxk = (aref sumx k)
				 for i from (add1 k) to n do 
			     (progn
			       (aset sumxk sumx i)
			       (loop for j from 1 to m
				     do (aset (aref ymax k j) ymax i j))))
			 and return t
		    finally (return nil))
	  if incremented 
	    do (loop with quotient = nil
		     for k = m then k
		     if (eq k 0) return (fillarray sumy '(0))
		     else if (eq k m)
			    if (neq 0 (remainder (- (aref sumx n) 
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
					      (loop for v in validsolns
						    always (not (less-vector v newvec))))
				     (push newvec validsolns))
				   (aset 0 y m) (setq k (sub1 k)))
		     else do (aset (add1 (aref y k)) y k)
			  and if (or (> (aref y k) (or (aref ymax n k) amax))
				     (> (aset (+ (* (aref b k) (aref y k)) 
						 (aref sumy (sub1 k))) sumy k)
					(aref sumx n)))
				do (progn (aset 0 y k) (setq k (sub1 k)))
		     else do
			    (progn (loop for i from (add1 k) to m 
					 do (aset (aref sumy k) sumy i)) (setq k m)))
	  else return (nconc validsolns (get-lcm-solns d e n m)))))

(defun get-lcm-solns (d e n m)
  (loop for i from 1 to n
	nconc (loop for j from 1 to m
		    collect
		      (nconc (loop for x from 1 to n 
				   if (eq x i) collect (aref d i j) 
				   else collect 0)
			     (loop for y from 1 to m
				   if (eq y j) collect (aref e i j) 
				   else collect 0)))))

(defun sumymax (k a b x sumx d e ymax amax m)
  (aset (+(aref sumx (sub1 k)) (*(aref a  k) (aref x k))) sumx k)
  (loop
    for j from 1 to m
   
    if (null (aref ymax (sub1 k) j))
    if (<= (aref d k j) (aref x k))
    do (aset (sub1(aref e k j)) ymax  k j)
    else do  (aset nil  ymax k j)
    else  if (<= (aref d k j) (aref x k))
    do (aset (min(sub1 (aref e k j)) (aref ymax (sub1 k) j)) ymax k j)
    else do (aset (aref ymax (sub1 k) j)  ymax k j))
  (loop
    for j from 1 to m
    sum (*(if (null(aref ymax k j)) amax (aref ymax k j)) (aref b j))))


;;; Transfer solutions for diophantine equation into substitutions. 

(defun get-solutions (character-indexes basis Q sigma args numargs nvcols nrow op top)
  (let ((no-0-basis (make-array (1+ nrow))))
    (loop for i from 0 to nrow do
      (aset (loop for j from 0 to numargs
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
  (if rest then
      (let ((new-null-cols null-cols) bad i)
	(setq i (car rest))
	(loop for xa in (aref no-0-basis i)
	      do (if (memq xa null-cols)
		     then (setq new-null-cols (remq xa new-null-cols 1))
		     elseif (memq xa nvcols)
		     then (return (setq bad t))))
	(if bad 
	    (take-out soln (cdr rest) no-0-basis null-cols nvcols info top)
	    (nconc
	      (take-out soln (cdr rest) no-0-basis null-cols nvcols info top)
	      (if new-null-cols 
		  (take-out (cons i soln) (cdr rest) no-0-basis
			    new-null-cols nvcols info top)
		  (if top
		      (one-composition (cons i soln) info t)
		      (nconc 
			(one-composition (cons i soln) info nil)
			(take-out (cons i soln) (cdr rest) no-0-basis
				  nil nvcols info nil)))))))))

(defun one-composition (soln info top)
  ; "soln" is a complete composition of the solutions in the basis.
  ; Try to return a set of AC-unifiers upon this composition.
  (if (and $sym-arg-positions
	   (not (symmetry-non-deletable
		  soln (car info) (cadr info)))) then
      (if (= $trace_flag 3) then 
	  (terpri) (princ "Deleting a unifier by symmetry relation.") 
	  (terpri))
      (inc $symmetry-dels)
      nil
      elseif (and top $last-soln (is-subseq-list $last-soln soln))
      then nil
      else
      (if (< $idem 3) (setq $last-soln soln))
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
    (loop for col from 0 to numargs do
      (if (variablep (aref args col)) then
	  (loop	with flag = nil
		for s in soln
		if (> (setq l1 (aref basis s col)) 0)
		  append (ntimes l1 (aref Q s)) into sub		
		  and if (not (variablep (aref Q s))) do (setq flag t)
		finally (if sub then
			    (setq sub (if (cdr sub) (cons op sub) (car sub)))
			    (if subs 
				(if (setq subs 
					  (comp1 subs
						 (ncons (cons (aref args col) sub))))
				    () 
				    (setq fail t))
				(setq subs (ncons (cons (aref args col) sub)))))))
      (if fail then (return nil)))
    (if fail then nil
	else 
	(setq subs (ncons subs))
	(loop for s in soln 
	      if (null (aref sigma s)) do nil
	      else if (setq subs (loop for sub in subs 
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
  (if (= m 1) 
      then (ncons (ncons n))
      elseif (= n 1)
      then (loop for xa from 1 to m 
		 collect (loop for xb from 1 to m 
			       collect (if (= xa xb) 1 0)))
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
  (cons (cons n (loop for i from 2 to m collect 0))
	(loop with m1 = (sub1 m)
	      for i from 1 to n
	      as j = (- n i) 
	      nconc (loop for xa in (combinate m1 i) collect (cons j xa)))))


(defun dio (vecx vecy &optional (num 1))
  (let* ((time 0) temp tmp)
    (setq temp (add-time time
			 (loop for i from 1 to (sub1 num) do
			   (find-basis-vectors vecx vecy)
			       finally (return (find-basis-vectors vecx vecy))))
	  tmp (length temp))
    (mark time "Time used.")
    (mark tmp "Number of basis solutions.")
    (if (ok-to-continue "Display them ? ")
	(loop for xa in temp do
	  (terpri) (princ xa)
	      finally (terpri)))))

(defun dio2 (vecx vecy &optional (num 1))
  (let* ((time 0) temp tmp)
    (setq temp (add-time time 
			 (loop for i from 1 to (sub1 num) do
			   (general-basis-vectors vecx vecy)
			   finally (return (general-basis-vectors vecx vecy))))
	  tmp (length temp))
    (mark time "Time used.")
    (mark tmp "Number of basis solutions.")
    (if (ok-to-continue "Display them ? ")
	(loop for xa in temp do
	  (terpri) (princ xa)
	      finally (terpri)))))

(defun sym-arg-positions (num args)
  (loop for i from 0 to num
	nconc
	  (loop with xa = (aref args i)
		for l1 in $symmetry-terms 
		append (loop for xb in l1 
			     if (equal xa xb) collect (cons xb i)))))

(defun symmetry-non-deletable (soln character-indexes basis)
  (loop for l1 in $good-symmetry-terms 
	always (non-decreasing-seq 
		     (loop for xb in l1 
			   collect (cardinality soln basis (variablep xb)
						(cdr (assoc xb $sym-arg-positions))
						character-indexes)))))

(defun cardinality (soln basis isvar col character-indexes)
  (if isvar 
      (loop for j in soln sum (aref basis j col))
      (loop for j in soln 
	    if (> (aref basis j col) 0)
	      return (loop with sum = 0 
			   for i in character-indexes
			   do (setq sum (add (times sum 10) (aref basis j i)))
			   finally (return sum)))))

