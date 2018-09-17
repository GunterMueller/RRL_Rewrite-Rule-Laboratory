(in-package "USER")

;; There is a bug when (full-dio '(-88 -1) nil (-89 -90) nil (1 7) (1 7) 1 T) 
;; is called.

;;;; Copyright 1988 The University of Iowa
;;; Created by Hantao Zhang, 3/3/89.

;; This file contains huet's diophatine basis algorithm, with some improvements.
;; Results with timing can be obtained by (huet vecx vecy).
;; If one side of the equation is all 1's, then
;;  results with timing can be obtained by (dio vecx vecy).
;; A list of solutions can be obtained by (find-basis-vectors vecx vecy), which is used
;; in AC unification algorithm.

(defun init-ac-arrays ()
  (unless $init-ac-arrays
    (setq $init-ac-arrays t)
    (def-array2 $a *dim3* 'fixnum)
    (def-array2 $b *dim3* 'fixnum)
    (def-array2 $x *dim3* 'fixnum)
    (def-array2 $y *dim3* 'fixnum)
    (def-array2 $maxd *dim3* 'fixnum)
    (def-array2 $maxe *dim3* 'fixnum)
    (def-array2 $sumx *dim3* 'fixnum)
    (def-array2 $sumy *dim3* 'fixnum)
    (def-array2 $ymax *dim4*)
    (def-array2 $d *dim4* 'fixnum)
    (def-array2 $e *dim4* 'fixnum)
    (def-array2 $basis (list *dim1* *dim2*) 'fixnum)
    (def-array2 $no-0-basis *dim1*)
    (def-array2 $sigma *dim1*)
    (def-array2 $Q *dim1*)
    (def-array2 $args *dim2*)
    ))

(defun dio (vecx vecy &optional print (num 1))
  (let* (time basis number)
    (start-timer time)
    (setq basis (sloop for i from 1 to (sub1 num) do
		       (find-basis-vectors vecx vecy)
		       finally (return (find-basis-vectors vecx vecy)))
	  time (run-time time)
	  number (length basis))
    (mark time "Time used.")
    (mark number "Number of basis solutions.")
    (when print
	(sloop for xa in basis do
	      (terpri) (princ xa)
	      finally (terpri)))))

(defun huet (vecx vecy &optional print (num 1))
  (let* (time basis number)
    (start-timer time)
    (setq basis (sloop for i from 1 to (sub1 num) do
		       (general-basis-vectors vecx vecy)
		       finally (return (general-basis-vectors vecx vecy)))
	  time (run-time time)
	  number (length basis))
    (mark time "Time used.")
    (mark number "Number of basis solutions.")
    (when print
	(sloop for xa in basis do
	      (terpri) (princ xa)
	      finally (terpri)))))

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
  (cons (cons n (sloop for i from 2 to m collect 0))
	(sloop with m1 = (sub1 m)
	      for i from 1 to n
	      as j = (- n i) 
	      nconc (sloop for xa in (combinate m1 i) collect (cons j xa)))))

(defun find-basis-vectors (vecx vecy)
  ;;; Basis generation starts here ......
  (if* (sloop for xa in vecx always (eq xa 1))
      then (half-ones (length vecx) vecy)
      elseif (sloop for xa in vecy always (eq xa 1))
      then (half-ones (length vecy) vecx t)
      else (general-basis-vectors vecx vecy)))

(defun half-ones (m vec &optional first-half)
  ;;; Speed up on All-one coefficients.
  (sloop with lvec = (length vec)
	 with half
	for i from 1 
	as y in vec 
	if (> y 0)
	  nconc (progn
		  (setq half (sloop for j from 1 to lvec 
				   collect (if (= j i) 1 0)))
		  (sloop for xa in (combinate m y)
			 collect (if first-half
				     (append half xa)
				     (append xa half))))))

(defun get-lcm-solns (n m)
  (sloop for i from 1 to n nconc
	 (sloop for j from 1 to m collect
		(nconc (sloop for x from 1 to n collect
			      (if (eq x i) (aref $d i j) 0))
		       (sloop for y from 1 to m collect
			      (if (eq y j) (aref $e i j) 0))))))

(defmacro init-basis-array ()
  `(let ()
    (fillarray $a (cons 0 vecx))
    (fillarray $b (cons 0 vecy))
    (fill $x 0)
    (fill $y 0)
    (fill $maxd 0)
    (fill $maxe 0)
    (fill $sumx 0)
    (fill $sumy 0)
    (fillarray2 $ymax n m nil)		
    (setq amax (sloop with max = -1000
		      for i from 1 to n do
		      (if (> (aref $a i) max) (setq max (aref $a i)))
		      finally (return max))
	  bmax (sloop with max = -1000
		      for i from 1 to m do
		      (if (> (aref $b i) max) (setq max (aref $b i)))
		      finally (return max)))
    (sloop with gcd with dij with eij
	   for j from 1 to m do
	   (sloop for i from 1 to n do
		  (setq gcd (gcd (aref $a i) (aref $b j))
			dij (quotient (aref $b j) gcd)
			eij (quotient (aref $a i) gcd))
		  (asetn dij $d i j)
		  (asetn eij $e i j)
		  (if (> dij (aref $maxd i)) (asetn dij $maxd i))
		  (if (> eij (aref $maxe j)) (asetn eij $maxe j))))

;    (when $deepak
;      (setq $hantao t)
;      (sloop for i from 1 to n do
;	     (asetn (sloop for j from 1 to m sum (aref $d i j)) $maxd i))
;      (sloop for j from 1 to m do
;	     (asetn (sloop for i from 1 to n sum (aref $e i j)) $maxe j)))

;    (when $hantao
;     (if (> bmax (sloop for i from 1 to n sum (aref $maxd i)))
;	  (setq bmax (sloop for i from 1 to n sum (aref $maxd i))))
;      (if (> amax (sloop for i from 1 to m sum (aref $maxe i)))
;	  (setq amax (sloop for i from 1 to m sum (aref $maxe i)))))

;    (princ "The bound of the sum of Xi = ") (princ bmax) (terpri)
;    (princ "The bound of the sum of Yj = ") (princ amax) (terpri)
    ))

(defmacro modify-sumymax ()
  `(sloop for j from 1 to m do
	 (cond ((null (aref $ymax (sub1 k) j))
		(if (<= (aref $d k j) (aref $x k))
		    (aset (sub1 (aref $e k j)) $ymax k j)
		    (aset nil $ymax k j)))
	       ((<= (aref $d k j) (aref $x k))
		(aset (min (sub1 (aref $e k j)) (aref $ymax (sub1 k) j)) $ymax k j))
	       (t (aset (aref $ymax (sub1 k) j) $ymax k j)))))

(defmacro incremented ()
  `(sloop for k downfrom n to 1 do
	  (cond ((eq xsum bmax) 
		 (setq xsum (- xsum (aref $x k)))
		 (asetn 0 $x k))
		;((and $hantao (eq (aref $x k) (aref $maxd k)))
		; (setq xsum (- xsum (aref $x k)))
		; (asetn 0 $x k))
		(t
		 (asetn (1+ (aref $x k)) $x k)
		 (asetn (+ (aref $sumx (sub1 k)) (* (aref $a k) (aref $x k))) $sumx k)
		 (modify-sumymax)
		 (cond ((< (sloop for j from 1 to m sum 
				  (* (or ; (> (aref $ymax k j) -1)
					 (aref $ymax k j)
					 amax)  ;;(if $hantao (aref $maxe j) amax))
				     (aref $b j)))
			   (aref $sumx k))
			(setq xsum (- (1+ xsum) (aref $x k)))
			(asetn 0 $x k))
		       (t (setq xsum (1+ xsum))
			  (sloop with sumxk = (aref $sumx k)
				 for i from (1+ k) to n do 
				 (asetn sumxk $sumx i)
				 (sloop for j from 1 to m
					do (aset (aref $ymax k j) $ymax i j)))
			  (return t)))))
	  finally (return nil)))
 
(defun general-basis-vectors (vecx vecy)
  ;;;  Huet's Basis Generation Algorithm
  (let ((n (length vecx)) (m (length vecy)))
    (if* (not (and (< n *dim3*) (< m *dim3*)))
	then 
	(trace-message 4 "    Ignore a BIG AC unification !!!") 
	(setq $discarded t)
	nil
	elseif (and (= n 1) (= m 1))
	then
	(setq n (car vecx) m (car vecy))
	(let ((g (gcd n m))) (ncons (list (/ m g) (/ n g))))
	else
	(general-basis-vectors-aux vecx vecy n m))))

(defun general-basis-vectors-aux (vecx vecy n m)
  (let (validsolns amax bmax newvec (xsum 0) (ysum 0))
    (init-basis-array)
    (sloop while (incremented) do
	   (sloop with quotient = nil
		  for k = m then k do
		  (if (eq k 0) 
		      (return (fill $sumy 0))
		    (cond ((eq k m)
			   (when (eq 0 (remainder 
					(- (aref $sumx n) (aref $sumy (sub1 k)))
					(aref $b k)))
				 (setq quotient (quotient (- (aref $sumx n) 
							     (aref $sumy (sub1 k))) 
							  (aref $b k)))
				 (when (and (<= (+ quotient ysum) amax)
					    (<= quotient 
						(or ;; (> (aref $ymax n m) -1)
						 (aref $ymax n m)
						 amax
						 ;;(if $hantao (aref $maxe m) amax)
						 )))
				       (progn (asetn quotient $y m) t)
				       (setq newvec (append (cdr (listarray $x n)) 
							    (cdr (listarray $y m))))
				       (if (sloop for v in validsolns
						  always (not (less-vector v newvec)))
					   (push newvec validsolns))))
			   (asetn 0 $y m) (setq k (sub1 k)))
			  (t
			   (cond ((eq ysum amax)
				  (setq ysum (- ysum (aref $y k)))
				  (asetn 0 $y k)
				  (setq k (sub1 k)))
				 ((equal (aref $y k) 
					 (or ; (> (aref $ymax n k) -1)
					  (aref $ymax n k)
					  amax))
				  ;; (if $hantao (aref $maxe k) amax)
				  (setq ysum (- ysum (aref $y k)))
				  (asetn 0 $y k)
				  (setq k (sub1 k)))
				 ((and (progn (asetn (1+ (aref $y k)) $y k) t)
				       (> (asetn (+ (* (aref $b k) (aref $y k)) 
						    (aref $sumy (sub1 k))) 
						 $sumy k)
					  (aref $sumx n)))
				  (setq ysum (- (1+ ysum) (aref $y k)))
				  (asetn 0 $y k)
				  (setq k (sub1 k)))
				 (t
				  (setq ysum (1+ ysum))
				  (sloop for i from (1+ k) to m 
					 do (asetn (aref $sumy k) $sumy i))
				  (setq k m))))))))
    (nconc validsolns (get-lcm-solns n m))
    ))

(defun mark (a &optional b)
  (princ a) (when b (princ " <=== ") (princ b)) (terpri))


;;;;;;;;;;;; merged from acdio.lisp

(defmacro get-array (dim candidate &optional fixnum)
  (if fixnum
      `(if  (or $big-unifier $array-in-use)
	    (make-array ,dim :element-type 'fixnum) 
	    ,candidate)
      `(if  (or $big-unifier $array-in-use)
	    (make-array ,dim) 
	    ,candidate)
      ))

(defmacro dio-initialize (arg-elements)
  `(let ()
     (sloop for ind from 0 for arg in ,arg-elements
	    do (aset arg args ind))
     (setq $last-soln nil
	   top (or (not $idem-superpose) (and top $prime-acu))
	   numargs (1- numargs))
     (fillarray1 sigma (1- tmp) nil)
     (fillarray1 Q (1- tmp) nil)
     (fillarray2 basis (1- tmp) numargs 0)
     ))

(defmacro solution-1-only-columns ()
  `(if (not $idem-superpose)
       (con-nums 0 numargs) 
       (sloop for i from 0 to numargs
	      if (or (nonvarp (aref args i))
		     (memq (aref args i) $top-only-vars))
	      collect i)))

; all-ones is the special case when ai's and bj's are all
; ones in the diophontine eqn. So only special solutions are
; needed. [these have only 2 1's and rest 0's]

(defun all-ones (vargsx nargsx vargsy nargsy op top)
  (let* ((l1 (length nargsx)) 
	 (l (+ l1 (length vargsx)))
	 (m1 (length vargsy)) 
	 (m (+ m1 (length nargsy)))
	 (tmp (* l m))
	 (numargs (+ l m)))
    (setq $big-unifier (or (>= l *dim3*) (>= m *dim3*)))
    (let 
	((basis (get-array (list tmp numargs) $basis 'fixnum))
	 (Q (get-array tmp $Q))
	 (sigma (get-array tmp $sigma))
	 (args (get-array numargs $args))
	 (row 0)
	 )

    (dio-initialize (nconc nargsx vargsx vargsy nargsy))

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
			 (asetn 1 basis row xi)
			 (asetn 1 basis row yi)
			 (setq row (1+ row)))
		     elseif (plausible (aref args xi) (aref args yi))
		     then
		     (aset (list xi yi) sigma row)
		     (aset (aref args xi) Q row)
		     (asetn 1 basis row xi)
		     (asetn 1 basis row yi)
		     (setq row (1+ row)))
	    else (if* (< (- yi l) m1)
		     then (if* (or (neq *xex1* (aref args xi))
				  (neq *xex2* (aref args yi))) then
			      (aset (make-new-variable) Q row)
			      (aset nil sigma row)
			      (asetn 1 basis row xi)
			      (asetn 1 basis row yi)
			      (setq row (1+ row)))
		     else (if* (occurs-in (aref args xi) (aref args yi))
			      then ()
			      else
			      (aset (aref args yi) Q row)
			      (aset nil sigma row)
			      (asetn 1 basis row xi)
			      (asetn 1 basis row yi)
			      (setq row (1+ row)))))))

    (when (> row 0) 
      (get-solutions (symm-initialize numargs args)
		     basis Q sigma args numargs
		     (solution-1-only-columns)
		     (1- row) op
		     top))
    )))

(defun full-dio (vargsx nargsx vargsy nargsy vecx vecy op top)
  (setq $big-unifier (or (>= (length vecx) *dim3*) (>= (length vecy) *dim3*)))
  (let* 
      ((temp (find-basis-vectors vecx vecy))
       (tmp (min (1- *dim1*) (length temp)))
       (arg-elements (nconc vargsx nargsx nargsy vargsy))
       (numargs (length arg-elements))
       (basis (get-array (list tmp numargs) $basis 'fixnum))
       (sigma (get-array tmp $sigma))
       (args  (get-array numargs $args))
       (Q     (get-array tmp $Q))
       (row 0)
       )

    (dio-initialize arg-elements)

    (sloop for soln in temp while (< row (1+ *dim1*)) do
      (if* (sloop for i from 0 for j in soln 
		thereis (and (> j 1)
			     (or (memq (aref args i) $top-only-vars)
				 (nonvarp (aref args i)))))
	  then ()
	  elseif (setq tmp (sloop for i from 0
				 for j in soln
				 if (and (> j 0) (nonvarp (aref args i)))
				   collect i))
	  then (if* (sloop for i from 0 for j in soln
			 thereis (and (> j 0) (variablep (aref args i))
				      (sloop for k in tmp
					    thereis (occurs-in (aref args i) 
							       (aref args k)))))
		   then ()
		   elseif (and $symmetry-arg-positions
			       (sloop for l1 in $symmetry-good-terms 
				     thereis (loose-sym-sequence tmp l1)))
		   then ()
		   else
		   (if* (null (cdr tmp)) then
		       (sloop for i from 0 for j in soln do
			 (asetn j basis row i))
		       (aset (aref args (car tmp)) Q row)
		       (setq row (1+ row))
		       (if (eq row *dim1*) (return))
		       elseif (all-plaus args tmp) then
		       (sloop for i from 0 for j in soln do
			 (asetn j basis row i))
		       (aset (aref args (car tmp)) Q row)
		       (aset tmp sigma row)
		       (setq row (add1 row))
		       (if (eq row *dim1*) (return))
		       ))
	  elseif (sloop for s in soln for i from 0 
		       always (or (eq 0 s) 
				  (equal (aref args i) *xex1*)
				  (equal (aref args i) *xex2*)))
	  then ()
	  else
	  (sloop for i from 0 for j in soln do (asetn j basis row i))
	  (aset (make-new-variable) Q row)
	  (setq row (1+ row))
	  (if (eq row *dim1*) (return))
	  ))

    (when (> row 0) 
      (get-solutions (symm-initialize numargs args)
		     basis Q sigma args numargs
		     (solution-1-only-columns)
		     (1- row) op
		     top))
    ))

;;; Transfer solutions for diophantine equation into substitutions. 

(defun get-solutions (char-index basis Q sigma args numargs nvcols nrow op top)
  (let ((no-0-basis (get-array (1+ nrow) $no-0-basis))
	(array-in-use $array-in-use))
    (sloop for i from 0 to nrow do
      (aset (sloop for j from 0 to numargs
		  if (> (aref basis i j) 0) collect j) 
	    no-0-basis i))
    (setq $array-in-use t
	  top (take-out nil 
			(con-nums 0 nrow) 
			no-0-basis
			(con-nums 0 numargs)
			nvcols
			(list char-index basis numargs args Q sigma op)
			top)
	  $array-in-use array-in-use)
    top
    ))

(defun take-out (soln rest no-0-basis null-cols nvcols info top)
  (when rest 
    (let ((new-null-cols null-cols) bad i)
      (setq i (car rest))
      (sloop for xa in (aref no-0-basis i)
	     do (if* (memq xa null-cols)
		     then (setq new-null-cols (removen xa new-null-cols 1))
		     elseif (memq xa nvcols)
		     then (return (setq bad t))))
      (if bad 
	  (take-out soln (cdr rest) no-0-basis null-cols nvcols info top)
	  (nconc
	    (take-out soln (cdr rest) no-0-basis null-cols nvcols info top)
	    (if new-null-cols 
		(take-out (cons i soln) (cdr rest) no-0-basis
			  new-null-cols nvcols info top)
		(if* top
		     then (one-composition (cons i soln) info t)
		     elseif (not $idem-superpose)
		     then (one-composition (cons i soln) info nil)
		     else
		     (nconc 
		       (one-composition (cons i soln) info nil)
		       (take-out (cons i soln) (cdr rest) no-0-basis
				 nil nvcols info nil)))))))))

(defun one-composition (soln info top)
  ; "soln" is a complete composition of the solutions in the basis.
  ; Try to return a set of AC-unifiers upon this composition.
  (if* (and $symmetry-arg-positions
	    (not (symmetry-non-deletable
		  soln (car info) (cadr info))))
       then
       (trace-message 4 "    Deleting a unifier by symmetry relation.")
       (incf $symmetry-dels)
       nil
       elseif (and top $last-soln (is-subseq-list $last-soln soln))
       then nil
       else
       (setq $last-soln soln)
       (add-soln soln (cdr info))))

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
	  (sloop for s in soln
		 if (> (setq l1 (aref basis s col)) 0)
		 append (ntimes l1 (aref Q s)) into sub		
		 and if (not (variablep (aref Q s))) do ()
		 finally (if* sub then
			      (setq sub (if* (cdr sub) (cons op sub) (car sub)))
			      (if* subs 
				   (if* (setq subs 
					      (comp1 subs
						     (ncons (cons (aref args col) sub))))
					() 
					(setq fail t))
				   (setq subs (ncons (cons (aref args col) sub)))))))
      (if fail (return nil)))
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

(defun loose-sym-sequence (nv-cols sym-terms)
  (and (cddr sym-terms)
       (not (condense-sequence 
	     nv-cols (sloop for xa in sym-terms collect
			    (cdr (assoc xa $symmetry-arg-positions)))))))

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
	    elseif (eq flag 1) then (setq flag 2))
	(return t))
	finally (return t)))

;;;; Following functions play the role in deleting AC-unifiers by 
;;;; symmetry relations.

(defun set-symmetry-info (rule &aux l1)
  (when (setq l1 (symmetry-vars rule))
	(setf (ref-symmetry-vars rule) l1)
	(setf (ref-symmetry-terms rule) (symmetry-terms (lhs rule) l1))))

(defun same-nonvar (t1 t2) (if* (match t1 t2) (match t2 t1)))

(defun symmetry-vars (rule &aux results)
  ; If lhs contains some AC operator, return a list of symmetry variables in lhs.
  (when (has-acop (lhs rule)) 
      (sloop with vars = (get-lhs-vars rule)
	    with first 
	    while vars do
	(setq first (car vars) vars (cdr vars))
	(sloop for second in vars 
	      if (is-symmetry-rule rule first second) 
		do (add-associate-list first second results)
		   (setq vars (deleten second vars 1)))
	    finally (return results))))

(defun is-symmetry-rule (rule xa xb)
  ; return t iff h1(rule) = h2(rule) where
  ;     h1(xa) = you and h1(xb) = me
  ;     h2(xa) = me  and h2(xb) = you.
  (let ((h1 (list (cons xa -1) (cons xb -2)))
	(h2 (list (cons xb -1) (cons xa -2))))
    (and (equal (flat-applysigma h1 (rhs rule))
		(flat-applysigma h2 (rhs rule)))
	 (equal (flat-applysigma h1 (lhs rule))
		(flat-applysigma h2 (lhs rule))))))

(defun symmetry-terms (term symvars &aux subst results)
  ; return all equivalent terms under the symmetry variables and are
  ; arguements of the same AC-operator.
  (cond ((variablep term) nil)
	((ac-root term) 
	 (sloop with args = (rem-dups (args-of term))
	       with first 
	       while args do
	   (setq first (car args) args (cdr args))
	   (sloop for second in args 
		  if (and (setq subst (same-nonvar first second))
			  (sloop for pair in subst 
				 as v1 = (car pair)
				 as v2 = (cdr pair)
				 always 
				 (or (eq v1 v2)
				     (sloop for vars in symvars
					    always (and (memq v1 vars)
							(memq v2 vars))))))
		  do (add-associate-list first second results)
		  (setq args (deleten second args 1)))
	   finally (return results)))
	(t (sloop for xa in (args-of term) 
		  append (symmetry-terms xa symvars)))))

(defun is-symmetry-eqn (vars lhs rhs &aux rhs1)
  (if* (cddr vars) then nil
      elseif (cdr vars) 
      then
      (setq vars (list (cons (car vars) (cadr vars))
		       (cons (cadr vars) (car vars))))
      (if* (equal lhs (setq rhs1 (flat-applysigma vars rhs)))
	  then t
	  elseif (equal rhs rhs1)
	  then (equal lhs (flat-applysigma vars lhs)))
      else t))

(defun symm-initialize (numargs args)
  (setq $symmetry-arg-positions 
	(if $symmetry-terms (symmetry-arg-positions numargs args)))
  (if* $symmetry-arg-positions 
       then
       (setq $symmetry-good-terms 
	     (sloop for l1 in $symmetry-terms 
		    if (sloop for xb in l1 
			      always (assoc xb $symmetry-arg-positions))
		    collect l1))

       ;;(mark "$symmetry-terms" $symmetry-terms)
       ;;(mark "$symmetry-good-terms" $symmetry-good-terms)
       ;;(mark "$symmetry-arg-positions" $symmetry-arg-positions)

       (sloop with sym-indexes = (sloop for xa in $symmetry-arg-positions
					collect (cdr xa))
	      for i from 0 to numargs
	      if (not (memq i sym-indexes)) collect i)
       else
       (setq $symmetry-good-terms nil)))

(defun symmetry-arg-positions (num args)
  (sloop for i from 0 to num
	nconc
	  (sloop with xa = (aref args i)
		for l1 in $symmetry-terms 
		append (sloop for xb in l1 
			     if (equal xa xb) collect (cons xb i)))))

(defun symmetry-non-deletable (soln nilpotent-indexes basis)
  (sloop for l1 in $symmetry-good-terms 
	always (non-decreasing-seq 
		     (sloop for xb in l1 
			   collect (val-count
				    soln basis (variablep xb)
				    (cdr (assoc xb $symmetry-arg-positions))
				    nilpotent-indexes)))))

(defun val-count (soln basis isvar col nilpotent-indexes)
  (if* isvar 
      (sloop for j in soln sum (aref basis j col))
      (sloop for j in soln 
	    if (> (aref basis j col) 0)
	      return (sloop with sum = 0 
			   for i in nilpotent-indexes
			   do (setq sum (add (times sum 10) (aref basis j i)))
			   finally (return sum)))))

;; top-only-variable implementation. >>>> 6/22/89

(defun set-top-only-vars (rule &aux vars)
  (sloop for xa in (args-of (lhs rule)) 
	 if (and (variablep xa) 
		 (sloop for xb in (args-of (lhs rule))
			always (or (variablep xb) (not (is-subterm xa xb)))))
	 do (query-insert xa vars))
  (if vars (setf (ref-top-vars rule) vars)))
