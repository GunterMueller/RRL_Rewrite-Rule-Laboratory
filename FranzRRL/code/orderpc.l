;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

(defun half-canonicalize-and-expand-eq (mon)
  (if (eq (op-of mon) 'and) then (loop for arg in (args-of mon)
				       nconc (expand-eq arg))
                            else (expand-eq mon)))

(defun mini-half-canonicalize-and-expand-eq (mon)
  (let ((res (if (eq (op-of mon) 'and) then (loop for arg in (args-of mon)
						  nconc (expand-eq arg))
		 else (expand-eq mon))))
    (make-term 'and res)))

(defun expand-eq (atom)
  (if (eq (op-of atom) 'eq) then
      (loop with rargs = (args-of atom)
	    for arg in (cdr rargs)
	    with low-arg = (car rargs)
	    collect (make-term 'eq `(,low-arg ,arg)))
      else (ncons atom)))

(defun mini-expand-eq (atom)
  (if (and (eq (op-of atom) 'eq) (cdddr atom))then
      (loop with rargs = (args-of atom)
	    for arg in (cdr rargs)
	    with low-arg = (car rargs)
	    collect (make-term 'eq `(,low-arg ,arg)))
      else atom))

(defun order-ass (ass source &optional flag dont-make-eq)
  (cond ((truep ass) nil)
        ((falsep ass) (refuted-result source))
	((and (eq (op-of ass) 'eq) (eq (length ass) 3) (not dont-make-eq))
	 (if (> $trace_flag 2)
	     then (terpri) (princ "Transform EQ into a rewrite rule: ")
	          (write-term ass) (terpri))
	 (process-equation (make-eqn (first-arg ass) (second-arg ass) nil source)))
	((and flag
	      (not (eq $post-ass-list 'q))
	      (> (setq flag (depth ass)) $small-depth))
	 (if (eq $trace_flag 3) then (terpri)
	    (princ "  Postpone big proposition: ") (write-term ass) (terpri))
	 (if (eq $post-ass-list 's)
	   then (push `(,flag . (,source . ,ass)) $post-ass-set)
	   else (setq $post-ass-set (insert `(,flag . (,source . ,ass))
					    $post-ass-set 'car-num-order t))))
	(t (add-time $ord_time (setq ass (make-rule-from-ass ass source)))
	   (if ass then (add-time $add_time (add-rule ass))))))

(defun size-compare (mon1 mon2)
  ; Return t iff mon1 > mon2 under some ordering.
  (if (truep mon1) then nil 
    elseif (truep mon2) then t
    else (let ((s1 (reverse (sort (half-canonicalize-and-expand-eq mon1) 'order-pc)))
               (s2 (reverse (sort (half-canonicalize-and-expand-eq mon2) 'order-pc))))
	    (loop with xa with xb while s2 do
		(setq xa (pop s2) xb (car s1))
		(cond ((alphalessp (op-of xb) (op-of xa)) (return nil))
		      ((alphalessp (op-of xa) (op-of xb)) t)
		      ((equal xa xb) (pop s1))
		      ((lrpo xb xa) t)
		      (t (push xa s2) (pop s1)))
		finally (return s1)))))

(defun size-compare (mon1 mon2)
  ; Return t iff mon1 > mon2 under some ordering.
  (if (truep mon1) then nil 
    elseif (truep mon2) then t
    else (let ((s1 (reverse (sort (half-canonicalize-and-expand-eq mon1) 'order-pc)))
               (s2 (reverse (sort (half-canonicalize-and-expand-eq mon2) 'order-pc))))
	    (loop with xa with xb while s2 do
		(setq xa (pop s2) xb (car s1))
		(cond ((pc-grt-prec (op-of xa) (op-of xb)) (return nil))
		      ((pc-grt-prec (op-of xb) (op-of xa)) t)
		      ((equal xa xb) (pop s1))
		      ((lrpo xb xa) t)
		      (t (push xa s2) (pop s1)))
		finally (return s1)))))

(defun compare-item (t1 t2)
  ; Compare two terms, returning t if t1 > t2.
  ; First check that the variable set of t1 is a superset or equal to t2,
  ; then call comp-item.
  (comp-terms (half-canonicalize-and-expand-eq t1) 
	      (half-canonicalize-and-expand-eq t2)))

(defun comp-terms (s1 s2)
  ; Compare two sets of atomic formulae, returning t iff s1 > s2. 
  ; Rank first by size, then by set ordering induced by compare-term.
  (let ((l1 (set-diff s1 s2)) (l2 (set-diff s2 s1)))
      (if (null l2) then l1
	elseif (null l1) then nil
	else (loop for xa in l2 always
	        (loop for xb in l1 thereis (compare-term xb xa))))))

(defun compare-term (t1 t2)
   ; Compare two atomic formulae.  Take special cases for (true) and 
   ; variables.
   ; Return t iff t1 > t2.
   ; If the flag $ordering is S and the sizes of t1 and t2 are different,
   ; then return t iff size(t1) > size(t2). Otherwise call lrpo. 
   (if (or (variablep t1) (truep t1)) then nil
      elseif (variablep t2) then (memq t2 (all-vars t1))
      elseif (truep t2) then t
      elseif (and (eq (car t1) $anspred) (eq (car t2) $anspred))
      then (comp-terms (args-of t1) (args-of t2))
      elseif (eq (car t2) $anspred) then t
      elseif (eq (car t1) $anspred) then nil
      elseif (same-op t1 t2) then (rpomult t1 t2)
      else (and (not (alphalessp (op-of t1) (op-of t2)))
		(or (rpomult t1 t2) 
		    (equiv-list (args-of t1) (args-of t2))))))

;The following change was made to ensure that in the fopc case when
;using lrpo ordering the variable check is made.
(defun compare-term (t1 t2)
  ; Compare two atomic formulae.  Take special cases for (true) and 
  ; variables.
  ; Return t iff t1 > t2.
  ; If the flag $ordering is S and the sizes of t1 and t2 are different,
  ; then return t iff size(t1) > size(t2). Otherwise call lrpo. 
  (if (or (variablep t1) (truep t1)) then nil
      elseif (variablep t2) then (memq t2 (all-vars t1))
      elseif (truep t2) then t
      elseif (and (eq (car t1) $anspred) (eq (car t2) $anspred))
      then (comp-terms (args-of t1) (args-of t2))
      elseif (eq (car t2) $anspred) then t
      elseif (eq (car t1) $anspred) then nil      
      elseif (same-op t1 t2) 
      then (and (is-subset (var-list t2) (var-list t1)) (lrpo t1 t2 ));(rpomult t1 t2))
      else (pc-grt-prec (op-of t1) (op-of t2))))

(defun order-pc (s1 s2 &aux s1op s2op)
  ;  Returns t if S1 is less or equal to S2.
  (cond ((equal s1 s2) #+franz t
	               #+lispm nil)
	((and (variablep s1) (variablep s2))
	 (compare-symbol s1 s2))
	((variablep s1) t)
	((variablep s2) nil)
	((same-op s1 s2)
	 (if (memq (op-of s1) '(& xor eq and))
	     then (if (eq (length s1) (length s2)) 
		      then (order-pc-seq (args-of s1) (args-of s2))
		      else (< (length s1) (length s2)))
	     elseif (predicatep (op-of s1))
	     then (compare-term s2 s1)
	     else (lrpo s2 s1)))
	(t (setq s1op (op-of s1) s2op (op-of s2))
   	  (if (and (numberp s1op) (numberp s2op)) then (lessp s1op s2op)
	   elseif (numberp s1op) then t
	   elseif (numberp s2op) then nil
	   elseif (and (predicatep s1op) (predicatep s2op))
	     then (if (grt-prec s1op s2op) then nil
		      elseif (grt-prec s2op s1op) then t
		      else (alphalessp s1op s2op))
	   else (lrpo s2 s1)))))

(defun compare-symbol (s1 s2)
  (cond ((alphalessp s1 s2) t)
	((alphalessp s2 s1) nil)
	(t ; at this point, s1 and s2 have the same print name.
	 (if (and (boundp s1) (boundp s2))
	     then (lessp (symeval s1) (symeval s2))
	     elseif (boundp s2) then t
	     else nil))))

(defun order-pc-seq (s1 s2)
   (loop for xa in s1 for xb in s2 
        if (not (equal xa xb)) return (order-pc xa xb)))

(defun order-pc (s1 s2)
  (selectq (order-pc-res s1 s2)
    (1 t)
    (2 nil)
    (0 #+franz t
       #+lispm nil)))

(defun order-pc-res (s1 s2)
 ; (dbg)
  ;  Returns t if S1 is less or equal to S2.
  (cond ((equal s1 s2) 0)
	((and (listp s1) (listp s2))
	 (cond ;((or (eq (op-of s1) 'xor) (eq (op-of s2) 'xor)) (dbg))
	       ((or (memq (op-of s1) '(& and xor eq)) (memq (op-of s2) '(& and xor eq)))
		(selectq (compare-item-result s1 s2)
		  (1 1)
		  (2 2)
		  (0 (total-order-pc-res s1 s2))))
	       ((or (predicatep (op-of s1)) (predicatep (op-of s2)))
		(selectq (compare-term-result s1 s2)
		  (1 1)
		  (2 2)
		  (0 (total-order-pc-res s1 s2))))
	       (t (selectq (lrpo-result s1 s2)
		    (1 1)
		    (2 2)
		    (0 (total-order-pc-res s1 s2))))))
	(t (total-order-pc-res s1 s2))))

(defun compare-item-result (s1 s2)
  ; Returns 0 if l1 is equal to l2
  ;         1 if l1 is less than l2
  ;         2 if l2 is less than l1
  (cond ((compare-item s2 s1) 1)
	((compare-item s1 s2) 2)
	(t 0)))

(defun compare-term-result (s1 s2)
  ; Returns 0 if l1 is equal to l2
  ;         1 if l1 is less than l2
  ;         2 if l2 is less than l1
  (cond ((compare-term s2 s1) 1)
	((compare-term s1 s2) 2)
	(t 0)))

(defun lrpo-result (s1 s2)
  ; Returns 0 if l1 is equal to l2
  ;         1 if l1 is less than l2
  ;         2 if l2 is less than l1
  (cond ((lrpo s2 s1) 1)
	((lrpo s1 s2) 2)
	(t 0)))

(defun total-order-pc-res (l1 l2)
  ; Returns 0 if l1 is equal to l2
  ;         1 if l1 is less than l2
  ;         2 if l2 is less than l1
  (cond ((null l1)
	 (if (null l2) then 0 else 1))
	((null l2) 2)
	((atom l1)
	 (if (atom l2)
	     then (cond ((equal l1 l2) 0)
			((pc-grt-prec l1 l2) 2)
			((pc-grt-prec l2 l1) 1)
			(t t)) ; (dbg)))
	     else 1))
	((atom l2) 2)
	((or (member (op-of l1) '(& and eq)) (member (op-of l2) '(& and eq)))
	 (cond ((> (literal-num l1) (literal-num l2)) 2)
	       ((> (literal-num l2) (literal-num l1)) 1)
	       (t (loop for ll1 in l1
			for ll2 in l2
			as comp = (total-order-pc-res ll1 ll2)
			until (neq comp 0)
			finally (return comp)))))
	((> (length l1) (length l2)) 2)
	((> (length l2) (length l1)) 1)
	(t (loop for ll1 in l1
		 for ll2 in l2
		 as comp = (total-order-pc-res ll1 ll2)
		 until (neq comp 0)
		 finally (return comp)))))

(defun total-order-pc (s1 s2)
  (selectq (total-order-pc-res s1 s2)
    (0 #+franz t
       #+lispm nil)
    (1 t)
    (2 nil)))

(defun total-order-res (l1 l2)
  ; Returns 0 if l1 is equal to l2
  ;         1 if l1 is less than l2
  ;         2 if l2 is less than l1
  (cond ((null l1)
	 (if (null l2) then 0 else 1))
	((null l2) 2)
	((atom l1) (if (atom l2) then (total-order-atom l1 l2) else 1))
	((atom l2) 2)
	((eq (car l1) 'and)
	 (if (eq (car l2) 'and) 
	     then
	     (cond ((> (length l1) (length l2)) 2)
		   ((> (length l2) (length l1)) 1)
		   (t (loop for ll1 in l1
			    for ll2 in l2
			    as comp = (total-order-res ll1 ll2)
			    until (neq comp 0)
			    finally (return comp))))
	     else 2))
	((eq (car l2) 'and) 1)
	((> (length l1) (length l2)) 2)
	((> (length l2) (length l1)) 1)
	(t (loop for ll1 in l1
		 for ll2 in l2
		 as comp = (total-order-res ll1 ll2)
		 until (neq comp 0)
		 finally (return comp)))))

(defun total-order-atom (op1 op2)
  ; Returns 0 if op1 is equal to op2
  ;         1 if op1 is less than op2
  ;         2 if op2 is less than op1
  (cond ((eq op1 op2) 0)
	((numberp op1)
	 (if (numberp op2) then 
	     (if (greaterp op1 op2) then 2 else 1)
	     else 1))
	((numberp op2) 2)
	(t (if (alphalessp op1 op2) then 1
	       elseif (alphalessp op2 op1) then 2
	       elseif (not (symbolp op1)) then 0
	       elseif (and (boundp op1) (boundp op2))
	       then (if (greaterp (symeval op1) (symeval op2)) then 2 else 1)
	       elseif (boundp op2) then 1
	       elseif (boundp op1) then 2
	       else 0))))


(defun total-order (s1 s2)
  (selectq (total-order-res s1 s2)
    (0 #+franz t
       #+lispm nil)
    (1 t)
    (2 nil)))

(defun total-order-2 (s1 s2)
  (selectq (total-order-res s1 s2)
    (0 #+franz nil
       #+lispm t)
    (1 nil)
    (2 t)))
