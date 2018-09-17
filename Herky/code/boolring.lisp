(in-package "USER")

; This file contains functions to implement the boolean ring transform
; reductions. First-trans takes a term in conjunctive normal form as
; set up by the reading routines, and returns one with 'and' and 'xor'
; (exclusive or). Brt is the main function that controls the reductions.
; This filee also contains functions for the eq-find algorithms.
; These are prefixed 'union'.
; They have been assimilated within the brt functions for maximum 
; efficiency. Simp-and is the function that calls the eq-find 
; algorithms with each of its list of conjuncts.

(defun top-first-trans (term)
  (cond
    ((null term) nil)
    ((variablep term) term)
    ((eq (op-of term) *and*)
     (make-term *and* (mapcar 'top-first-trans (args-of term))))
    (t (btp-trans term))))

(defun btp-trans (term)
  ;  Transforms a boolean term with 'and' and 'or' operators into a
  ;  boolean ring term with '&' and 'xor', exclusive or.
  ;  Returns modified term.
  (simplify
    (cond
      ((null term) nil)
      ((variablep term) term)
      (t (let ((new-args (mapcar 'btp-trans (args-of term)))
	       (op (op-of term)))
	   (cond
	     ((eq op *not*) (make-term *xor* (cons *trueterm* new-args)))
	     ((eq op *and*)  (make-term *and* new-args))
	     ((eq op *or*)
	      (make-term *xor* (cons (make-term *and* new-args) new-args)))
	     ((eq op *equ*)
	      (make-term *xor* (cons *trueterm* new-args)))
	     ((eq op *->*)
	      (make-term *xor* 
			 (list (make-term *and* new-args)
			       (car new-args) *trueterm*)))
	     (t (make-term op new-args))))))))

(defun or-args (arg1 arg2)
  ; Return an equivalent term (ARG1 or ARG2).
  (cond ((not (and arg1 arg2)) nil)
        ((equal arg1 arg2) arg1)
        (t (brt (list *xor* (list *and* arg1 arg2) arg1 arg2)))))

(defun not-arg (arg1)
  ; Return an equivalent term (not ARG1).
  (cond ((null arg1) *falseterm*)
        ((falsep arg1) nil)
        (t (m-xor-p *trueterm* arg1))))

(defun canonicalize (term)
   ; Convert anything into a sum of products.  If it isn't already a sum of
   ; products, then insert trivial sums and products until it is.
   (if (eq (op-of term) *xor*)
       (setq term (args-of term))
       (setq term (ncons term)))
   (make-term *xor*
	      (sloop for xa in term collect
		     (if (eq (op-of xa) *and*) xa (list *and* xa)))))

(defun decanon-and (mon) 
  (case (length mon) ((1 0) *trueterm*) (2 (first-arg mon)) (t mon)))

(defun decanon-xor (poly) 
  (case (length poly)
    ((1 0) *falseterm*) 
    (2 (decanon-and (first-arg poly))) 
    (t (make-term *xor* (sloop for xa in (args-of poly) 
			       collect (decanon-and xa))))))

(defun merge-and-remove-pairs (l1 l2 &optional (pred '<))
  ; This functions takes two sorted lists which contain no duplicates and merges them
  ; removing common pairs
  (sloop with res = nil
	with ll1 = l1
	with ll2 = l2
	with cl1
	with cl2
	while (and ll1 ll2) do
    (setq cl1 (car ll1)
	  cl2 (car ll2))
    (cond ((equal cl1 cl2)
	   (setq ll1 (cdr ll1)
		 ll2 (cdr ll2)))
	  ((funcall pred cl1 cl2)
	   (setq res (append res (ncons cl1))
		 ll1 (cdr ll1)))
	  (t (setq res (append res (ncons cl2))
		   ll2 (cdr ll2))))
	finally (return (cond (ll1 (append res ll1))
			      (ll2 (append res ll2))
			      (t res)))))

(defun merge-and-remove-dups (l1 l2 &optional (pred '<))
  ;; This functions takes two sorted lists which contain no duplicates 
  ;; and merges them making common pairs into one
  (sloop with res = nil
	with ll1 = l1
	with ll2 = l2
	with cl1
	with cl2
	while (and ll1 ll2) do
    (setq cl1 (car ll1)
	  cl2 (car ll2))
    (cond ((equal cl1 cl2)
	   (setq res (append res (ncons cl1))
		 ll1 (cdr ll1)
		 ll2 (cdr ll2)))
	  ((funcall pred cl1 cl2)
	   (setq res (append res (ncons cl1))
		 ll1 (cdr ll1)))
	  (t (setq res (append res (ncons cl2))
		   ll2 (cdr ll2))))
	finally (return (cond (ll1 (append res ll1))
			      (ll2 (append res ll2))
			      (t res)))))

(defun insert-and-remove-pairs (g-object l-list &optional u-comparefn)
  ; This functions takes a sorted list l-list and inserts g-object into it.
  ; If g-object is already in l-list then this function returns
  ; l-list with one g-object removed from it.
  (cond
    ((null l-list) (cons g-object l-list))
    (t
     (when (null u-comparefn)(setq u-comparefn 'string-lessp))
     (sloop
       with prev-position = nil
       for position on l-list
       for x = (car position)
       if (equal g-object x) return (remonce x l-list)
       else if (funcall u-comparefn g-object x)
       return (if*  prev-position
		   (progn (rplacd prev-position (cons g-object position)) l-list)
		   (cons g-object l-list))
       else do (setq prev-position position)
       finally (return (progn (rplacd prev-position  (ncons g-object)) l-list))))))

(defun m-and-m (mon1 mon2 &aux (hcm1 (half-canonicalize mon1)) (hcm2 (half-canonicalize mon2)))
  ; This function takes two perfect monomials (arguments already sorted)
  ; and returns their product.
  ; mon1 is not equal to false.
  (cond ((truep mon1) mon2)
	;((falsep mon1) mon1)
	((truep mon2) mon1)
	((falsep mon2) mon2)
	(t (let ((res-args (merge-and-remove-dups hcm1 hcm2 'total-term-ordering)))
	     (if* (cdr res-args)			;more than one argument to the and.
		 then (make-term *and*
				 (merge-and-remove-dups hcm1 hcm2 'total-term-ordering))
		 else (car res-args))))))

(defun m-and-p (mon poly &aux (poly-args (args-of poly)))
  ; This function takes a perfect monomial (arguments already sorted)
  ; and a perfect polynomial
  ; and returns their product.
  (cond ((null poly-args) *falseterm*)
	((falsep mon) mon)
	((truep mon) poly)
	(t (sloop with monomials-that-get-smaller = nil
		 with monomials-that-dont = nil
		 with mon-size = (length (half-canonicalize mon))
		 for m in poly-args
		 for new-m = (m-and-m mon m)
		 for m-size = (length (half-canonicalize m))
		 for new-m-size = (length (half-canonicalize new-m))
		 do
	     ; This function assumes that if m1 > m2 then m*m1 > m*m2 (using total-term-ordering)
	     ; This might not be the case if m and m1 or m and m2 share atomic formulae
	     ; To check for this I check the size of the m*m1 and see if it is equal to
	     ; the sum of the sizes of m and m1.
	     ; If it isn't then I know that I have to reinsert m*m1 into the list at the end.
	     (if* (equal new-m-size (+ mon-size m-size))
		 then (setq monomials-that-dont (append monomials-that-dont (ncons new-m)))
		 else (setq monomials-that-get-smaller
			    (insert-and-remove-pairs new-m monomials-that-get-smaller 'total-term-ordering)))
		 finally
		   (return
		     (let ((res-args (merge-and-remove-pairs monomials-that-get-smaller
							     monomials-that-dont 'total-term-ordering)))
		       (if* (null res-args) then *falseterm*
			   elseif (cdr res-args) then (make-term *xor* res-args)
			   else (car res-args))))))))

(defun p-and-p (poly1 poly2)
  ; This function takes two perfect polynomials (arguments already sorted)
  ; and returns their product.
  (sloop with res = *falseterm*
	for m1 in (args-of poly1)
	for new-arg = (m-and-p m1 poly2) 
	for op = (op-of new-arg) do
    (setq res
	  (cond 
	    ((eq op *xor*)
	     (if (eq (op-of res) *xor*)
		 (p-xor-p res new-arg)
		 (m-xor-p res new-arg)))
	    (t (if (eq (op-of res) *xor*)
		   (m-xor-p new-arg res)
		   (m-xor-m res new-arg)))))
    finally (return res)))

(defun m-xor-m (mon1 mon2)
  ; This function takes two perfect monomials (arguments already sorted)
  ; and returns their sum.
  (cond ((falsep mon1) mon2)
	((falsep mon2) mon1)
	(t (cond
	    ((equal mon1 mon2) *falseterm*) ; mon1 = mon2
	    ((total-term-ordering mon1 mon2) (list *xor* mon1 mon2))	; mon1 < mon2
	    (t (list *xor* mon2 mon1))	; mon2 < mon1
	    ))))

(defun m-xor-p (mon poly)
  ; This function takes a perfect monomial (arguments already sorted)
  ; and a perfect polynomial
  ; and returns their sum.
  ; This is basically insertion of mon into poly taking care to 
  ; remove a duplicate mon.
  (if* (falsep mon) then poly
      else (sloop with 1st-part-of-poly = nil
		 with res-args
		 for rest-of-poly on (args-of poly)
		 for m = (car rest-of-poly) do
	     (cond
	      ((equal mon m)
	       (setq res-args (append 1st-part-of-poly (cdr rest-of-poly)))
	       (return (if* res-args 
			    (if* (equal (length res-args) 1) 
				 (car res-args)
				 (make-term *xor* res-args))
			    *falseterm*)))
	       ((total-term-ordering mon m)
		(return (make-term *xor* (append 1st-part-of-poly
						 (cons mon rest-of-poly)))))
	       (t (setq 1st-part-of-poly (append 1st-part-of-poly 
						 (ncons m))))
	       )
	     finally (return (make-term *xor* 
					(append 1st-part-of-poly 
						(ncons mon)))))))

(defun p-xor-p (poly1 poly2)
  ; This function takes two perfect polynomials (arguments already sorted)
  ; and returns their sum.
  (let ((new-args (merge-and-remove-pairs (args-of poly1) (args-of poly2) 'total-term-ordering)))
    (if* new-args
	then (if* (cdr new-args) then (make-term *xor* new-args)
		 else (car new-args))
	else *falseterm*)))

(defun brt-if (new old) (if* (equal new old) then old else (brt new)))

(defun brt (term &optional short)
  ; "brt" stands for boolean ring transform.
  ; Applies boolean ring transform on term. Works on reductions
  ; in a bottom fashion. Returns simplified term.
  (if* term (add-time $brt-time 
		     (if* short
			 (simplify-almost-flat term)
		         (simplify term)))))

(defun simplify-almost-flat (term)
  ;  Applies boolean ring transform on term; it has already been flattened. 
  ;  The arguments of the operators "and" and "xor" are not already flatten.
  (if (or (null term) (variablep term))
      term
      (cond 
	((eq (op-of term) *and*) (simp-and-simp (args-of term)))
	((eq (op-of term) *xor*) 
	 (simp-xor-simp (sloop for arg in (args-of term) 
			       collect (simplify-flat arg))))
	((eq (op-of term) *eq*) (car (eq-find (ncons term))))
	(t term))))

(defun simplify-flat (term)
  ;  Applies boolean ring transform on term; it has already been flattened. 
  ;  The arguments of the operators "and" and "xor" are not already flatten.
  (if* (or (null term) (variablep term)) then term else
     (cond
       ((eq (op-of term) *and*) (simp-and-simp (args-of term)))
       ((eq (op-of term) *xor*)
	(make-term *xor* (sloop for arg in (args-of term) 
				collect (simplify-flat arg))))
       ((eq (op-of term) *eq*) (car (eq-find (ncons term))))
       (t term))))

(defun simplify (term &aux args)
  ;  Applies boolean ring transform on term. 
  ;  The arguments of the operators "and" and "xor" are not already flatten.
  (if* (or (null term) (variablep term)) then term else
     (cond
       ((eq (op-of term) *and*)
	(setq args (sloop for arg in (args-of term) collect (simplify arg)))
	(simp-and args))
       ((eq (op-of term) *xor*)
	(setq args (sloop for arg in (args-of term) collect (simplify arg)))
	(simp-xor args))
       ((eq (op-of term) *eq*) (car (eq-find (ncons term))))
       (t term))))

(defun and-of-monomials (args &aux pre)
  ; Returns simplified TERM whose top level operator is and.
  ; The term has been flattened, and all subterms simplified.
  (setq args (sort (eq-tr args) 'total-term-ordering))
  (cond ((member0 *falseterm* args) *falseterm*)
        (t (setq pre (pop args))
	   (sloop while (truep pre) do (setq pre (pop args)))
	   (setq args (sloop for this in args
			     if (not (or (truep this) 
					 (equal this pre)))
			     collect (prog1 pre (setq pre this))))
	   (cond (args (make-term *and* (append args (ncons pre))))
		 (pre pre)
		 (t *trueterm*)))))

(defun simp-and (args)
  (sloop with res = *trueterm* for arg in args do
    (setq res
	  (cond
	    ((eq (op-of arg) *xor*)
	     (if (eq (op-of res) *xor*)
		 (p-and-p res arg)
		 (m-and-p res arg)))
	    ((eq (op-of arg) *false*)
	     (return arg)) ; We should have this.
	    (t (if (eq (op-of res) *xor*)
		   (m-and-p arg res)
		   (m-and-m res arg)))))
	finally (return res)))

(defun simp-and-simp (args &aux pre)
  ; Returns simplified TERM whose top level operator is and.
  ; The term has been flattened, and all subterms simplified.
  (setq args (sort (eq-tr args) 'total-term-ordering))
  (if* (member0 *falseterm* args) then *falseterm* else
      (setq pre (pop args))
      (sloop while (equal pre *trueterm*) do (setq pre (pop args)))
      (setq args (sloop for this in args
		       if (not (or (equal this *trueterm*) 
				   (equal this pre)))
			 collect (prog1 pre (setq pre this))))
      (cond (args (make-term *and* (nconc args (ncons pre))))
	    (pre pre)
	    (t *trueterm*))))

(defun xor-of-monomials (args)
  ; Returns simplified (xor ARGS), a sum. The TERM has been flattened.
  (let (previous)
     (setq args (sort args 'total-term-ordering)
           previous (pop args))
     (sloop while (equal previous *falseterm*) do (setq previous (pop args)))
     (setq args 
        (sloop for this in args 
           if (cond
                    ((equal this *falseterm*) nil)
                    ((equal this previous) (setq previous nil))
                    (previous t) 
                    (t (setq previous this) nil))
           collect (prog1 previous (setq previous this))))
     (if* (null args) then
        (if* previous then previous else *falseterm*)
      elseif previous then (make-term *xor* (add-at-end args previous))
      elseif (null (cdr args)) then (car args)
      else (make-term *xor* args))))

(defun simp-xor (args)
  (sloop with res = *falseterm*
	for arg in args
	do

     ;; (if* (eq (op-of arg) *xor*) (setq arg (simp-xor (args-of arg))))

    (setq res
	  (if (eq (op-of arg) *xor*)
	      (if (eq (op-of res) *xor*)
		  (p-xor-p res arg)
		  (m-xor-p res arg))
	      (if (eq (op-of res) *xor*)
		  (m-xor-p arg res)
		  (m-xor-m res arg))))
	finally (return res)))

(defun simp-xor-simp (args)
  ; Returns simplified TERM, a sum. The TERM has been flattened.
  (let (previous)
     (setq args (sort args 'total-term-ordering)
           previous (pop args))
     (sloop while (equal previous *falseterm*) do (setq previous (pop args)))
     (setq args 
        (sloop for this in args 
           if (cond
                    ((equal this *falseterm*) nil)
                    ((equal this previous) (setq previous nil))
                    (previous t) 
                    (t (setq previous this) nil))
           collect (prog1 previous (setq previous this))))
     (if* (null args) then
	  (if previous previous *falseterm*)
	  elseif previous then (make-term *xor* (add-at-end args previous))
	  elseif (null (cdr args)) then (car args)
	  else (make-term *xor* args))))

(defun eqn2assertion (eqn)
  (if (equal (lhs eqn) (rhs eqn)) 
      *trueterm*
      (let* ((lhs (lhs eqn)) (rhs (rhs eqn)) 
	     (op1 (op-of lhs))
	     (op2 (op-of rhs)))
	(cond
	  ((eq op1 *false*)
	   (cond
	     ((eq op2 *true*) *falseterm*)
	     ((eq op2 *xor*) (m-xor-p *trueterm* rhs))
	     (t (m-xor-m *trueterm* rhs))))
	  ((eq op1 *true*) rhs)
	  ((eq op1 *xor*)
	   (cond 
	     ((eq op2 *true*) lhs)
	     ((eq op2 *false*) (m-xor-p *trueterm* lhs))
	     ((eq op2 *xor*)
	      (setq lhs (m-xor-p *trueterm* lhs)
		    op1 (op-of lhs))
	      (cond
		((eq op1 *xor*) (p-xor-p rhs lhs))
		(t (m-xor-p lhs rhs))))
	     (t (p-xor-p lhs (m-xor-m *trueterm* rhs)))))
	  (t (cond
	       ((eq op2 *true*) lhs)
	       ((eq op2 *false*) (m-xor-m *trueterm* lhs))
	       ((eq op2 *xor*) (p-xor-p rhs (m-xor-m *trueterm* lhs)))
	       (t (m-xor-p *trueterm* (m-xor-m lhs rhs)))))))))

;(in-package "USER")

(defmacro half-canonicalize (term)
   `(if (equal (op-of ,term) *and*)
	(args-of ,term)
	(ncons ,term)))

(defun half-canonicalize-and-expand-eq (mon)
  (if (eq (op-of mon) *and*)
       (sloop for arg in (args-of mon)
		   nconc (expand-eq arg))
       (expand-eq mon)))

(defun expand-eq (atom)
  (if (eq (op-of atom) *eq*)
       (sloop with rargs = (args-of atom)
	      for arg in (cdr rargs)
	      with low-arg = (car rargs)
	      collect (make-term *eq* `(,low-arg ,arg)))
       (ncons atom)))

(defun order-ass (ass source &optional flag dont-make-eq)
  (cond ((truep ass) nil)
        ((falsep ass) (refuted-result source))
	((and (eq (op-of ass) *eq*) (equal (length ass) 3) (not dont-make-eq))
	 (trace-message 4 "Transform eq(t1, t2) into an equation t1 = t2: "
			(write-term ass) (terpri))
	 (orient-an-eqn
	  (make-eqn (first-arg ass) (second-arg ass) nil source)))
	((and flag
	      (> (w-size ass) $discard-eqn-2max-size))
	 (trace-message 4 "  Postpone big proposition: "
			(write-term ass) (terpri))
	 (if (eq $post-ass-list 's)
	      (push (cons source ass) $post-ass-set)
	      (push-end (cons source ass) $post-ass-set)))
	(t (add-time $ord-time (setq ass (make-rule-from-ass ass source)))
	   (if ass (add-rule-time ass)))))

(defun compare-monomial (mon1 mon2 &aux s1 xc)
  ; Return t iff mon1 > mon2 under some ordering.
  (if* (truep mon1) then nil 
    elseif (truep mon2) then t
    elseif (not (equal (setq s1 (length mon1)) (setq xc (length mon2))))
    then (> s1 xc)
    else 
    (setq mon1 (sort (half-canonicalize-and-expand-eq mon1) 
		     'total-term-ordering)
	  mon2 (sort (half-canonicalize-and-expand-eq mon2) 
		     'total-term-ordering))
    (setq s1 nil)
    (sloop with xc for xb in mon1 do
	   (if (null mon2) (return t))
	   (setq xc (car mon2))
	   (cond ((operator-ordering (op-of xc) (op-of xb)) (return nil))
		 ((operator-ordering (op-of xb) (op-of xc)) (return t))
		 ((equal xc xb) (pop mon2))
		 ((lrpo xb xc) (return t))
		 (t (push xb s1)))
	   finally (return (and s1 (null mon2))))))

(defmacro order-pc (s1 s2) 
  ;; Assuming both S1 and S2 are non-variable terms.
  ;; Return t iff S1 is less than S2.
  (cond ((equal s1 s2) t)
	((and (nonvarp s1) (nonvarp s2))
	 (cond 
	  ((or (memq (op-of s1) *xor*and*or*) (eq (op-of s1) *eq*)
	       (memq (op-of s2) *xor*and*or*) (eq (op-of s2) *eq*))
	   (compare-item-result s1 s2))
	  ((or (predicatep (op-of s1)) (predicatep (op-of s2)))
	   (compare-term-result s1 s2))
	  (t (lrpo s1 s2))))
	(t (lrpo s1 s2))))

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
      (if* (null l2) then l1
	elseif (null l1) then nil
	else (sloop for xa in l2 always
		    (sloop for xb in l1 thereis (compare-term xb xa))))))

(defun compare-term (t1 t2)
  ; Compare two atomic formulae.  Take special cases for (true) and 
  ; variables.
  ; Return t iff t1 > t2.
  ; If the flag $ordering is S and the sizes of t1 and t2 are different,
  ; then return t iff size(t1) > size(t2). Otherwise call lrpo. 
  (if* (or (variablep t1) (truep t1)) then nil
      elseif (variablep t2) then (memq t2 (all-vars-of t1))
      elseif (truep t2) then t
      elseif (same-root t1 t2) 
      then (lrpo t1 t2)
      else (operator-ordering (op-of t1) (op-of t2))))

(defun compare-item-result (s1 s2) (compare-item s2 s1))
(defun compare-term-result (s1 s2) (compare-term s2 s1))

(defun skolemize (ass &optional sign &aux (op (op-of ass)))
  ; Remove all quantifiers of ASS. Take special care of "equ" and "xor".
  (cond 
    ((member op *exist*all*) 
     (skolemize (skolemize-away-quants ass ass sign) sign))
    ((eq op *equ*)
     (let ((a1 (sloop for xa in (args-of ass)
		      if (has-quantifier xa)
		      return xa)) a2)
       (if* a1 then 
	    (setq a2 (remove0 a1 (args-of ass))
		  a2 (if* (cdr a2) then (make-term *xor* a2) else (car a2)))
	    (remove-quan-args (list *and*
				    (list *->* a1 a2) 
				    (list *->* a2 a1)) sign)
	    else
	    (remove-quan-args (make-term `xor (cons *trueterm* (args-of ass)))
			      sign))))
    ((eq op *xor*)
     (let ((a1 (sloop for xa in (args-of ass)
		      if (has-quantifier xa)
		      return xa)) a2)
       (if* a1 then 
	    (setq a2 (remove0 a1 (args-of ass))
		  a2 (if* (cdr a2) then (make-term *xor* a2) else (car a2)))
	    (if* (equal a2 *trueterm*) then
		 (make-term *xor* (cons *trueterm* (skolemize a1 (not sign))))
		 else
		 (remove-quan-args 
		   (list *not* (list *and*
				     (list *->* a1 a2)
				     (list *->* a2 a1))) 
		   (not sign)))
	    else
	    (remove-quan-args ass sign))))
    ((eq op *->*)
     (list *->* 
	   (skolemize (first-arg ass) (not sign))
	   (skolemize (second-arg ass) sign)))
    ((eq op *not*) (list *not* (skolemize (first-arg ass) (not sign))))
    ((member op *xor*and*or*) (remove-quan-args ass sign))
    (t ass)))

(defun remove-quan-args (ass sign)
  ; remove the quantifiers from the arguments of ass.
  (make-term (op-of ass) 
	     (sloop for xa in (args-of ass) 
		   collect (skolemize xa sign))))

(defun skolemize-away-quants (ass whole-ass sign)
   ; Remove the leading quantifiers from ass by introducing a skolem 
   ; function or a skolem variable.
   (let ((quant (op-of ass)) (var (first-arg ass)) (form (second-arg ass))
	 newvar)
     (setq newvar (if (equal sign (eq quant *exist*))  
		      (make-new-variable)
		      (get-sko-func var form whole-ass))
	   form (special-subst newvar var form))
     (if (quantifierp (op-of form)) 
	 (skolemize-away-quants form whole-ass sign)
       form)))

(defun special-subst (new old form)
  (cond ((variablep form) 
	 (if* (eq form old) new form))
        ((memq (op-of form) *exist*all*)
	 (if* (equal (first-arg form) old) 
	    then form
	    else (list (op-of form) (first-arg form)  
		       (special-subst new old (second-arg form)))))
	(t (make-term (op-of form)
		      (sloop for xa in (args-of form)
			     collect (special-subst new old xa))))))

(defun subst-quant-form (func ass source &aux l1)
    (setq l1 (list *->* ass func))
    (process-ass2 (list *->* (skolemize-away-quants ass l1 t) func) source)
    (setq l1 (list *->* func ass))
    (process-ass2 (list *->* func (skolemize-away-quants ass l1 nil)) source))

(defun hasquant (ass)
  ; Determine whether a formula has any quantifiers.
    (cond ((variablep ass) nil)
	  ((quantifierp (op-of ass)) t)
          (t (sloop for xa in (args-of ass) thereis (hasquant xa)))))

(defun get-sko-func (var ass whole-ass) 
    ; Given that we have to introduce a skolem function to replace var in
    ; ass, figure out what that function should be.
    (let ((op (get-new-operator "s")) (args (remonce var (free-vars ass))))
      (setq op (enter-op op (length args)))
      (push op $skolem-ops)
      (setq args (make-term op args))
      (trace-message 3 "  Introducing"
	   (display-one-arity2 op)
	   (princ " ") (write-term args)
	   (princ " as a skolem function for ") 
	   (write-variable var poport)
	   (terpri) (princ "     in the assertion: ") 
	   (write-term whole-ass) (terpri))
      args))
