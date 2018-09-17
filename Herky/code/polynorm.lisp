(in-package "USER")

; This file contains functions to implement the polynomial simplifications.
; A polynomial is defined by +, * and 0, where 
;     + is AC;
;     0 is the zero of * and the unit of +;
;     + distributes over *;
;     + satisfies the cancellation law.
;   
; * is optionally associative;
; * is optionally commutative;
; * has optionally the unit;
; * has optionally the nilpotent property m: x^m == x;
; + has optionally the nilpotent property n: nx == 0.
;
; Three main group of functions needed to be done:
; 1. Normalize a polynomial;
; 2. Reduction in built-in associativity of *;
; 3. Superpose a rule with the distributation law;

(defmacro times-cdr (n1 list) 
  `(if (eq ,n1 1)
       ,list
       (sloop with cf = ,n1 
	      for xa in ,list 
	      collect (progn (setf (cdr xa) (times cf (cdr xa)))
			     xa))
       ))

(defmacro sharing-coef (term cf)
  `(times-cdr ,cf (mult-form-minus (+-canonicalize ,term))))

;;;; First Group of Functions.

(defun poly-simplify (term) (poly-simplify-aux term))

(defun poly-simplify-aux (term &aux args)
  ; Applies polynomial transform on term.
  ; It assumes nothing about whether it is flattened or not.
  ; Works on reductions in a bottom-up fashion. 
  ; Returns simplified flattended term.
  (if (or (null term) (variablep term)) 
      term
      (cond
	((eq (op-of term) *+*)
	 (simplify-+ (mapcar 'poly-simplify-aux (args-of term))))
	((eq (op-of term) $*$)
	 (simplify-* (mapcar 'poly-simplify-aux (args-of term))))
	(t (setq args (mapcar 'poly-simplify-aux (args-of term)))
	   (if (eq (op-of term) *-*)
	       (negate-poly-term (car args))
	       (compress-flat (op-of term) args))
	   ))))

(defun simplify-+ (args)
  (sloop with res = *0term*
	for arg in args do
    (setq res
	  (if (and (nonvarp arg) (eq *+* (op-of arg)))
	      (if (and (nonvarp res) (eq *+* (op-of res)))
		  (p-+-p res arg)
		  (m-+-p res arg))
	      (if (and (nonvarp res) (eq *+* (op-of res)))
		  (m-+-p arg res)
		  (m-+-m res arg))))
	finally (return res)))

(defun simplify-* (args)
  (sloop with res = nil for arg in args 
	 with negative = 1
	 if (equal arg *0term*) return arg ; We should have this.
	 else do
	 (setq res
	       (if (variablep arg)
		   (if (and (nonvarp res) (eq *+* (op-of res)))
		       (if (memq $*$ $ac) (m-*-p arg res) (p-*-m res arg))
		     (m-*-m res arg))
		 (if (eq *+* (op-of arg))
		     (if (is-rooted-+ res)
			 (p-*-p res arg)
		       (m-*-p res arg))
		   (progn
		     (if (eq (op-of arg) *-*)
			 (setq arg (first-arg arg)
			       negative (- negative)))
		     (if (is-rooted-+ res)
			 (if (memq $*$ $ac)
			     (m-*-p arg res)
			   (p-*-m res arg))
		       (m-*-m res arg))))))
	 finally (return (if (< negative 0)
			     (negate-poly-term res)
			   res))))

#|
(defun dummy-simplify-* (args)
  (sloop with res = nil for arg in args 
	 if (equal arg *0term*) return arg ; We should have this.
	 else do
	 (setq res
	       (if (variablep arg)
		   (if (and (nonvarp res) (eq *+* (op-of res)))
		       (if (memq $*$ $ac) (m-*-p arg res) (p-*-m res arg))
		       (m-*-m res arg))
		   (if (eq *+* (op-of arg))
		       (if (and (nonvarp res) (eq *+* (op-of res)))
			   (p-*-p res arg)
			   (m-*-p res arg))
		       (if (and (nonvarp res) (eq *+* (op-of res)))
			   (if (memq $*$ $ac)
			       (m-*-p arg res)
			       (p-*-m res arg))
			   (m-*-m res arg)))))
	 finally (return res)))

(defun dummy-p-+-p (poly1 poly2)
  ; This function takes two perfect polynomials (arguments already sorted)
  ; and returns their sum.
  (if (or poly1 poly2)
      (let ((new-args (merge-sort-args 
			(args-of poly1) (args-of poly2) 'total-term-ordering)))
	(if (cdr new-args) 
	    (make-term *+* new-args)
	    (car new-args)))
      *0term*))
|#

(defun p-+-p (poly1 poly2)
  (sloop for mon in (args-of poly2) do 
	 (cond ((and (nonvarp poly1) (eq (op-of poly1) *+*))
		(setq poly1 (m-+-p mon poly1)))
	       (t (setq poly1 (m-+-m mon poly1)))))
  poly1)

(defun m-*-m (mon1 mon2)
  ; This function takes two perfect monomials and returns their product. 
  ; mon1 is not equal to 0.
  (cond ((null mon1) mon2)
	((null mon2) mon1)
	((equal *0term* mon2) mon2)
	(t (let ((sign 1))
	     (if (is-rooted-minus mon1)
		 (setq sign (- sign)
		       mon1 (first-arg mon1)))
	     (if (is-rooted-minus mon2)
		 (setq sign (- sign)
		       mon2 (first-arg mon2)))
	     (setq mon2
		   (if (memq $*$ $ac)
		       (merge-sort-args
			(*-canonicalize mon1)
			(*-canonicalize mon2)
			'total-term-ordering)
		     (if (memq $*$ $associative)
			   (append 
			    (*-canonicalize mon1)
			    (*-canonicalize mon2))
		       (list mon1 mon2))))
	     (setq mon1 (if (cdr mon2)	
			    (make-term $*$ mon2)
			  (car mon2)))
	     (if (> sign 0)
		 mon1
	       (negate-by-minus mon1))))))

(defun m-*-p (mon poly) 
  ; This function takes a perfect monomial and a perfect polynomial 
  ; (arguments already sorted) and returns their product.
  (cond ((null (args-of poly)) *0term*)
	((equal *0term* mon) mon)
	((null mon) poly)
	((memq $*$ $ac)
	 (sloop with monomials-that-get-smaller = nil
	       with monomials-that-dont = nil
	       with mon-size = (length (*-canonicalize mon))
	       for m in (args-of poly)
	       as new-m = (m-*-m mon m)
	       as m-size = (length (*-canonicalize m))
	       as new-m-size = (length (*-canonicalize new-m))
	       do
	   ; This function assumes that if m1 > m2 then m*m1 > m*m2 
	   ; (using total-term-ordering)
	   ; This might not be the case if m and m1 or m and m2 share atomic
	   ; formulae. To check for this I check the size of the m*m1 and 
	   ; see if it is equal to the sum of the sizes of m and m1.
	   ; If it isn't then I know that I have to reinsert m*m1 into 
	   ; the list at the end.
	   (if* (equal new-m-size (+ mon-size m-size))
	       then (setq monomials-that-dont (append monomials-that-dont 
						      (ncons new-m)))
	       else (setq monomials-that-get-smaller
			  (insert-sort-arg new-m monomials-that-get-smaller
					   'total-term-ordering)))
	       finally
		 (return
		   (let ((res-args (merge-sort-args
				    monomials-that-get-smaller
				    monomials-that-dont
				    'total-term-ordering)))
		       (if* (null res-args) then *0term*
			   elseif (cdr res-args) then (make-term *+* res-args)
			   else (car res-args))))))
	(t (setq poly (sloop for m in (args-of poly) collect (m-*-m mon m)))
	   (if* (null poly) 
	       then *0term*
	       elseif (cdr poly) then (make-term *+* poly)
	       else (car poly)))))

(defun p-*-m (poly mon)
  ;; Assuming that * is not AC.
  (cond ((null (args-of poly)) *0term*)
	((equal *0term* mon) mon)
	((null mon) poly)
	(t (setq poly (sloop for m in (args-of poly) collect (m-*-m m mon)))
	   (if* (null poly) 
	       then *0term*
	       elseif (cdr poly) then (make-term *+* poly)
	       else (car poly)))))

(defun p-*-p (poly1 poly2)
  ; This function takes two perfect polynomials (arguments already sorted)
  ; and returns their product.
  (sloop with res = *0term*
	 for m1 in (args-of poly1)
	 as new-arg = (m-*-p m1 poly2) do
    (setq res
	  (if (and (nonvarp new-arg) (eq *+* (op-of new-arg)))
	      (if (and (nonvarp res) (eq *+* (op-of res)))
		   (p-+-p res new-arg)
		   (m-+-p res new-arg))
	      (if (and (nonvarp res) (eq *+* (op-of res)))
		 (m-+-p new-arg res)
		 (m-+-m res new-arg))))
	finally (return res)))
#|
(defun p-*-p (poly1 poly2)
  ; This function takes two perfect polynomials (arguments already sorted)
  ; and returns their product.
  (sloop with res = *0term*
	 for xa in (args-of poly1) 
	 for new = (m-*-p xa poly2) do
	 (cond ((equal res *0term*)
		(setq res new))
	       ((variablep poly2)
		(setq res (m-*-m m1 poly2)))
	       ((eq (op-of poly2) *+*)
		(setq poly2 (m-*-p m1 poly2)))
	       (t
		(setq poly2 (m-*-m m1 poly2)))
	       )

	  (if (and (nonvarp new-arg) (eq *+* (op-of new-arg)))
	      (if (and (nonvarp res) (eq *+* (op-of res)))
		   (p-+-p res new-arg)
		   (m-+-p res new-arg))
	      (if (and (nonvarp res) (eq *+* (op-of res)))
		 (m-+-p new-arg res)
		 (m-+-m res new-arg))))
	finally (return res)))
|#

(defun m-+-m (mon1 mon2)
  ; This function takes two perfect monomials and returns their sum.
  (cond ((equal *0term* mon1) mon2)
	((equal *0term* mon2) mon1)
	((and (nonvarp mon1) (eq (op-of mon1) *-*) (equal (first-arg mon1) mon2))
	 *0term*)
	((and (nonvarp mon2) (eq (op-of mon2) *-*) (equal (first-arg mon2) mon1))
	 *0term*)
	(t (if (total-term-ordering mon1 mon2)
	       (list *+* mon1 mon2)	; mon1 > mon1
	       (list *+* mon2 mon1)))))	; mon1 <= mon2

#|
(defun dummy-m-+-p (mon poly)
  ; This function takes a perfect monomial (arguments already sorted)
  ; and a perfect polynomial
  ; and returns their sum.
  ; This is basically insertion of mon into poly taking care to remove a duplicate mon.
  (if (equal *0term* mon)
      poly
      (sloop with 1st-part-of-poly = nil
	     for rest-of-poly on (args-of poly)
	     as m = (car rest-of-poly) 
	     do (if (total-term-ordering mon m)
		    (return (make-term *+* (append 1st-part-of-poly
						   (ncons mon) rest-of-poly)))
		  (setq 1st-part-of-poly (append1 1st-part-of-poly m)))
	     finally (return (make-term *+* (append1 1st-part-of-poly mon))))))
|#
(defmacro m-+-p-insert ()
  `(sloop with 1st-part-of-poly = nil
	     for rest-of-poly on (args-of poly)
	     as m = (car rest-of-poly) 
	     do (if (total-term-ordering mon m)
		    (return (make-term *+* (append 1st-part-of-poly
						   (ncons mon) rest-of-poly)))
		  (setq 1st-part-of-poly (append1 1st-part-of-poly m)))
	     finally (return (make-term *+* (append1 1st-part-of-poly mon)))))

(defun m-+-p (mon poly)
  ; This function takes a perfect monomial (arguments already sorted)
  ; and a perfect polynomial
  ; and returns their sum.
  (if* (equal *0term* mon)
      then poly
      elseif (and (nonvarp mon) (eq (op-of mon) *-*))
      then
      (if* (member0 (first-arg mon) (args-of poly))
	   then 
	   (setq poly (deleten (first-arg mon) poly 1))
	   (if (cdr (args-of poly)) poly (first-arg poly))
	   else
	   (m-+-p-insert))
      elseif (member0 (make-term *-* mon) (args-of poly))
      then
      (setq poly (deleten (first-arg mon) poly 1))
      (if (cdr (args-of poly)) poly (first-arg poly))
      else
      (m-+-p-insert)))

(defun merge-sort-args (l1 l2 &optional (pred '<))
  ; This functions takes two sorted lists and merges them.
  ; Good for +'s args or *'s args if * is commutative.
  (sloop with res = nil
	with ll1 = l1
	with ll2 = l2
	with cl1
	with cl2
	while (and ll1 ll2) do
    (setq cl1 (car ll1)
	  cl2 (car ll2))
    (cond ((funcall pred cl1 cl2)
	   (setq res (append res (ncons cl1))
		 ll1 (cdr ll1)))
	  (t (setq res (append res (ncons cl2))
		   ll2 (cdr ll2))))
	finally (return (cond (ll1 (append res ll1))
			      (ll2 (append res ll2))
			      (t res)))))

(defun insert-sort-arg (g-object l-list &optional u-comparefn)
  ; This functions takes a sorted list l-list and inserts g-object into it.
  ; If g-object is already in l-list then this function returns
  ; l-list with one g-object removed from it.
  (cond
    ((null l-list) (ncons g-object))
    (t (if (null u-comparefn) (setq u-comparefn 'string-lessp))
       (sloop with prev-position = nil
	     for position on l-list
	     as x = (car position)
	     if (funcall u-comparefn g-object x)
	       return (if prev-position
			  (progn (rplacd prev-position (cons g-object position)) l-list)
			  (cons g-object l-list))
	     else do (setq prev-position position)
	     finally (return (progn (rplacd prev-position (ncons g-object)) l-list))))))

(defun +-canonicalize (term)
  ; Convert anything into args of a product. 
  (if (nonvarp term) 
      (if* (eq (op-of term) *+*) then (args-of term) 
	  elseif (eq (op-of term) *0*) then nil
	  else (ncons term))
      (ncons term)))

(defun +-canonicalize-minus (term)
  ; Convert anything into args of a product. 
  (if (nonvarp term) 
      (if* (eq (op-of term) *+*) 
	   then (mapcar 'negate-by-minus (args-of term) )
	   elseif (eq (op-of term) *0*) then nil
	   else (ncons (negate-by-minus term)))
      (ncons (negate-by-minus term))))

(defmacro negate-poly-term (res)
  `(if (is-rooted-+ ,res)
       (make-term *+* (mapcar 'negate-by-minus (args-of ,res)))
       (negate-by-minus ,res)))

(defun negate-by-minus (term)
  (if (not (nonvarp term))
      (list *-* term)
    (if (eq (op-of term) *-*)
	(first-arg term)
      (if (eq (op-of term) *0*)
	  term
	(list *-* term)))))

(defun *-canonicalize (term)
  ; Convert anything into args of a product. 
  (if (and (nonvarp term) (eq (op-of term) $*$))
      (args-of term)
      (ncons term)))


;;; Group Two: reduction in built-in associativity.

(defun poly-reduce-at-root (term op-rules &aux (op (op-of term)))
  ; Returns rewritten term iff term can be rewritten.
  (cond
   ((eq op *+*) (reduce-+-term term))
   ((eq op $*$) (reduce-*-term term (get-rules-with-op $*$ op-rules) $poly-rules))
   (t nil)))

(defun poly-reduce-by-one-rule (term rule)
  (or (poly-reduce-by-one-at-root term rule)
      (sloop for xa in (args-of term) for i from 1
	     if (and (nonvarp xa) (setq xa (poly-reduce-by-one-rule xa rule)))
	     return (replace-nth-arg i term xa)
	     finally (return nil))))

(defun poly-reduce-by-one-at-root (term rule)
  ; return the reduced term by rule.
  (when (same-root term (lhs rule)) 
	(cond
	 ((eq (op-of term) $*$) (reduce-*-term term (ncons rule)))
	 ((eq (op-of term) *+*) 
	  (or (reduce-+-term term (ncons rule))
	      (if (is-multi-1p-rule rule)
		  (reduce-by-one-multi-1p-rule term rule))
	      (if (not (member $*$ $associative))
		  (reduce-+-term-wt-1-arg term (ncons rule)))))
	 (t (ac-reduce-by-one-at-root term rule)))))

(defun poly-cycle-reduce-by-one-at-root (term rule &aux condi)
  ; return the reduced term by rule.
  (if (variablep term)
      nil
      (when (same-root term (lhs rule)) 
	  (setq condi (list (get-rhs-vars rule) (rhs rule)))
	  (cond
	    ((eq (op-of term) $*$)
	     (flat-term (reduce-*-term term (ncons rule) condi)))
	    ((eq (op-of term) *+*) 
	     (flat-term (reduce-+-term term (ncons rule))))
	    (t (if (setq condi (applies (lhs rule) term condi))
		   (add-to-args rule condi)))))))

(defun poly-cycle-luck (new old) (total-term-ordering new old))

(defmacro poly-reduce-+-term (term)
  ;; term is assumed to be +-rooted.
  `(cond ((sloop for xa in $nilpotent-rules 
		 if (eq *+* (caddr xa))
		 return (reduce-by-nilpotent xa ,term)))
	 ((reduce-+-term ,term))
	 ((member $*$ $associative) nil)
	 ((reduce-+-term-wt-1-arg ,term))))

(defmacro is-small-term (term)
  `(or (variablep ,term) (is-constant-term ,term)))

(defmacro decompose-x1-t1 ()
  `(if (nonvarp xa)
       (if* (eq (op-of xa) $*$) then
	    (if* (is-small-term xa)
		 then (setq x1 (first-arg xa)
			    t1 (second-arg xa)
			    res 1)
		 elseif (is-small-term (second-arg xa))
		 then (setq x1 (second-arg xa) 
			    t1 (first-arg xa)
			    res 2)
		 else (setq res 0))

	    elseif (and (eq (op-of xa) *-*) 
			(nonvarp (setq res (first-arg xa)))
			(eq (op-of res) $*$))
	    then
	    (if* (is-small-term (first-arg res))
		 then (setq x1 (first-arg res)
			    t1 (list *-* (second-arg res))
			    res 1)
		 elseif (is-small-term (second-arg res))
		 then (setq x1 (second-arg res) 
			    t1 (list *-* (first-arg res))
			    res 2)
		 else (setq res 0))
	    else
	    (setq res 0))
     (setq res 0)))

(defun reduce-+-term-wt-1-arg (term &optional (rules $poly-rules)
				    &aux done res firsts seconds rests x1 t1)
  (when (or (not $check-homogenous) (> (product-degree term) 3))
	(sloop for xa in (args-of term) do
	       (decompose-x1-t1)
	       (case res
		(0 (push xa rests))
		(1 (add-associate-list-equal x1 t1 seconds))
		(2 (add-associate-list-equal x1 t1 firsts))
		))
	
	;; try to reduce "seconds"
	(sloop for args in seconds 
	       if (and (cddr args) 
		       (setq res (reduce-+-term (make-term *+* (cdr args))
						rules)))
	       do (setq done t) (setf (cdr args) (ncons res)))

	;; try to reduce "firsts"
	(sloop for args in firsts
	       if (and (cddr args) 
		       (setq res (reduce-+-term (make-term *+* (cdr args))
						rules)))
	       do (setq done t) (setf (cdr args) (ncons res)))

	(when done
	      ;; restore the term from three pieces: seconds, firsts & rests.
	      (flat-term
	      (make-term
	       *+*
	       (nconc
		(sloop for xa in seconds
		       nconc (sloop for xb in (cdr xa)
				    collect (list $*$ (car xa) xb)))
		(sloop for xa in firsts 
		       nconc (sloop for xb in (cdr xa)
				    collect (list $*$ xb (car xa))))
		rests))))
	))

(defun reduce-+-term (term &optional (rules $poly-rules) condi)
  (sloop for rule in rules
;	 with term-degree = (or (not $check-homogenous) (product-degree term))
	with rest-args
	with left-*-args
	with right-*-args
	with res
	if
	;; (and (not (is-multi-1p-rule rule))
	;;      (or (not $check-homogenous) 
 	;;          (equal (product-degree (lhs rule)) term-degree)))
	(setq res (poly-match-+ (lhs rule) term condi))
	  do
	  (remember-used-rule-num (ruleno rule))
	    ;; Structure of the value returned by poly-match-+ is
	    ;;    ((rest-of-+-args left-*-args . right-*-args) . substitution)
	    (setq right-*-args (pop res)
		  rest-args (pop right-*-args)
		  left-*-args (pop right-*-args)
		  res (if (empty-sub res) (rhs rule) (applysubst res (rhs rule))))

	    (if (or left-*-args right-*-args)
		(setq res (nconc left-*-args (ncons res) right-*-args)
		      res (make-term $*$ res)))
	    (if rest-args 
		(setq res (nconc (list *+* res) rest-args)))
	    (return (flat-term res))
	    ))

(defmacro reduce-*-term (term rules &optional rules2 condi)
  ; "term" is rooted by "*". 
  ; If "term" is reducible at the root, then return the reduced term.
  ; Otherwise, nil.
  `(or (reduce-*-term1 ,term ,rules ,condi)
       (and ,rules2 (reduce-*-term1 ,term ,rules2 ,condi))))

(defun reduce-*-term1 (term rules &optional condi)
  (sloop for rule in rules
	 with left-args
	 with right-args
	 with res
	 do
	 (when (setq res (poly-match-* (lhs rule) term (ncons nil) condi nil))
	       (remember-used-rule-num (ruleno rule))
	
	   ;; Structure of the value returned by match-set is
	   ;;    ((left-args . right-args) . substitution)
	   (setq right-args (pop res)
		 left-args (pop right-args)
		 res (applysubst res (rhs rule)))
	   
	   (if (and (null left-args) (null right-args))
	       (return (flat-term res))
	       (return (simplify-* (nconc left-args (ncons res)
					  right-args)))))))

(defun poly-match-+ (t1 t2 &optional condi &aux res)
  ; Return ((rest-of-args left-*-args . right-*-args) . substitution) 
  ; if the matching exists.
  ; Return NIL otherwise.
  (if (setq res (ac-match (ncons (list t1 t2 nil)) (ncons nil) condi t))
      (let ((rest-*-args (pop res))
	    (rest-+-args (assoc '$extra res)))
	(if* rest-+-args then
	    (setq res (remove0 rest-+-args res)
		  rest-+-args (ncons (cdr rest-+-args))))
	(cons (cons rest-+-args rest-*-args) res))))

(defun poly-match-* (first second &optional (sigma (ncons nil)) condi triples)
  ; Return ((left-*-args . right-*-args) . substitution)
  ; Return (rest-of-xor-args rest-of-and-args . substitution) if the matching exists.
  ; Return NIL otherwise.
  (let ((args1 (args-of first))
	(args2 (args-of second))
	(not-first (pop sigma)))
    (if not-first 
	(poly-match-test-rest-*-args args1 args2 sigma condi triples not-first)
	(poly-match-find-rest-*-args args1 args2 sigma condi triples))))

(defun poly-match-one-to-* (first second sigma condi triples)
  (let ((args1 (ncons first))
	(args2 (args-of second))
	(not-first (pop sigma)))
    (if not-first 
	(poly-match-test-rest-*-args args1 args2 sigma condi triples not-first)
	(poly-match-find-rest-*-args args1 args2 sigma condi triples))))
  
(defun poly-match-test-rest-*-args (args1 args2 sigma condi triples rest-args)
  (let ((left-args (car rest-args))
	(right-args (cdr rest-args))
	(n1 (length args1)))
    (if (and (sloop for xa in left-args always (equal xa (pop args2)))
	     (equal (length args2) (add n1 (length right-args)))
	     (equal right-args (rest-elements args2 n1))
	     (sloop for xa in args1 
		   as xb in args2 
		   always (setq sigma (match xa xb sigma condi))))
	(ac-match triples (cons rest-args sigma) condi t))))

(defun poly-match-find-rest-*-args (args1 args2 sigma condi triples)
  ;; try to make different "left-args" and "right-args".
  (sloop with left-args with new
	with n1 = (length args1)
	with n2 = (length args2)
	for i from 0 to (- n2 n1)
	for args-2 on args2
	do (setq new sigma)
	   (if (and (sloop for xa in args1 
			  for xb in args-2 
			  always (setq new (match xa xb new condi)))
		    (setq new
			  (ac-match triples 
				    (cons (cons left-args
						(if (neq i n2) 
						    (rest-elements args-2 n1)))
					  new)
				    (append1 condi 
					     (make-term $*$ args-2))
				    t)))
	       (return new)
	       (push-end (car args-2) left-args))
	finally (return nil)))

;;; Another group of functions for normalizing rhs of rules.

(defun is-multi-1p-term (term)
  (and (is-rooted-+ term)
       (nonvarp (first-arg term))
       (sloop with first = (car (args-of term))
	     for xa in (cddr term) always (equal xa first))))

(defmacro is-multi-1p-rule (rule) `(is-multi-1p-term (lhs ,rule)))

(defun poly-add-multi-1p-rules (rule)
  (add-associate-list (length (args-of (lhs rule))) rule $poly-multi-1p-rules))

;;;;;;;;  Another group of functions: normalization of polys.

(defmacro poly-normal-eqn (eqn) `(move-monos-minus ,eqn t))

(defun norm-poly-term (old)
  (setq $reduce-times $reduce-max)
  (if (and $instant (is-poly old))
      (norm-poly-+ old)
      (norm-simp-poly-term old)))

(defun norm-simp-poly-term (old &aux new)
  ;; Ensure that the returned term is flattened.
  (setq $reduce-times $reduce-max)
  (if* (variablep old) then old 
      else
      (setq new (norm-outermost old))
      (if* (equal new old) then old
	   elseif (equal (setq old (poly-simplify new)) new) then new
	   else (norm-simp-poly-term old))))

(defmacro norm-rooted-+ (term)
  `(sloop for new = (reduce-+-term ,term)
	  if new do 
	  (setq ,term new)
	  (if (not (is-rooted-+ ,term)) (return ,term))
	  else return ,term))

(defun norm-poly-+ (term &optional (strong t))
  ; term is +-rooted and $polynomial is on.
  (setq term (norm-mult-monos 
	       (mult-form-minus (+-canonicalize (flat-term term))))
	term (demult-form-minus term)
	term (if* (null term) then *0term* 
		 elseif (cdr term) 
		 then (simplify-+ term) 
		 else (car term)))

  (if (and strong (is-rooted-+ term)) (norm-rooted-+ term) term))
						
(defun norm-sign-changed-monos (num monos &aux reduced mono new term (size 0))
  (setq monos (change-mono-sign num monos))
  (sloop for xa in monos do (incf size (* (abs (cdr xa)) 5)))

  (sloop while monos do
    (setq mono (pop monos)
	  term (norm-term (car mono)))
      
    (if* (and (> (times 2 (cdr mono)) num)
	      (setq new
		    (or (if (> (abs (cdr mono)) 1)
			    (reduce-mono term (cdr mono)))
			(if (equal term (car mono)) 
			    nil
			  (sharing-coef term (cdr mono))
			  ))))
	 then
	 (sloop for xa in reduced 
		if (sloop for xb in new thereis (equal (car xa) (car xb)))
		do 
		(setq new (mult-insert xa new))
		(setq reduced (remove0 xa reduced)))

	 (sloop for xa in new do (incf size (* 5 (abs (cdr xa)))))
	 (when (> size $discard-poly-max-size) 
	       (mark "Too many monomials! I discarded one equation.")
	       (return nil))

	 (setq monos (mult-sort-merge monos new))
	 else
	 (setq reduced (cons mono reduced)))
    finally (return (nreverse reduced))))

(defun norm-mult-monos (monos &aux reduced mono new term (size 0))
  ; normalize each monomials.
  (sloop for xa in monos do (incf size (abs (cdr xa))))

  (sloop while monos do
	 
	 (setq mono (pop monos)
	       term (flat-term (norm-term (car mono))))

	 (decf size (abs (cdr mono)))

	 (if (and (not (is-rooted-+ term)) (equal term (car mono)))
	     (setq new (reduce-mono term (cdr mono))
		   term nil)
	   (setq new (sharing-coef term (cdr mono))))

    (if* (or term new)
	 then
	 ;(mark new "reduce!")

	 (sloop for xa in reduced do
		(sloop for xb in new do
		       (when (equal (car xa) (car xb))
			     (setf (cdr xb) (+ (cdr xb) (cdr xa)))
			     (if (eq (cdr xb) 0) 
				 (setq new (remove0 xb new)))
			     (setq reduced (remove0 xa reduced))
			     (return))
		       ))

	 (sloop for xa in new do (incf size (abs (cdr xa))))
	 (when (> size $discard-poly-max-size) 
	       (trace-message 4 "Too many monomials! I discarded one equation.")
	       (return nil))

	 (setq monos (mult-sort-merge new monos))
	 else
	 ;(mark "reduced")
	 ;(setq reduced (mult-sort-merge (ncons mono) reduced))
	 (push mono reduced)
	 )
    finally (return reduced)))

(defun reduce-mono (term coef)
  ;; coef is the coeffcient of the term in a monomial.
  ;; return a list of monomials.
  (cond ((reduce-mono-by-nilpotent term coef))
	((variablep term) nil)
	((sloop for xa in $p-commut-rules 
		if (eq *+* (cadr xa))
		return (reduce-by-p-commut2 xa coef term)))
	((sloop for xa in $poly-multi-1p-rules 
		if (>= (abs coef) (car xa))
		do (if (setq xa (reduce-by-multi-1p-rules
				  coef term (car xa) (cdr xa)))
		       (return xa))))
	((sloop for rule in $poly-rules do
		(when (setq rule (reduce-by-one-rule term rule))
		  (if (is-rooted-minus rule)
		      (setq rule (cadr rule) 
			    coef (- coef)))
		  (if (is-rooted-+ rule)
		      (return (times-cdr coef 
					 (mult-form-minus (args-of rule))))
		      (return (ncons (cons rule coef)))))))))

(defun reduce-by-one-multi-1p-rule (term rule)
  ;; term is +-rooted.
  (setq term (if *-* (mult-form-minus (args-of term)) 
	       (mult-form (args-of term))))
  (sloop with new 
	 with length = (length (args-of (lhs rule)))
	 for pair in term 
	 if (and (>= (abs (cdr pair)) length)
		 (setq new (reduce-by-multi-1p-rules
			    (cdr pair) (car pair) length (ncons rule)))
		 )
	 return (make-term *+* (demult-form-minus 
				(append new (removen pair term 1))))))

(defmacro n-first-elements (i args)
  `(sloop for j from 1 to ,i 
	  for xa in ,args collect xa))

(defun but-first-n-elements (i n args)
  (sloop for j from 1 to i do (setq args (cdr args)))
  (n-first-elements n args))

(defun asso-reduce-by-one-at-root (term rule &aux (op (op-of (lhs rule))))
  ;; the lhs of rule is associaitive.
  ;; prepare the term so that they have the same arguments.
  (if (and (nonvarp term) (eq (op-of term) op))
      (let ((n (length (args-of (lhs rule))))
	    (m (length (args-of term)))
	    new)
	(if (< m n) nil
	  (if (eq m n) 
	      (ac-reduce-by-one-at-root term rule)
	    (sloop
	     with args = (args-of term)
	     for i from 0 to (- m n)
	     if (setq new (ac-reduce-by-one-at-root 
			   (make-term op (but-first-n-elements i n args))
			   rule))
	     return (make-term op (append (n-first-elements i args)
					  (ncons new) 
					  (but-first-n-elements (+ i n) m args)))
	     ))))))
    
(defun reduce-by-multi-1p-rules (coef term num rules)
  ;
  (sloop for rule in rules 
	 for lhs = (lhs rule)
	 as first = (first-arg lhs)
	 as res = (op-of lhs)
	 if (and (eq res *+*)
		 (setq res (if (member (op-of first) $associative)
			       (asso-reduce-by-one-at-root 
				term (change-lhs rule first))
			     (ac-reduce-by-one-at-root 
			      term (change-lhs rule first)))))
	 return 
	 (progn
	   (setq first (quotient coef num)
		 res (if (is-rooted-+ res) 
			 (times-cdr first (mult-form-minus
					   (args-of res)))
		       (ncons (cons res first))))
	   (change-lhs rule lhs)

	   (setq num (times first num))

	   (if (eq num coef)
	       res
	     (cons (cons term (- coef num))
		   ;; (if (> coef 0) (- coef num) (+ coef num)))
		   res)))
	 else do
	 (change-lhs rule lhs)
	 ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; functions to handle nilpotent rules n x == 0
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun reduce-mono-by-nilpotent (term coef)
  (sloop for xa in $nilpotent-rules 
	 if (eq *+* (caddr xa)) do
	 (cond ((>= (abs coef) (cadr xa))
		(return (if (equal (setq xa (remainder coef (cadr xa))) 0)
			    (ncons (cons nil 0))
			  (ncons (cons term xa)))))
;	       ((and *-* (> (* 2 (abs coef)) (cadr xa)))
;		(return (ncons (cons term (if (> coef 0)
;					      (- coef (cadr xa))
;					    (+ (cadr xa) coef))))))
	       )
	 ))

(defun reduce-by-nilpotent (char term)
  (sloop with succ with l1
	 with num = (cadr char)
	 with rhs = (cadddr char)
	 with margs = (mult-form (args-of term))
	 for xa in margs do
	 (when (>= (cdr xa) num)
	   (setq margs (deleten xa margs 1)
		 l1 (quotient (cdr xa) num))
	   (sloop for i from 1 to l1 do (push rhs succ))
	   (sloop for i from 1 to (- (cdr xa) (times l1 num))
		  do (push (car xa) succ)))
	 finally (return 
		   (when succ
			 (remember-used-rule-num (car char))
		     (setq succ (nconc succ (demult-form margs)))
		     (if (cdr succ) (make-term (caddr char) succ) (car succ))))))












