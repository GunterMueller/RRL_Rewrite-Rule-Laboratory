(in-package "USER")

; -- This file contains both non-ac and ac unification.
; -- wrote a cleaner version of unifer which does not
; -- use any global variables for non-ac

(defun unifier (t1 t2 &aux uni)
  (if (setq uni (nonac-unify t1 t2)) 
     (if $block-cps (is-blocked uni) uni)))


;; We can call nonac-unify with some variables already bound
;; in binds.

(defun nonac-unify (t1 t2 &optional sigma &aux cvalt1 cvalt2)
  ; Returns a sigma, if one exists, such that sigma(T1) = sigma(T2);
  ; otherwise, returns NIL.  This is a very simple algorithm and
  ; does very well for most examples.
  ; suppose t1 and t2 don't contain variables bouneded in sigma.
  (if (empty-sub sigma) (setq sigma nil))
  (cond ((equal t1 t2) (or sigma *empty-sub*))
        ((variablep t1)
	 (if (variablep (setq cvalt1 (cur-val t1 sigma)))
	     (if (occurs-in cvalt1 (setq t2 (applysigma sigma t2))) 
		 nil 
	       (nconc (replace-term t2 cvalt1 sigma) `((,cvalt1 . ,t2))))
	   (nonac-unify cvalt1 t2 sigma)))
        ((variablep t2)
	 (if (variablep (setq cvalt2 (cur-val t2 sigma)))
	     (if (occurs-in cvalt2 (setq t1 (applysigma sigma t1)))
		 nil 
	       (nconc (replace-term t1 cvalt2 sigma) `((,cvalt2 . ,t1))))
	   (nonac-unify cvalt2 t1 sigma)))
        ((same-root t1 t2)
	 (sloop with ans = sigma 
		for xa in (args-of t1)
		for ya in (args-of t2)
		if (setq ans (if* (variablep xa)
				  then (if (variablep ya) 
					   (nonac-unify (cur-val xa ans)
							(cur-val ya ans) ans)
					 (nonac-unify (cur-val xa ans) ya ans))
				  elseif (variablep ya) 
				  then (nonac-unify xa (cur-val ya ans) ans)
				  else (nonac-unify xa ya ans))) 
		do (if (eq ans *empty-sub*) (setq ans nil))
		else return nil
		finally (return (or ans *empty-sub*))))
	))

#|
The following algorithm is buggy: For instance, try
   h(x, f(x, f(x, x)), x) and h(f(y, f(y, y)), y, y) 
   h(x, y, z, u, x) and h(f(y), f(z), f(u), f(x), z)

(defun nonac-unify (t1 t2 &aux binds)
  (setq binds (unify-decompose-terms t1 t2 nil))
  (if (eq binds 'fail) 
      nil
    (if binds (normal-form-sub binds nil) *empty-sub*)))

;; No loops/setq/globals etc. just mapcar and tail recursion.
;; a unification routine that uses mapcar & throw
;; checking conflicts at the end. 
;; Will gain if failure due to fn-symbol clash occurs often.
;; first decompose into equations with one side a variable and
;; then resolve sunstitutions.

(defmacro add-bind-to-sub (v1 t1 sub)
     `(cons (cons ,v1 ,t1) ,sub))

(defun unify-decompose-terms (t1 t2 ans)
  ;; takes two terms and returns list of equations with lhs a variable
  ;; throws away trivial eqns like (x x) for unification. 
  ;; detects symbol clash.
  (cond ((variablep t1) 
	 (if (eq t1 t2) 
	     ans
	   (if (occurs-in t1 t2) 
	       'fail
	     (let ((cval (assq t1 ans)))
	       (if cval 
		   (unify-decompose-terms (cdr cval) t2 ans)
		 (if (and (variablep t2) (setq cval (assq t2 ans)))
		     (unify-decompose-terms t1 (cdr cval) ans)
		   (add-bind-to-sub t1 t2 ans))))
	     )))
	((variablep t2) 
	 (if (occurs-in t2 t1)
	     'fail
	   (let ((cval (assq t2 ans)))
	     (if cval 
		 (unify-decompose-terms (cdr cval) t1 ans)
	       (add-bind-to-sub t2 t1 ans)))))
	((same-root t1 t2)
	 (sloop for xa in (args-of t1)
		as  ya in (args-of t2)  
		while (neq ans 'fail)
		do (setq ans (unify-decompose-terms xa ya ans))
		finally (return ans)))
	(t 'fail)))
|#

(defun normal-form-sub (sub ans)
  ;; to give answer in normal form for unification. and do occurs check.
  ;; first occur-check and then re-sub
  (if sub
     ;; occur-check here
      (let ((v1 (caar sub))
	    (t1 (applysubst ans (cdar sub))))
	(if (occurs-in v1 t1) 
	    nil
	  (normal-form-sub (cdr sub)
			   (cons (cons v1 t1)
				 (replace-term t1 v1 ans)))))
    ans))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; AC Unification functions.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun unifiers (t1 t2 &optional (flag 3) notop)
  (if (or $ac $commutative) 
      (sloop for xa on (setq flag (ac-unify t1 t2 flag notop)) do
	     (setf (car xa) (cdar xa))   ;; remove the size of each unifier.
	     finally (return flag))
    (if (setq flag (unifier t1 t2)) (ncons flag))))

(defun ac-unify (x y &optional flag no-top &aux u)
  ; if source is not nil, then process each unifiers once it is made out.
  (setq u (ac-unification x y flag (not no-top)))
  (when u
      (setq u (sloop for uni in u collect (size-flat-sigma uni)))
      (when u 
       (trace-message 4 ""
	   (format t "    There are ~d unifiers between ~%" (length u))
	   (princ "        ") (write-term x) (princ " and") (terpri)
	   (princ "        ") (write-term y) (terpri)))

      (sort (if $block-cps
		(blocked-check u)
	      u)
	    'car-lessp)))

(defun ac-unification (x y &optional flag top)
  (cond
    ((or (null x) (null y)) nil)
    ((variablep x)
     (cond
       ((occurs-in x y) (if (equal x y) (ncons *empty-sub*)))
       ((or (and (eq x *xex1*) (eq y *xex2*))
	    (and (eq x *xex2*) (eq y *xex1*))) nil)
       (t (ncons (ncons (cons x y))))))
    ((variablep y)
     (if* (not (occurs-in y x)) then
	 (ncons (ncons (cons y x)))))
    ((not (eq (op-of x) (op-of y)))                  nil)
    ;((ac-root x) (acuni (make-flat x) (make-flat y) flag top))
    ((ac-root x) (acuni x y flag top))
    ((equal (length (cdr x)) (length (cdr y)))
     (sloop for xa in (args-of x) 
	     for ya in (args-of y)
	     if (or (variablep xa) (variablep ya))
	       collect xa into m1 and collect ya into m2
	     else if (neq (op-of xa) (op-of ya))
		    return nil
	     else if (ac-root xa)
		    collect xa into l1 and collect ya into l2
	     else collect xa into k1 and collect ya into k2
	     finally 
	       (return (unicompound (append m1 k1 l1)
					(append m2 k2 l2)))))))

(defmacro actual-unify-action ()
  `(cond ((and (null vecx) (null vecy)) (ncons *empty-sub*))
	 ((or (null vecx) (null vecy)) nil)                     ; failure
	 ((and (null (cdr new-argsx)) (null (cdr new-argsy)))
	  (ac-unification (car new-argsx) (car new-argsy)))
	 ((null (cdr new-argsx))
	  (if* (nonvarp (car new-argsx))
	      nil
	      (if* (sloop with xarg = (car new-argsx)
			for arg in new-argsy
			thereis (occurs-in xarg arg))
		  nil
		  (ncons (ncons (cons (car new-argsx) (cons op new-argsy)))))))
	 ((null (cdr new-argsy))
	  (if* (nonvarp (car new-argsy))
	      nil
	      (if* (sloop with yarg = (car new-argsy)
			for arg in new-argsx
			thereis (occurs-in yarg arg))
		  nil
		  (ncons (ncons (cons (car new-argsy)
				      (cons op new-argsx)))))))
	 ((and (sloop for x in vecx always (eq x 1))
	       (sloop for x in vecy always (eq x 1)))
	  (all-ones vargsx nargsx vargsy nargsy op top))
	 (t (full-dio vargsx nargsx vargsy nargsy vecx vecy op top))))

(defun acuni (x y &optional flag top)
  (let ((argsx (args-of x)) (argsy (args-of y))
        (op (op-of x)) l1 l2
	new-argsx new-argsy vargsx nargsx vecx vargsy nargsy vecy)

       (setq l1 (elimcom argsx argsy) 
	     new-argsx (car l1) 
	     new-argsy (cdr l1))
       (case flag
	 (1 (push *xex1* new-argsx))
	 (2 (push *xex1* new-argsx)
	    (push *xex2* new-argsy)))

       (setq l1 (multi-com new-argsx) 
	     l2 (split-alist (cdr l1))
	     l1 (split-alist (car l1))
	     vargsx (car l1) 
	     nargsx (car l2)
	     vecx (nconc (cadr l1) (cadr l2)))

       (setq l1 (multi-com new-argsy)
	     l2 (split-alist (cdr l1))
	     l1 (split-alist (car l1))
	     vargsy (car l1) 
	     nargsy (car l2)
	     vecy (nconc (cadr l2) (cadr l1)))

       (actual-unify-action)))
       

; finds mgus of sub(terms) though we already know mgu of terms.
(defun res1 (sub terms args) 
     (sloop with uni = (ncons sub)
           with t1 = (aref args (car terms))
           for n in (cdr terms) do
 	    (setq uni (sloop for sub1 in uni 
			   append (compose2 sub1
                		    (ac-unification
				      (applysigma sub1 t1)
				      (applysigma sub1 (aref args n))))))
	    (if* (null uni) (return nil))
            finally (return uni)))

; simple check to see if terms can unify
(defun plausible (t1 t2)
  (cond ((neq (op-of t1) (op-of t2)) nil)
	((ac-root t1) t)
	((and $polynomial (eq (op-of t1) '*)) t)
	(t (sloop for xa in (args-of t1) as ya in (args-of t2)
		 always (or (variablep xa) 
			    (variablep ya)
			    (plausible xa ya))))))

(defun all-plaus (args tmp)
  (sloop with t1 = (aref args (car tmp))
	for i in (cdr tmp) always (plausible t1 (aref args i))))


; The following functions are put here temporarily
; until a better home can be found.

(defun unicompound (largs lsigma )
  ; Unicompound returns a list of substitutions such that for each substitution the
  ; nth element in largs is ac-equal to the nth element in lsigma under that substitution.
  ; For efficiency purposes largs should contain variables followed by non-variable terms.
  ; Nil is returned if no such substitution exists.
  (sloop
    with subst-list = (list *empty-sub*)
    for arg in largs
    for bind in lsigma
    if subst-list
    do(setq subst-list (continue-mapping arg bind subst-list))
    else return nil
    finally(return subst-list)))

(defun continue-mapping (arg bind subst-list 
			     &aux return-subst-list unify-subst-list)
  ; Continue-mapping applys each substitution "sub" in subst-list to arg and to
  ; bind and trys to unify the resulting terms. If a list of substitutions is
  ; returned from a successful unification each substitution in that list is
  ; composed with "sub" and the resulting list of substitutions is appended onto 
  ; the return-list.  If no sucessful unifications obtains then nil is returned.
  (dolist (sub subst-list)
	  (setq unify-subst-list (ac-unification (applysigma sub arg)
						 (applysigma sub bind)))
	  (if unify-subst-list
	      (setq return-subst-list 
		    (nconc return-subst-list
			   (sloop for unify-sub in unify-subst-list 
				  collect (compose unify-sub sub)))))
	  )
  return-subst-list)


; From pccritical

(defun two-unifier (ls1 ls2)
  ;; Unify the first element of ls1 with an element of ls2. If such a unifer
  ;; exists, then try to unify another element of ls1 with another element
  ;; of ls2, under the context of the first unifer. If such a unifier exists,
  ;; return it. Otherwise, return nil.
  (sloop for xa in ls2
	with subst
	with ls22
	with res
	do
    (if* (setq subst (unifier (car ls1) xa nil))
	then (setq ls22 (remonce xa ls2))
	(if* (setq res (sloop for xa in (cdr ls1)
			    thereis 
			      (sloop for xb in ls22
				    thereis (unifier xa xb subst))))
	    then (return res)))))

(defun set-unification (args1 args2 &optional fast-flag bind)
   ; Find a subset of ARGS2 say ARGS22 which unify with ARGS1. 
   ; Return ((ARGS2 - ARGS22) . substition) if the unifier exists.
   ; Return NIL otherwise.
   (prog ((t1 (pop args1)) t2 newbind result args22)
        loop-here
        (sloop while t do
	    (if* (null (setq t2 (pop args2))) 
		then (return nil)
	        elseif (setq newbind (unifier t1 t2 bind))
		then (return nil)
	        else (setq args22 (nconc args22 (ncons t2)))))
        (if* (null t2) then (return nil)
	    elseif (null args1)
	    then (return (cons (nconc args22 args2) newbind))
	    elseif (setq result 
			  (set-unification args1 
		  	       (if* fast-flag then args2
					     else (append args22 args2))
			        fast-flag newbind))
	    then (if* fast-flag then
		     (rplaca result (nconc args22 (car result))))
      	         (return result)
	    else (setq args22 (nconc args22 (ncons t2)))
	 	 (go loop-here))))


;;; Functions used to be in blocking.l

(defun blocked-check (u)
  (sloop for bindings in u if (is-blocked (cdr bindings)) collect bindings))

(defun is-blocked (sigma)
  ; In the old function, (memq (car xb) vars) is equal to
  ; (not (memq (car xb) (list *xex1* *xex2*))). --HZ.
  (if* (or (empty-sub sigma)
	   (sloop for xb in sigma 
		  always (or (eq (car xb) *xex1*)
			     (eq (car xb) *xex2*)
			     (variablep (cdr xb))
			     (not (reducible (cdr xb))))))
       then sigma
       else
       (incf $block-cps)
      (trace-message 4 "    Unblocked substitution deleted: ["
	  (write-sigma sigma) (princ "]")
	  (terpri))
      nil))

(defun display-unify (x y)
  (sloop for xa in (ac-unify x y) do (write-sigma (cdr xa)) (terpri)))
