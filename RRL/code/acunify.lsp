;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

;; NONAC unify now in uni-match -- Siva   dec '89.

; -- This file contains both non-ac and ac unification.
; -- wrote a cleaner version of unifer which does not
; -- use any global variables for non-ac
; -- Ac unification code is long but works. the procedures
; -- for getting basis-soln can be improved.

(defun unifiers (t1 t2 &optional (flag 3))
  (if* (or $ac $commutative) then
      (sort (unify t1 t2 flag) 'lessp-size-bindings)
      else 
      (add-time $unif_time
		(if* (setq flag (unifier t1 t2)) then (ncons flag)))))

(defun unifier (t1 t2 &optional uni)
  (if* (setq uni (nonac-unify t1 t2 uni)) 
     (if* (eq $blocking-on 'y) 
	 (add-time $block_time (is-blocked uni))
	 uni)))

(defun unify (x y &optional flag no-top &aux u)
  ; if source is not nil, then process each unifiers once it is made out.
  (add-time $unif_time (setq u (unify-with-ac x y flag (not no-top))))
  (when u
      (setq u (sloop for uni in u		
		    collect (cons (size-uni uni) 
				  (if* (eq uni *empty-sub*)
				      uni
				    (sloop for sig in uni 
					  collect (cons (car sig)
							(make-flat (cdr sig))))))))
      (if* (and u (= $trace_flag 3)) then
	  (terpri) (princ (uconcat "    There are " (length u) " unifiers between "))
	  (terpri) (princ "        ") (write-term x) (princ " and")
	  (terpri) (princ "        ") (write-term y) (terpri))
      (if* (eq $blocking-on 'y) 
	  (add-time $block_time (block-check u))
	  u)))



(defun unify-with-ac (x y &optional flag top)
  (cond
    ((or (null x) (null y)) nil)
    ((variablep x)
     (cond
       ((occurs-in x y)
	(if* (equal x y) then (ncons *empty-sub*)))
       ((or (and (eq x 'xex1) (eq y 'xex2))
	    (and (eq x 'xex2) (eq y 'xex1))) nil)
       (t (ncons (ncons (cons x y))))))
    ((variablep y)
     (if* (not (occurs-in y x)) then
	 (ncons (ncons (cons y x)))))
    ((not (eq (op-of x) (op-of y)))                  nil)
    ((ac-root x) (acuni (make-flat x) (make-flat y) flag top))
    ((= (length (cdr x)) (length (cdr y)))
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
	  (unify-with-ac (car new-argsx) (car new-argsy)))
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
	 ((and (sloop for x in vecx always (= x 1))
	       (sloop for x in vecy always (= x 1)))
	  (all-ones vargsx nargsx vargsy nargsy op top))
	 (t (full-dio vargsx nargsx vargsy nargsy vecx vecy op top))))

(defun acuni (x y &optional flag top)
  (let ((argsx (args-of x)) (argsy (args-of y))
        (op (op-of x)) l1 l2
	new-argsx new-argsy vargsx nargsx vecx vargsy nargsy vecy)

       (setq l1 (elimcom argsx argsy) 
	     new-argsx (car l1) 
	     new-argsy (cadr l1))
       (caseq flag
	 (1 (push 'xex1 new-argsx))
	 (2 (push 'xex1 new-argsx)
	    (push 'xex2 new-argsy)))

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
                		    (unify-with-ac
				      (apply-to t1 sub1)
				      (apply-to (aref args n) sub1)))))
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

(defun unicompound (largs lbinds )
  ; Unicompound returns a list of substitutions such that for each substitution the
  ; nth element in largs is ac-equal to the nth element in lbinds under that substitution.
  ; For efficiency purposes largs should contain variables followed by non-variable terms.
  ; Nil is returned if no such substitution exists.
  (sloop
    with subst-list = (list *empty-sub*)
    for arg in largs
    for bind in lbinds
    if subst-list
    do(setq subst-list (continue-mapping arg bind subst-list))
    else return nil
    finally(return subst-list)))

(defun continue-mapping (arg bind subst-list)
  ; Continue-mapping applys each substitution "sub" in subst-list to arg and to
  ; bind and trys to unify the resulting terms. If a list of substitutions is
  ; returned from a successful unification each substitution in that list is
  ; composed with "sub" and the resulting list of substitutions is appended onto 
  ; the return-list.  If no sucessful unifications obtains then nil is returned.
  (sloop
    for sub in subst-list
    for unify-subst-list = (unify-with-ac (apply-to arg sub)
					  (apply-to bind sub) ) 
    if unify-subst-list
    append (sloop for unify-sub in unify-subst-list collect(compose unify-sub sub))
    into return-subst-list
    finally(return return-subst-list)))


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
    (if* (setq subst (add-time $unif_time (unifier (car ls1) xa nil)))
	then (setq ls22 (remonce xa ls2))
	(if* (setq res (sloop for xa in (cdr ls1)
			    thereis 
			      (sloop for xb in ls22
				    thereis 
				      (add-time $unif_time (unifier xa xb subst)))))
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
	        elseif (setq newbind (add-time $unif_time (unifier t1 t2 bind)))
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

(defun block-check (u)
  (sloop for bindings in u if (is-blocked (cdr bindings)) collect bindings))

(defun is-blocked (bindings)
  ; In the old function, (memq (car xb) vars) is equal to
  ; (not (memq (car xb) '(xex1 xex2))). --HZ.
  (if* (eq bindings *empty-sub*) 
      then bindings
      elseif (sloop for xb in bindings 
		   always (or (memq (car xb) '(xex1 xex2))
			      (variablep (cdr xb))
			      (not (reducible (cdr xb)))))
      then bindings
      else
      (setq $unblocked (1+ $unblocked))
      (if* (= $trace_flag 3) then
	(terpri) 
	(princ "    Unblocked substitution deleted: [")
	(write-sigma bindings t) (princ "]")
	(terpri))
      nil))

(defun display-unify (x y)
  (sloop for xa in (unify x y) do (write-sigma (cdr xa) t) (terpri)))
