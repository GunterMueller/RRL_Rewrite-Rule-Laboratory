;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-

#+franz (include "datamacs.l")
#-franz (in-package "RRL")

;; non-AC match and unify. written sharing most of the code
;; and to do well in failure cases. -- Siva DEC 4 1989.
;; No loops/setq/globals etc. just mapcar and tail recursion.
;; a matching/unification routine that uses mapcar & throw
;; checking conflicts at the end. 

;; will gain if failure due to fn-symbol clash occurs often.
;; first decompose into equations with one side a variable and
;; then resolve sunstitutions.

#-franz
(defvar *empty-sub* '(()))

;; (defmacro fail-uni-match() `(throw '*unimatch* nil))

(defmacro add-bind-to-sub (v1 t1 sub)
     `(cons (cons ,v1 ,t1) ,sub))

;; takes two terms and returns list of equations with 
;; lhs a variable
;; throws away trivial eqns like (x x) for unification. 
;; detects symbol clash.
;; flag can be 'match or 'unify. in unify vars in rhs are also
;; made into equations.
;;
(defun decompose-terms (t1 t2 ans flag)
  (cond ((var? t1) (let ((cval (assq t1 ans)))
		     (case flag
			   (match (if cval (if (equal t2 (cdr cval)) ans 'fail)
				    (add-bind-to-sub t1 t2 ans)))
			   (unify (if (eq t1 t2) ans
				    (if cval (decompose-terms (cdr cval) t2 ans flag)
				     (add-bind-to-sub t1 t2 ans)))))))
	((var? t2) (case flag
			 (match 'fail)
			 (unify (decompose-terms t2 t1 ans flag))))
	((and (same-op? t1 t2) (= (length t1) (length t2)))
	    (loop for xa in (args-of t1)
		  as  ya in (args-of t2)  
                  while (not (eq (setq ans (decompose-terms xa ya ans flag)) 'fail))
			finally (return ans)))
	(t 'fail)))

;; to give answer in normal form for unification. and do occurs check.
;;;;; first occur-check and then re-sub
(defun normal-form-sub (sub ans)
  (if sub
     ;; occur-check here
      (let ((v1 (caar sub))
	    (t1 (applysubst ans (cdar sub))))
	(if (occurs-in v1 t1) nil
	  (normal-form-sub (cdr sub) (cons (cons v1 t1)
					   (sublis (list (cons v1 t1)) ans)))))
    ans))

;;
;; match and unify now easily defined below.
;; We can call either match or unify with some variables already bound
;; in binds.


;; unify t1 & t2 in the context binds.
(defun nonac-unify (t1 t2 &optional binds)
  (let ((ans1 (decompose-terms t1 t2 binds 'unify)))
    (if (eq ans1 'fail) nil
      (if ans1 (normal-form-sub ans1 nil) *empty-sub*))))

;; these calls the way RRL uses.

(defun match (t1 t2 &optional sigma condi) ;; condi from RRL? why?
  (let ((ans (decompose-terms t1 t2  sigma 'match)))
    (if (eq ans 'fail) nil (or ans *empty-sub*))))

(defun pure-match (t1 t2 &optional sigma) 
  (let ((ans (decompose-terms t1 t2  sigma 'match)))
    (if (eq ans 'fail) nil (or ans *empty-sub*))))
