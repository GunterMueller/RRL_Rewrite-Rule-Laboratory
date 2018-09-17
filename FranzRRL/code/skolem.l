;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

; ********WARNING*********
; *****Parental guidance suggested for children under the age of 17*********
; ********WARNING*********

(defun skolemize (ass &optional sign)
  ; Remove all quantifiers of ASS. Take special care of "equ" and "xor".
  (caseq (op-of ass)
    ((all exist) (skolemize (skolemize-away-quants ass ass sign) sign))
    (equ (let ((a1 (loop for xa in (args-of ass)
			     if (have-common (all-ops xa) '(exist all))
			       return xa)) a2)
	   (if a1 then 
	       (setq a2 (remq a1 (args-of ass))
		     a2 (if (cdr a2) then (make-term 'xor a2) else (car a2)))
	       (remove-quan-args `(and (-> ,a1 ,a2) (-> ,a2 ,a1)) sign)
	       else
	       (remove-quan-args `(xor (true) . ,(args-of ass)) sign))))
    (xor (let ((a1 (loop for xa in (args-of ass)
			     if (have-common (all-ops xa) '(exist all))
			       return xa)) a2)
	   (if a1 then 
	       (setq a2 (remq a1 (args-of ass))
		     a2 (if (cdr a2) then (make-term 'xor a2) else (car a2)))
	       (if (equal a2 '(true)) then
		   `(xor (true) ,(skolemize a1 (not sign)))
		   else
		   (remove-quan-args `(not (and (-> ,a1 ,a2) (-> ,a2 ,a1))) (not sign)))
	       else
	       (remove-quan-args ass sign))))
    (->  `(-> ,(skolemize (first-arg ass) (not sign))
              ,(skolemize (second-arg ass) sign)))
    (not `(not ,(skolemize (first-arg ass) (not sign))))
    ((and or) (remove-quan-args ass sign))
    (t ass)))

(defun remove-quan-args (ass sign)
  ; remove the quantifiers from the arguments of ass.
  (make-term (op-of ass) 
	     (loop for xa in (args-of ass) 
		   collect (skolemize xa sign))))

(defun skolemize-away-quants (ass whole-ass sign)
   ; Remove the leading quantifiers from ass by introducing a skolem 
   ; function or a skolem variable.
   (let ((quant (op-of ass)) (var (first-arg ass)) (form (second-arg ass))
	 newvar)
    (if (eq sign (eq quant 'exist))  
	then (setq newvar (make-new-variable var))
	     (if (assoc var $var-type-list) then
		 (push (cons newvar (cdr (assoc var $var-type-list))) $var-type-list))
	else (setq newvar (get-sko-func var form whole-ass)))
    (setq form (special-subst newvar var form))
    (if (quantifierp (op-of form)) 
	then (skolemize-away-quants form whole-ass sign)
	else form)))

(defun special-subst (new old form)
  (cond ((variablep form) 
	 (if (eq form old) then new else form))
        ((memq (op-of form) `(exist all))
	 (if (eq (first-arg form) old) 
	    then form
	    else (list (op-of form) (first-arg form)  
		       (special-subst new old (second-arg form)))))
	(t (make-term (op-of form)
		      (loop for xa in (args-of form)
			  collect (special-subst new old xa))))))

(defun subst-quant-form (func ass source &aux l1)
    (setq l1 `(-> ,ass ,func))
    (process-ass2 `(-> ,(skolemize-away-quants ass l1 t) ,func) source)
    (setq l1 `(-> ,func ,ass))
    (process-ass2 `(-> ,func ,(skolemize-away-quants ass l1 nil)) source))

(defun hasquant (ass)
  ; Determine whether a formula has any quantifiers.
    (cond ((variablep ass) nil)
	  ((quantifierp (op-of ass)) t)
          (t (loop for xa in (args-of ass) thereis (hasquant xa)))))

(defun get-sko-func (var ass whole-ass) 
    ; Given that we have to introduce a skolem function to replace var in
    ; ass, figure out what that function should be.
    (let ((op (gennewsym 's)) (args (remonce var (free-vars ass))))
	(set-arity op (length args))

	(if (assoc var $var-type-list) then
	    (set-arity2 op 
			(cons (cdr (assoc var $var-type-list))
			      (loop for xa in args 
				    collect (if (setq xa (assoc xa $var-type-list))
						then (cdr xa)
						else 'univ)))))
	(set-skolem op)
	(setq args (make-term op args))
	(if (> $trace_flag 1) then
	    (terpri) (princ "  Introducing") (display-one-arity2 op)
	    (princ "  ") (write-term args)
	    (princ " is a skolem function for ") (princ var) 
	    (terpri) (princ "     in the assertion: ") 
	    (write-term whole-ass) (terpri))
	args))
