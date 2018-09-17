;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

(defun quasi-check (l1 l2 &optional trace time &aux testset)
  ; Test the quasi-reducibility of non-ground terms in l2.
  ; If a term in l2 is not quasi-reducble then put it into testset.
  (loop while l1 do
    (push (rename-vars (pop l1)) testset)
    (setq $quasis nil)
    (if (and trace (eq $trace_flag 3)) then (terpri)
      (princ "Add to test set: ") (write-term (car testset)) (terpri))
    (loop for term in l2 do
	(cond ((sub-quasi-reducible term testset) nil)
		; "term" is quasi-reducible w.r.t. the current testset.
		; it should be tested for more terms.
	      (t (setq l2 (remonce term l2)) (push term l1))))
    (if (null l2) then (return)))
  (if (and trace (eq $trace_flag 3)) then (trace-add-testset l1 time))
  (nconc testset (mapcar 'rename-vars l1)))

(defun sub-quasi-reducible (t1 testset)
  ; Returns "t" iff one of subterms of "t1" is quasi-reducible.
  (loop for xa in (args-of t1) thereis (nail-quasi-reducible xa testset)))

(defun quasi-equivalent (t1 t2 &optional testset &aux vars sigma t11)
  ; Returns "t" iff "t1" is quasi-reducible w.r.t. testset.
  (if (null testset) then (setq testset $testset))
  (if (setq vars (type-var-list t1)) then
      (loop for ts in (n-tuples (length (car vars)) testset) 
	    always (or (not (loop for ty in (car vars)
				  for term in ts always
						   (type-cohere ty (type-of term))))
		       (guide-reducible-time 
			 t1
			 (setq t11 (sublis (setq sigma (mapcar 'cons (cadr vars) ts)) t1)))
		       (equal t11 (norm-term (sublis sigma t2)))))))

(defun quasi-reducible (t1 &optional testset &aux vars)
  ; Returns "t" iff "t1" is quasi-reducible w.r.t. testset.
  (if (nonvarp t1) then
     (if (null testset) then (setq testset $testset))
     (if (setq vars (type-var-list t1)) then
	(setq t1 (if $commutative then (c-permutation t1) else t1))
	(loop for ts in (n-tuples (length (car vars)) testset) 
  		always (or (not (loop for ty in (car vars)
				      for term in ts always
					   (type-cohere ty (type-of term))))
			   (guide-reducible-time t1
			      (sublis (mapcar 'cons (cadr vars) ts) t1)))))))

(defun nail-quasi-reducible (t1 testset &aux vars first)
  ; Returns "t" iff "t1" is quasi-reducible w.r.t. testset.
  ; The first element of testset should be used to contruct each 
  ; substitution which is from vars(t1) to testset.
  (if (is-an-instance t1 $quasis) then t else
    (setq first (car testset))
    (if (and (setq vars (type-var-list t1))
	     (loop for ts in (make-tuples (length (car vars)) testset) 
  		always (or (not (loop for ty in (car vars)
				      for term in ts always
					   (type-cohere ty (type-of term))))
			   (guide-reducible-time t1
				 (sublis (mapcar 'cons (cadr vars) ts) t1)))))
	then (push t1 $quasis) t)))

(defun quasi-remover (ts)
  ; Returns the all non-quasi-reducible terms in "ts".
  (if $testset 
      then (prog (nts)
             (loop for xa in ts do 
               (if (sub-quasi-reducible xa $testset)
                   then (if (eq $trace_flag 3) then
		  	 (terpri) 
			 (princ "Following term is ground-reducible:")
			 (terpri) (princ "    ") (write-term xa) (terpri))
                   else (setq nts (append1 nts xa))))
             (return nts))
      else ts))

