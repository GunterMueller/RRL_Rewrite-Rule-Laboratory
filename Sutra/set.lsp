;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "RRL")



; This file contains some functions to implement basic
; data-structures like multisets and some functions on lists.

#+franz
(defun intersection (s1 s2)
  ;  Returns the intersection of the sets S1 and S2.
  (loop for x in s2 if (member x s1) collect x))

(defun common-elements (l1 l2)
  (loop for xa in l2 
	if (member xa l1) 
	  collect xa into res
	and do (setq l1 (remove xa l1 1))
	finally (return res)))

(defun have-common (l1 l2) 
   (loop for x1 in l1 if (member x1 l2) return x1 finally (return nil)))

#+franz
(defun union (s1 s2)
  ;  Returns the union of the sets S1 and S2.
  (nconc s1 (loop for elem in s2 if (not (member elem s1)) collect elem)))

(defun set-diff (s1 s2)
  ; Returns the difference of S1 and S2, that is, S1 - S2.
  (loop for xa in s2 do (setq s1 (remove xa s1 1))
	finally (return s1)))
;  (loop for xa in s1 if (not (member xa s2)) collect xa))

(defun is-subset (l1 l2)
  ;  Returns T if L1 is a subset of L2.
  (loop for xa in l1 always (member xa l2)))

(defun list-diff (l1 l2)
  ; Returns the difference of l1 and l2.
  (loop for xa in l1 
	if (if (member xa l2) 
	       then (setq l2 (delete xa l2 1)) nil
	       else t)
	  collect xa))

(defun is-sublist (l1 l2)
  ;  Returns T if L1 is a sublist of L2.
  (loop for xa in l1 always (if (member xa l2) then (setq l2 (remove xa l2 1)) t)))

(defun mult-insert (m1 ms)
  ; insert a multi iterm into a multi iterm set.
  (loop for m2 in ms 
	if (equal (car m1) (car m2))
	 return (progn (rplacd m2 (+ (cdr m1) (cdr m2))) ms)
	 finally (return (cons m1 ms))))

(defun mult-sort-insert (m1 ms)
  ; insert a multi iterm into a multi iterm set.
  (loop for ms2 on ms as m2 = (car ms2)
	if (equal (car m1) (car m2))
	  return (progn (rplacd m2 (+ (cdr m1) (cdr m2))) ms)
	else if (total-order (car m2) (car m1))
	       return (append small (ncons m1) ms2)
	else collect m2 into small
	finally (return (append1 ms m1))))

(defun mult-merge (l1 l2) 
  (loop for xa in l1
	if (loop for xb in l2
		 if (equal (car xb) (car xa))
		   return (rplacd xb (+ (cdr xb) (cdr xa)))
		 finally (return nil))
	  do nil
	else collect xa into mlis
	finally (return (append mlis l2))))

(defun mult-sort-merge (l1 l2)
  ; assume l2 is well-order mult-sets.
  (loop for xa in l1
	do (setq l2 (mult-sort-insert 
		      (cons (flat-term (car xa)) (cdr xa)) l2))
	finally (return l2)))

(defun mult-union (s1 s2)
  (loop for xa in s1 do (setq s2 (mult-insert xa s2))
	finally (return s2)))

(defun mult-length (ms)
  ; return the number of length of ms.
  (apply '+ (mapcar 'cdr ms)))

(defun mult-diff (m1 m2) 
  ; Returns (M1-M2 . M2-M1) where M1 and M2 must be in mult-form.
  ; However, M1-M2 and M2-M1 are in set form.
  (let (l1 l2 l3)       
    (loop for xa in m1 do
          (setq l1 (assoc (car xa) m2))
          (if l1 then (if (greaterp (cdr xa) (cdr l1)) 
                          then (push (car xa) l2))
              else (push (car xa) l2)))
    (loop for xa in m2 do
          (setq l1 (assoc (car xa) m1))
          (if (and l1 (greaterp (cdr xa) (cdr l1)))
              then (push (car xa) l3)
              elseif (not l1) then (push (car xa) l3)))
    (cons l2 l3)))

(defun mult-diff2 (m1 m2) 
  ; Returns (M1-M2) where M1 and M2 must be in mult-form.
  ; M1-M2 is also in multi-form.
  (loop with l1 = nil 
	for xa in m1 
	   if (if (setq l1 (assoc (car xa) m2))  
	         then (if (greaterp (cdr xa) (cdr l1)) then
                         (setq xa (cons (car xa) (- (cdr xa) (cdr l1)))))
                 else xa)
	    collect xa))

(defun mult-form (lis) 
  ; Returns the multiset-form of list LIS.
  ; eg. (* * a b a *) ==> ((* . 3) (a . 2) (b . 1))
  (loop for xa in lis
	if (loop for l in mlis
		 if (equal (car l) xa)
		   return (rplacd l (1+ (cdr l)))
		 finally (return nil))
	  do nil
	else collect (cons xa 1) into mlis
	finally (return mlis)))

;(defun mult-form (lis) 
;  (multi-to-one (car lis) (cdr lis) nil))

;(defun multi-to-one (elem rest n_rep)
;  ; Local function.  Called by MULT-FORM.
;  (let ((i 1)) 
;    (if (null rest)
;        then (if (not (assoc elem n_rep))
;                 (setq n_rep (cons (cons elem i) n_rep)))
;             n_rep
;        elseif (not (assoc elem n_rep))
;        then (loop for xa in rest do
;                   (if (equal elem xa) then (setq i (1+ i))))
;             (setq n_rep (cons (cons elem i) n_rep)))
;    (multi-to-one (car rest) (cdr rest) n_rep)))

(defun demult-form (mul &aux res) 
  ; Returns the list-form of multi-set MUL.
  ; eg. ((* . 3) (a . 2) (b . 1)) ==> (b a a * * *).
  (loop for m in mul do 
     (loop for xa from 1 to (cdr m) do (push (car m) res)))
    res)






